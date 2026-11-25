# -*- coding: utf-8 -*-
"""
Rudig Sounds Bot
ربات کانال موسیقی بلوچی: دانلود آهنگ کامل در یک مرحله، پست‌ساز، عضویت اجباری،
دو لاگ جدا، بلاک، پیام پیوست، مدیریت چندکاناله و پنل ادمین.

نیازمندی: aiogram 3.x (نسخه‌ی جدید برای رنگ دکمه‌ها)، Python 3.10+
"""
import asyncio
import html
import io
import logging
import os
import random
import re
import sqlite3
import time
from collections import defaultdict, deque
from datetime import datetime, timedelta
from logging.handlers import RotatingFileHandler
from zoneinfo import ZoneInfo

from aiogram import BaseMiddleware, Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import (TelegramBadRequest, TelegramForbiddenError,
                                TelegramRetryAfter)
from aiogram.filters import Command, CommandObject, CommandStart, Filter, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (BotCommand, BotCommandScopeChat, BotCommandScopeDefault,
                           BufferedInputFile, CallbackQuery, ChatMemberUpdated,
                           InlineKeyboardButton, InlineKeyboardMarkup, Message)

# ───────────────────────────── تنظیمات ─────────────────────────────


def load_env(path=".env"):
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                k, v = line.split("=", 1)
                os.environ.setdefault(k.strip(), v.strip().strip('"').strip("'"))


load_env()


def _chat_ref(v):
    v = (v or "").strip()
    if not v:
        return None
    return int(v) if v.lstrip("-").isdigit() else v


TOKEN = os.environ.get("BOT_TOKEN", "")
MAIN_CHANNEL = _chat_ref(os.environ.get("MAIN_CHANNEL", ""))
ENV_ADMINS = {int(x) for x in re.findall(r"-?\d+", os.environ.get("ADMINS", ""))}
ENV_JOIN_LOG = _chat_ref(os.environ.get("JOIN_LOG_CHAT", ""))
ENV_DL_LOG = _chat_ref(os.environ.get("DOWNLOAD_LOG_CHAT", ""))
CHANNEL_NAME = os.environ.get("CHANNEL_NAME", "𝐑𝐮𝐝𝐢𝐠 𝐒𝐨𝐮𝐧𝐝𝐬")
CHANNEL_LINK = os.environ.get("CHANNEL_LINK", "")
TZ = ZoneInfo(os.environ.get("TIMEZONE", "Asia/Tehran"))
DB_PATH = os.environ.get("DB_PATH", "rudig.db")
STYLES_ON = os.environ.get("BUTTON_STYLES", "1") != "0"
SPAM_LIMIT = int(os.environ.get("SPAM_LIMIT", "8"))
STORAGE_CHAT = _chat_ref(os.environ.get("STORAGE_CHAT", ""))
WELCOME = os.environ.get(
    "WELCOME_TEXT",
    "سلام 👋\nاینجا آهنگ‌های کامل کانال برات فرستاده می‌شه.\n"
    "از دکمه‌ی زیر پست‌های کانال استفاده کن.")

os.makedirs("logs", exist_ok=True)
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    handlers=[RotatingFileHandler("logs/bot.log", maxBytes=2_000_000,
                                  backupCount=3, encoding="utf-8"),
              logging.StreamHandler()])
log = logging.getLogger("rudig")

G = {"bot_id": 0, "bot_username": "", "main_id": 0, "main_title": ""}

# ───────────────────────────── دیتابیس ─────────────────────────────

db = sqlite3.connect(DB_PATH, isolation_level=None)
db.row_factory = sqlite3.Row
db.executescript("""
CREATE TABLE IF NOT EXISTS users(
  id INTEGER PRIMARY KEY, first_name TEXT, username TEXT, joined_at INTEGER,
  active INTEGER DEFAULT 1, blocked INTEGER DEFAULT 0, block_reason TEXT, blocked_at INTEGER);
CREATE TABLE IF NOT EXISTS posts(
  id INTEGER PRIMARY KEY AUTOINCREMENT, kind TEXT, media_type TEXT, media_id TEXT,
  title TEXT, artist TEXT, code TEXT, button_on INTEGER DEFAULT 1, color_idx INTEGER DEFAULT 0,
  status TEXT, created_at INTEGER, run_at INTEGER, created_by INTEGER);
CREATE TABLE IF NOT EXISTS post_msgs(post_id INTEGER, chat_id INTEGER, message_id INTEGER);
CREATE TABLE IF NOT EXISTS songs(
  id INTEGER PRIMARY KEY AUTOINCREMENT, post_id INTEGER, pos INTEGER DEFAULT 0, label TEXT,
  file_id TEXT, file_type TEXT, downloads INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS downloads(
  id INTEGER PRIMARY KEY AUTOINCREMENT, song_id INTEGER, user_id INTEGER, ts INTEGER);
CREATE TABLE IF NOT EXISTS force_channels(
  id INTEGER PRIMARY KEY AUTOINCREMENT, chat_id INTEGER, title TEXT, link TEXT,
  enabled INTEGER DEFAULT 1, checked INTEGER DEFAULT 0, is_main INTEGER DEFAULT 0, sort INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS force_events(ch_id INTEGER, user_id INTEGER, kind TEXT, ts INTEGER);
CREATE TABLE IF NOT EXISTS force_ok(user_id INTEGER, ch_id INTEGER, PRIMARY KEY(user_id, ch_id));
CREATE TABLE IF NOT EXISTS managed(
  chat_id INTEGER PRIMARY KEY, title TEXT, send_songs INTEGER DEFAULT 0, added_at INTEGER);
CREATE TABLE IF NOT EXISTS attach(
  id INTEGER PRIMARY KEY AUTOINCREMENT, html TEXT, photo_id TEXT, btn_text TEXT, btn_url TEXT,
  enabled INTEGER DEFAULT 1);
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS admins(id INTEGER PRIMARY KEY);
""")


def q(sql, *a):
    return db.execute(sql, a).fetchall()


def q1(sql, *a):
    return db.execute(sql, a).fetchone()


def ex(sql, *a):
    return db.execute(sql, a).lastrowid


DEFAULTS = {"force_on": "1", "rotate_every": "2", "post_counter": "0", "protect": "0",
            "attach_mode": "all", "attach_idx": "0", "attach_ttl": "0",
            "spam_limit": str(SPAM_LIMIT)}


def gs(key, default=None):
    r = q1("SELECT value FROM settings WHERE key=?", key)
    if r:
        return r["value"]
    return DEFAULTS.get(key, default)


def ss(key, value):
    ex("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
       key, str(value))


# ───────────────────────────── ابزارها ─────────────────────────────

esc = html.escape
FA_DIGITS = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")
REASONS = ["مزاحم", "اسپم", "ترک کانال", "دیگر"]
STYLE_CYCLE = ["success", "danger", "primary"]
DEFAULT_BTN = "دانلود آهنگ کامل"


def now_ts():
    return int(time.time())


def fmt_ts(ts=None):
    d = datetime.fromtimestamp(ts or now_ts(), TZ)
    return d.strftime("%Y-%m-%d %H:%M")


def day_start(days_back=0):
    d = datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0)
    return int((d - timedelta(days=days_back)).timestamp())


def is_admin(uid):
    return uid in ENV_ADMINS or q1("SELECT 1 FROM admins WHERE id=?", uid) is not None


def all_admin_ids():
    return set(ENV_ADMINS) | {r["id"] for r in q("SELECT id FROM admins")}


def user_link(uid, name):
    return f'<a href="tg://user?id={uid}">{esc(name or str(uid))}</a>'


def B(text, cb=None, url=None, style=None):
    kw = {"text": text}
    if cb:
        kw["callback_data"] = cb
    if url:
        kw["url"] = url
    if style and STYLES_ON:
        kw["style"] = style
    return InlineKeyboardButton(**kw)


def kb(*rows):
    return InlineKeyboardMarkup(inline_keyboard=[list(r) for r in rows if r])


HOME_ROW = [B("↩️ منوی اصلی", "p:home")]
CANCEL_KB = kb([B("✖ لغو", "x:cancel", style="danger")])


async def show(target, text, markup=None):
    if isinstance(target, CallbackQuery):
        try:
            await target.message.edit_text(text, reply_markup=markup)
        except TelegramBadRequest as e:
            if "not modified" not in str(e):
                await target.message.answer(text, reply_markup=markup)
        try:
            await target.answer()
        except Exception:
            pass
    else:
        await target.answer(text, reply_markup=markup)


async def notify_admins(bot, text, markup=None):
    for aid in all_admin_ids():
        try:
            await bot.send_message(aid, text, reply_markup=markup)
        except Exception:
            pass


def join_log_chat():
    v = gs("join_log")
    return int(v) if v else ENV_JOIN_LOG


def dl_log_chat():
    v = gs("dl_log")
    return int(v) if v else ENV_DL_LOG


def parse_when(text):
    s = text.strip().translate(FA_DIGITS)
    m = re.fullmatch(r"(\d{4})-(\d{1,2})-(\d{1,2})\s+(\d{1,2}):(\d{2})", s)
    try:
        if m:
            y, mo, d, h, mi = map(int, m.groups())
            return int(datetime(y, mo, d, h, mi, tzinfo=TZ).timestamp())
        m = re.fullmatch(r"(\d{1,2}):(\d{2})", s)
        if m:
            h, mi = map(int, m.groups())
            t = datetime.now(TZ).replace(hour=h, minute=mi, second=0, microsecond=0)
            if t <= datetime.now(TZ):
                t += timedelta(days=1)
            return int(t.timestamp())
    except ValueError:
        return None
    return None


# ───────────────────────────── کپشن و دکمه‌ی پست ─────────────────────────────

def post_caption(title, artist, code):
    parts = [f"<blockquote><b>{esc(title)}</b>" + (f"\n<i>{esc(artist)}</i>" if artist else "") + "</blockquote>"]
    if code:
        parts.append(f"<blockquote>کد  {esc(code)}</blockquote>")
    parts.append(f'\n◜ <a href="{CHANNEL_LINK}">{CHANNEL_NAME}</a> ◞')
    return "\n".join(parts)


def download_markup(labels_urls, color_idx):
    """labels_urls: [(label, url)] . تا ۳ دکمه کنار هم، بیشتر زیر هم."""
    n = len(labels_urls)
    if not n:
        return None
    btns = []
    for i, (label, url) in enumerate(labels_urls):
        if label:
            text = label
        else:
            text = DEFAULT_BTN if n == 1 else f"دانلود {i + 1}"
        style = STYLE_CYCLE[(color_idx + i) % 3]
        btns.append(B(text, url=url, style=style))
    if n <= 3:
        return kb(btns)
    return kb(*[[b] for b in btns])


def song_url(song_id):
    return f"https://t.me/{G['bot_username']}?start=s{song_id}"


def peek_color():
    n = int(gs("post_counter", "0"))
    every = max(1, int(gs("rotate_every", "2")))
    return (n // every) % 3


def next_color():
    n = int(gs("post_counter", "0"))
    every = max(1, int(gs("rotate_every", "2")))
    ss("post_counter", n + 1)
    return (n // every) % 3


async def send_media(bot, chat_id, mt, fid, caption, markup=None):
    kw = {"caption": caption, "reply_markup": markup}
    if mt == "video":
        return await bot.send_video(chat_id, fid, **kw)
    if mt == "voice":
        return await bot.send_voice(chat_id, fid, **kw)
    if mt == "audio":
        return await bot.send_audio(chat_id, fid, **kw)
    return await bot.send_photo(chat_id, fid, **kw)


def post_markup(post_id):
    p = q1("SELECT * FROM posts WHERE id=?", post_id)
    if not p or not p["button_on"]:
        return None
    songs = q("SELECT * FROM songs WHERE post_id=? ORDER BY pos,id", post_id)
    return download_markup([(s["label"], song_url(s["id"])) for s in songs], p["color_idx"])


def post_url(post_id):
    r = q1("SELECT message_id FROM post_msgs WHERE post_id=? AND chat_id=?", post_id, G["main_id"])
    if not r:
        return None
    mid = r["message_id"]
    if isinstance(MAIN_CHANNEL, str) and MAIN_CHANNEL.startswith("@"):
        return f"https://t.me/{MAIN_CHANNEL[1:]}/{mid}"
    cid = str(G["main_id"])
    if cid.startswith("-100"):
        return f"https://t.me/c/{cid[4:]}/{mid}"
    return None


def publish_targets():
    ids = [G["main_id"]]
    for r in q("SELECT chat_id FROM managed WHERE send_songs=1"):
        if r["chat_id"] not in ids:
            ids.append(r["chat_id"])
    return ids


async def publish_post(bot, post_id):
    """پست را در کانال اصلی و کانال‌هایی که ارسال آهنگ دارند منتشر می‌کند."""
    p = q1("SELECT * FROM posts WHERE id=?", post_id)
    if not p:
        return ["پست پیدا نشد"]
    color = next_color()
    ex("UPDATE posts SET color_idx=? WHERE id=?", color, post_id)
    cap = post_caption(p["title"], p["artist"], p["code"])
    markup = post_markup(post_id)
    errors = []
    for chat_id in publish_targets():
        try:
            msg = await send_media(bot, chat_id, p["media_type"], p["media_id"], cap, markup)
            ex("INSERT INTO post_msgs(post_id,chat_id,message_id) VALUES(?,?,?)", post_id, chat_id, msg.message_id)
        except Exception as e:
            log.exception("publish failed")
            errors.append(f"{chat_id}: {e}")
    ex("UPDATE posts SET status='published' WHERE id=?", post_id)
    return errors


async def refresh_post(bot, post_id):
    p = q1("SELECT * FROM posts WHERE id=?", post_id)
    if not p:
        return
    cap = post_caption(p["title"], p["artist"], p["code"])
    markup = post_markup(post_id)
    for r in q("SELECT * FROM post_msgs WHERE post_id=?", post_id):
        try:
            await bot.edit_message_caption(chat_id=r["chat_id"], message_id=r["message_id"],
                                           caption=cap, reply_markup=markup)
        except TelegramBadRequest as e:
            if "not modified" not in str(e):
                log.warning("refresh failed: %s", e)
        except Exception as e:
            log.warning("refresh failed: %s", e)


# ───────────────────────────── آماده‌سازی فایل آهنگ ─────────────────────────────

async def make_thumb(bot, cover_id):
    try:
        buf = io.BytesIO()
        await bot.download(cover_id, destination=buf)
        data = buf.getvalue()
        try:
            from PIL import Image
            im = Image.open(io.BytesIO(data)).convert("RGB")
            im.thumbnail((320, 320))
            out = io.BytesIO()
            im.save(out, "JPEG", quality=85)
            data = out.getvalue()
        except Exception:
            pass
        return BufferedInputFile(data, filename="cover.jpg")
    except Exception:
        return None


async def retag(bot, v, title, artist, cover_id, store_chat):
    """نام آهنگ، خواننده و کاور را روی خود فایل می‌نویسد. در صورت خطا همان فایل اصلی می‌ماند."""
    ftype = v["file_type"]
    if ftype == "voice":
        return v["file_id"], "voice"
    if ftype == "document" and not (v.get("mime") or "").startswith("audio"):
        return v["file_id"], ftype
    if v.get("size", 0) > 20 * 1024 * 1024:
        return v["file_id"], ftype  # محدودیت دانلود Bot API
    try:
        buf = io.BytesIO()
        await bot.download(v["file_id"], destination=buf)
        name = v.get("name") or f"{title}.mp3"
        thumb = await make_thumb(bot, cover_id) if cover_id else None
        for th in ([thumb, None] if thumb else [None]):
            try:
                msg = await bot.send_audio(store_chat, BufferedInputFile(buf.getvalue(), filename=name),
                                           title=title, performer=artist or None, thumbnail=th)
                fid = msg.audio.file_id
                try:
                    await msg.delete()
                except Exception:
                    pass
                return fid, "audio"
            except TelegramBadRequest:
                continue
    except Exception:
        log.exception("retag failed")
    return v["file_id"], ftype


async def create_post(bot, data, admin_chat, status, run_at=None, by=0):
    cover = data.get("cover")
    post_id = ex(
        "INSERT INTO posts(kind,media_type,media_id,title,artist,code,button_on,status,created_at,run_at,created_by)"
        " VALUES(?,?,?,?,?,?,?,?,?,?,?)",
        data["kind"], data["media_type"], data["media_id"], data["title"], data["artist"], data["code"],
        1 if data["button_on"] else 0, status, now_ts(), run_at, by)
    store = STORAGE_CHAT or admin_chat
    for i, v in enumerate(data.get("versions", [])):
        fid, ft = await retag(bot, v, data["title"], data["artist"], cover, store)
        ex("INSERT INTO songs(post_id,pos,label,file_id,file_type) VALUES(?,?,?,?,?)",
           post_id, i, v.get("label", ""), fid, ft)
    return post_id


# ───────────────────────────── کاربر، لاگ، بلاک ─────────────────────────────

def upsert_user(u):
    r = q1("SELECT id FROM users WHERE id=?", u.id)
    if r:
        ex("UPDATE users SET first_name=?, username=?, active=1 WHERE id=?", u.first_name, u.username, u.id)
        return False
    ex("INSERT INTO users(id,first_name,username,joined_at) VALUES(?,?,?,?)",
       u.id, u.first_name, u.username, now_ts())
    return True


def is_blocked(uid):
    r = q1("SELECT blocked FROM users WHERE id=?", uid)
    return bool(r and r["blocked"])


def block_kb(uid):
    if is_blocked(uid):
        return kb([B("🟢 آنبلاک", f"ub:{uid}", style="success")])
    return kb([B("🔴 بلاک کاربر", f"bk:{uid}", style="danger")])


def who_line(uid, name, username):
    uname = f"@{esc(username)}" if username else "—"
    return f"{user_link(uid, name)} | {uname} | <code>{uid}</code>"


async def send_log(bot, chat, text, uid=None):
    if not chat:
        return
    try:
        await bot.send_message(chat, text, reply_markup=block_kb(uid) if uid else None)
    except Exception as e:
        log.warning("log send failed: %s", e)


def channel_ids():
    ids = {G["main_id"]}
    ids |= {r["chat_id"] for r in q("SELECT chat_id FROM managed")}
    return ids


async def do_block(bot, uid, reason):
    if q1("SELECT 1 FROM users WHERE id=?", uid):
        ex("UPDATE users SET blocked=1, block_reason=?, blocked_at=? WHERE id=?", reason, now_ts(), uid)
    else:
        ex("INSERT INTO users(id,first_name,joined_at,blocked,block_reason,blocked_at) VALUES(?,?,?,?,?,?)",
           uid, str(uid), now_ts(), 1, reason, now_ts())
    for cid in channel_ids():
        try:
            await bot.ban_chat_member(cid, uid)
        except Exception as e:
            log.warning("ban failed in %s: %s", cid, e)


async def do_unblock(bot, uid):
    ex("UPDATE users SET blocked=0, block_reason=NULL WHERE id=?", uid)
    for cid in channel_ids():
        try:
            await bot.unban_chat_member(cid, uid, only_if_banned=True)
        except Exception as e:
            log.warning("unban failed in %s: %s", cid, e)


dl_times = defaultdict(deque)
limited_until = {}


def spam_check(uid):
    limit = int(gs("spam_limit", "8"))
    if limit <= 0:
        return None
    now = time.time()
    if limited_until.get(uid, 0) > now:
        return "limited"
    dq = dl_times[uid]
    dq.append(now)
    while dq and now - dq[0] > 60:
        dq.popleft()
    if len(dq) > limit:
        limited_until[uid] = now + 300
        return "alert"
    return None


# ───────────────────────────── عضویت اجباری ─────────────────────────────

pending_missing = set()


async def is_member(bot, chat_id, uid):
    try:
        m = await bot.get_chat_member(chat_id, uid)
    except (TelegramBadRequest, TelegramForbiddenError):
        return None
    if m.status in ("creator", "administrator", "member"):
        return True
    if m.status == "restricted":
        return bool(getattr(m, "is_member", False))
    return False


async def bot_is_admin(bot, chat_id):
    try:
        m = await bot.get_chat_member(chat_id, G["bot_id"])
        return m.status in ("administrator", "creator")
    except Exception:
        return False


async def force_status(bot, uid):
    missing, pending = [], []
    for ch in q("SELECT * FROM force_channels WHERE enabled=1 ORDER BY sort,id"):
        confirmed = q1("SELECT 1 FROM force_ok WHERE user_id=? AND ch_id=?", uid, ch["id"])
        if ch["checked"] and ch["chat_id"]:
            ok = await is_member(bot, ch["chat_id"], uid)
            if ok is None:
                ex("UPDATE force_channels SET checked=0 WHERE id=?", ch["id"])
                if not confirmed:
                    pending.append(ch)
            elif not ok:
                missing.append(ch)
                pending_missing.add((uid, ch["id"]))
        elif not confirmed:
            pending.append(ch)
    return missing, pending


async def send_join_prompt(bot, uid, song_id, chans):
    rows = [[B(f"🔵 {c['title']}", url=c["link"], style="primary")] for c in chans if c["link"]]
    rows.append([B("🟢 عضو شدم", f"ok:{song_id}", style="success")])
    await bot.send_message(uid, "برای دریافت آهنگ، عضو این کانال‌ها شو 👇", reply_markup=kb(*rows))


# ───────────────────────────── ارسال آهنگ ─────────────────────────────

async def delete_later(bot, chat_id, mid, sec):
    await asyncio.sleep(sec)
    try:
        await bot.delete_message(chat_id, mid)
    except Exception:
        pass


async def send_attach_item(bot, chat_id, it):
    markup = None
    if it["btn_text"] and it["btn_url"]:
        markup = kb([B(it["btn_text"], url=it["btn_url"], style="primary")])
    if it["photo_id"]:
        return await bot.send_photo(chat_id, it["photo_id"], caption=it["html"], reply_markup=markup)
    return await bot.send_message(chat_id, it["html"], reply_markup=markup)


async def send_attachments(bot, uid):
    items = q("SELECT * FROM attach WHERE enabled=1 ORDER BY id")
    if not items:
        return
    mode = gs("attach_mode", "all")
    if mode == "rotate":
        idx = int(gs("attach_idx", "0"))
        chosen = [items[idx % len(items)]]
        ss("attach_idx", idx + 1)
    elif mode == "random":
        chosen = [random.choice(items)]
    else:
        chosen = items
    ttl = int(gs("attach_ttl", "0"))
    for it in chosen:
        try:
            msg = await send_attach_item(bot, uid, it)
            if ttl:
                asyncio.create_task(delete_later(bot, uid, msg.message_id, ttl))
        except Exception as e:
            log.warning("attach send failed: %s", e)


async def send_song(bot, user, song):
    uid = user.id
    cap = f"<b>{esc(song['title'])}</b>"
    if song["artist"]:
        cap += f" · {esc(song['artist'])}"
    if song["label"]:
        cap += f" · {esc(song['label'])}"
    cap += f'\n◜ <a href="{CHANNEL_LINK}">{CHANNEL_NAME}</a> ◞'
    url = post_url(song["pid"])
    markup = kb([B("🔵 دیدن پست در کانال", url=url, style="primary")]) if url else None
    protect = gs("protect", "0") == "1"
    kw = {"caption": cap, "reply_markup": markup, "protect_content": protect}
    try:
        ft = song["file_type"]
        if ft == "voice":
            await bot.send_voice(uid, song["file_id"], **kw)
        elif ft == "document":
            await bot.send_document(uid, song["file_id"], **kw)
        else:
            await bot.send_audio(uid, song["file_id"], **kw)
    except TelegramForbiddenError:
        return
    except TelegramBadRequest as e:
        log.exception("song send failed")
        await bot.send_message(uid, "مشکلی پیش اومد، چند لحظه‌ی دیگه دوباره امتحان کن ⚠️")
        await notify_admins(bot, f"⚠️ ارسال آهنگ ناموفق بود\nکد: {esc(song['code'] or '')}\n{esc(str(e))}")
        return
    ex("INSERT INTO downloads(song_id,user_id,ts) VALUES(?,?,?)", song["id"], uid, now_ts())
    ex("UPDATE songs SET downloads=downloads+1 WHERE id=?", song["id"])
    n = q1("SELECT downloads FROM songs WHERE id=?", song["id"])["downloads"]
    await send_attachments(bot, uid)
    label = f" · نسخه {esc(song['label'])}" if song["label"] else ""
    text = (f"⬇️ <b>دانلود</b>\n"
            f"آهنگ: {esc(song['title'])} - {esc(song['artist'] or '')}{label} · کد: {esc(song['code'] or '')}\n"
            f"کاربر: {who_line(uid, user.first_name, user.username)}\n"
            f"زمان: {fmt_ts()} | دانلود شماره {n}")
    await send_log(bot, dl_log_chat(), text, uid)


async def request_song(bot, user, song_id):
    uid = user.id
    song = q1("SELECT s.*, p.title, p.artist, p.code, p.status, p.id AS pid FROM songs s "
              "JOIN posts p ON p.id=s.post_id WHERE s.id=?", song_id)
    if not song or song["status"] == "deleted":
        await bot.send_message(uid, "این آهنگ دیگه موجود نیست ❌")
        return
    if not is_admin(uid):
        r = spam_check(uid)
        if r:
            await bot.send_message(uid, "کمی صبر کن، بعداً دوباره امتحان کن ⏳")
            if r == "alert":
                await send_log(bot, dl_log_chat(),
                               f"⚠️ <b>هشدار اسپم</b>\n{who_line(uid, user.first_name, user.username)}\n"
                               f"درخواست‌های پشت‌سرهم دانلود. تا ۵ دقیقه محدود شد.\n{fmt_ts()}", uid)
            return
    if gs("force_on", "1") == "1":
        missing, pending = await force_status(bot, uid)
        if missing or pending:
            await send_join_prompt(bot, uid, song_id, missing + pending)
            return
    await send_song(bot, user, song)


# ───────────────────────────── روترها و فیلترها ─────────────────────────────

admin = Router()
public = Router()


class IsAdmin(Filter):
    async def __call__(self, event) -> bool:
        u = getattr(event, "from_user", None)
        return bool(u and is_admin(u.id))


admin.message.filter(IsAdmin())
admin.callback_query.filter(IsAdmin())


class BlockMW(BaseMiddleware):
    async def __call__(self, handler, event, data):
        u = getattr(event, "from_user", None)
        if u and not is_admin(u.id) and is_blocked(u.id):
            return None
        return await handler(event, data)


class NP(StatesGroup):
    media = State()
    title = State()
    artist = State()
    code = State()
    vfile = State()
    vlabel = State()
    cover = State()
    when = State()


class EF(StatesGroup):
    val = State()


class PV(StatesGroup):
    file = State()
    label = State()


class AT(StatesGroup):
    content = State()
    button = State()


class BC(StatesGroup):
    msg = State()


class FJ(StatesGroup):
    add = State()
    title = State()
    link = State()
    edit = State()


class MC(StatesGroup):
    add = State()


class BL(StatesGroup):
    uid = State()


class ADM(StatesGroup):
    add = State()


# ───────────────────────────── کاربر عادی ─────────────────────────────

def welcome_kb():
    return kb([B("🔵 ورود به کانال", url=CHANNEL_LINK, style="primary")])


@public.message(CommandStart(deep_link=True), F.chat.type == "private")
async def start_link(m: Message, command: CommandObject, bot: Bot):
    new = upsert_user(m.from_user)
    if new:
        await send_log(bot, join_log_chat(),
                       f"🟢 <b>استارت ربات</b>\n{who_line(m.from_user.id, m.from_user.first_name, m.from_user.username)}\n{fmt_ts()}",
                       m.from_user.id)
    arg = command.args or ""
    if re.fullmatch(r"s\d+", arg):
        await request_song(bot, m.from_user, int(arg[1:]))
    else:
        await m.answer(WELCOME, reply_markup=welcome_kb())


@public.message(CommandStart(), F.chat.type == "private")
async def start_plain(m: Message, bot: Bot):
    new = upsert_user(m.from_user)
    if new:
        await send_log(bot, join_log_chat(),
                       f"🟢 <b>استارت ربات</b>\n{who_line(m.from_user.id, m.from_user.first_name, m.from_user.username)}\n{fmt_ts()}",
                       m.from_user.id)
    await m.answer(WELCOME, reply_markup=welcome_kb())


@public.message(Command("channel"), F.chat.type == "private")
async def cmd_channel(m: Message):
    upsert_user(m.from_user)
    await m.answer("کانال Rudig Sounds 👇", reply_markup=welcome_kb())


@public.callback_query(F.data.startswith("ok:"))
async def cb_ok(cb: CallbackQuery, bot: Bot):
    uid = cb.from_user.id
    song_id = int(cb.data[3:])
    missing, pending = await force_status(bot, uid)
    if missing:
        await cb.answer(f"هنوز عضو «{missing[0]['title']}» نشدی ❌", show_alert=True)
        return
    for (u, chid) in list(pending_missing):
        if u == uid:
            pending_missing.discard((u, chid))
            ex("INSERT OR IGNORE INTO force_ok(user_id,ch_id) VALUES(?,?)", uid, chid)
            ex("INSERT INTO force_events(ch_id,user_id,kind,ts) VALUES(?,?,?,?)", chid, uid, "join", now_ts())
    for ch in pending:
        ex("INSERT OR IGNORE INTO force_ok(user_id,ch_id) VALUES(?,?)", uid, ch["id"])
        ex("INSERT INTO force_events(ch_id,user_id,kind,ts) VALUES(?,?,?,?)", ch["id"], uid, "confirm", now_ts())
    await cb.answer()
    try:
        await cb.message.delete()
    except Exception:
        pass
    await request_song(bot, cb.from_user, song_id)


@public.my_chat_member()
async def on_my_chat_member(ev: ChatMemberUpdated, bot: Bot):
    chat = ev.chat
    new, old = ev.new_chat_member.status, ev.old_chat_member.status
    if chat.type == "private":
        if new == "kicked":
            ex("UPDATE users SET active=0 WHERE id=?", ev.from_user.id)
            await send_log(bot, join_log_chat(),
                           f"🚫 <b>ربات را بلاک کرد</b>\n{who_line(ev.from_user.id, ev.from_user.first_name, ev.from_user.username)}\n{fmt_ts()}",
                           ev.from_user.id)
        elif new == "member":
            ex("UPDATE users SET active=1 WHERE id=?", ev.from_user.id)
        return
    if new == "administrator" and old != "administrator":
        ex("UPDATE force_channels SET checked=1 WHERE chat_id=?", chat.id)
        if chat.id not in channel_ids():
            await notify_admins(
                bot, f"ربات ادمین «{esc(chat.title or '')}» شد. اضافه‌اش کنم؟",
                kb([B("🟢 بله", f"mc:y:{chat.id}", style="success"), B("🔴 نه", f"mc:n:{chat.id}", style="danger")]))
    elif new in ("left", "kicked"):
        ex("UPDATE force_channels SET checked=0 WHERE chat_id=?", chat.id)


@public.chat_member()
async def on_chat_member(ev: ChatMemberUpdated, bot: Bot):
    cid = ev.chat.id
    row = q1("SELECT title FROM managed WHERE chat_id=?", cid)
    if not row and cid != G["main_id"]:
        return
    user = ev.new_chat_member.user
    if user.is_bot:
        return
    inside = ("member", "administrator", "creator")
    old, new = ev.old_chat_member.status, ev.new_chat_member.status
    title = esc(ev.chat.title or (row["title"] if row else ""))
    if old not in inside and new in inside:
        head = f"🟢 <b>عضو شد</b> · {title}"
    elif old in inside and new == "kicked":
        head = f"⛔ <b>بن شد</b> · {title}"
    elif old in inside and new == "left":
        head = f"🔴 <b>کانال را ترک کرد</b> · {title}"
    else:
        return
    await send_log(bot, join_log_chat(),
                   f"{head}\n{who_line(user.id, user.first_name, user.username)}\n{fmt_ts()}", user.id)


@public.message(F.chat.type == "private")
async def fallback(m: Message):
    upsert_user(m.from_user)
    await m.answer(WELCOME, reply_markup=welcome_kb())


# ───────────────────────────── پنل: صفحه‌ی اصلی ─────────────────────────────

def home_text():
    users = q1("SELECT COUNT(*) c FROM users")["c"]
    new_today = q1("SELECT COUNT(*) c FROM users WHERE joined_at>=?", day_start())["c"]
    dl_today = q1("SELECT COUNT(*) c FROM downloads WHERE ts>=?", day_start())["c"]
    posts = q1("SELECT COUNT(*) c FROM posts WHERE status IN ('published','scheduled')")["c"]
    blocked = q1("SELECT COUNT(*) c FROM users WHERE blocked=1")["c"]
    return (f"⚙️ <b>پنل مدیریت Rudig Sounds</b>\n━━━━━━━━━━━━━━\n"
            f"کاربران: {users} (امروز +{new_today}) | دانلود امروز: {dl_today}\n"
            f"پست‌ها: {posts} | بلاک‌شده: {blocked}")


def home_kb():
    return kb(
        [B("🟢 ساخت پست جدید", "p:new", style="success")],
        [B("🎵 آهنگ‌ها", "p:list:0", style="primary"), B("📊 آمار", "p:stats", style="primary")],
        [B("📎 پیام پیوست", "p:attach", style="primary"), B("📣 پیام همگانی", "p:bc", style="primary")],
        [B("📢 عضویت اجباری", "p:fj", style="primary"), B("📡 کانال‌های مدیریت‌شده", "p:mc", style="primary")],
        [B("🚫 بلاک‌لیست", "p:bl", style="danger"), B("🕒 زمان‌بندی", "p:sc", style="primary")],
        [B("⚙️ تنظیمات", "p:set", style="primary")])


@admin.message(Command("panel"), F.chat.type == "private")
async def cmd_panel(m: Message, state: FSMContext):
    await state.clear()
    await m.answer(home_text(), reply_markup=home_kb())


@admin.message(Command("start"), F.chat.type == "private")
async def admin_start(m: Message, state: FSMContext, command: CommandObject, bot: Bot):
    await state.clear()
    arg = command.args or ""
    if re.fullmatch(r"s\d+", arg):
        upsert_user(m.from_user)
        await request_song(bot, m.from_user, int(arg[1:]))
        return
    await m.answer(home_text(), reply_markup=home_kb())


@admin.callback_query(F.data.in_({"p:home", "x:cancel"}))
async def cb_home(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    await show(cb, home_text(), home_kb())


# ───────────────────────────── ساخت پست ─────────────────────────────

KIND_NAMES = {"video": "🎬 ویدیو", "voice": "🎤 ویس", "audio": "🎵 آهنگ", "photo": "🖼 عکس"}
KIND_ASK = {"video": "ویدیوی پیش‌نمایش را بفرستید.", "voice": "ویس پیش‌نمایش را بفرستید.",
            "audio": "فایل آهنگ را بفرستید (به‌صورت Audio).", "photo": "عکس را بفرستید."}


@admin.callback_query(F.data == "p:new")
async def np_start(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    await show(cb, "نوع پست چیه؟", kb(
        [B("🎬 ویدیو", "nk:video", style="primary"), B("🎤 ویس", "nk:voice", style="primary")],
        [B("🎵 آهنگ", "nk:audio", style="primary"), B("🖼 عکس", "nk:photo", style="primary")],
        HOME_ROW))


@admin.callback_query(F.data.startswith("nk:"))
async def np_kind(cb: CallbackQuery, state: FSMContext):
    kind = cb.data[3:]
    await state.set_data({"kind": kind, "versions": []})
    await state.set_state(NP.media)
    await show(cb, KIND_ASK[kind], CANCEL_KB)


def file_info(m: Message):
    if m.audio:
        o, t = m.audio, "audio"
    elif m.voice:
        o, t = m.voice, "voice"
    elif m.document:
        o, t = m.document, "document"
    else:
        return None
    return {"file_id": o.file_id, "file_type": t, "size": o.file_size or 0,
            "name": getattr(o, "file_name", None), "mime": getattr(o, "mime_type", None) or ""}


@admin.message(NP.media)
async def np_media(m: Message, state: FSMContext):
    d = await state.get_data()
    kind = d["kind"]
    fid = None
    if kind == "video" and m.video:
        fid = m.video.file_id
    elif kind == "voice" and m.voice:
        fid = m.voice.file_id
    elif kind == "audio" and m.audio:
        fid = m.audio.file_id
        await state.update_data(media_info=file_info(m))
    elif kind == "photo" and m.photo:
        fid = m.photo[-1].file_id
    if not fid:
        await m.answer(f"فایل با نوع پست نمی‌خواند. {KIND_ASK[kind]}", reply_markup=CANCEL_KB)
        return
    await state.update_data(media_type=kind, media_id=fid)
    await state.set_state(NP.title)
    await m.answer("نام آهنگ را بنویسید.", reply_markup=CANCEL_KB)


@admin.message(NP.title, F.text)
async def np_title(m: Message, state: FSMContext):
    await state.update_data(title=m.text.strip()[:200])
    await state.set_state(NP.artist)
    await m.answer("نام خواننده را بنویسید. (برای رد کردن «-» بفرستید)", reply_markup=CANCEL_KB)


def next_code():
    n = q1("SELECT COUNT(*) c FROM posts")["c"] + 1
    while True:
        c = f"{n:03d}"
        if not q1("SELECT 1 FROM posts WHERE lower(code)=lower(?) AND status!='deleted'", c):
            return c
        n += 1


@admin.message(NP.artist, F.text)
async def np_artist(m: Message, state: FSMContext):
    a = m.text.strip()
    await state.update_data(artist="" if a == "-" else a[:200])
    await state.set_state(NP.code)
    await m.answer("کد آهنگ را بنویسید (فقط برای جستجو در کانال). یا خودکار بسازم؟",
                   reply_markup=kb([B("🎲 خودکار بساز", "cd:auto", style="primary")], [B("✖ لغو", "x:cancel", style="danger")]))


async def ask_button(target, state, kind):
    await state.set_state(None)
    default_on = kind in ("video", "voice")
    await show(target, f"دکمه‌ی دانلود زیر پست باشد؟\n(پیش‌فرض برای این نوع: {'روشن' if default_on else 'خاموش'})",
               kb([B("🟢 دکمه روشن", "bt:1", style="success"), B("🔴 دکمه خاموش", "bt:0", style="danger")],
                  [B("✖ لغو", "x:cancel")]))


@admin.callback_query(NP.code, F.data == "cd:auto")
async def np_code_auto(cb: CallbackQuery, state: FSMContext):
    d = await state.update_data(code=next_code())
    await ask_button(cb, state, d["kind"])


@admin.message(NP.code, F.text)
async def np_code(m: Message, state: FSMContext):
    c = m.text.strip()
    if len(c) > 40 or "\n" in c:
        await m.answer("کد باید یک خط و حداکثر ۴۰ کاراکتر باشد.", reply_markup=CANCEL_KB)
        return
    if q1("SELECT 1 FROM posts WHERE lower(code)=lower(?) AND status!='deleted'", c):
        await m.answer("این کد قبلاً هست ❌ کد دیگری بنویسید.", reply_markup=CANCEL_KB)
        return
    d = await state.update_data(code=c)
    await ask_button(m, state, d["kind"])


async def ask_version_file(target, state, n):
    await state.set_state(NP.vfile)
    await show(target, f"فایل آهنگ کامل (نسخه {n}) را بفرستید.", CANCEL_KB)


@admin.callback_query(F.data.startswith("bt:"))
async def np_button(cb: CallbackQuery, state: FSMContext):
    on = cb.data == "bt:1"
    d = await state.update_data(button_on=on)
    if not on:
        await np_review(cb, state, cb.bot)
        return
    if d["kind"] == "audio" and d.get("media_info") and not d["versions"]:
        await state.update_data(pending=d["media_info"])
        await state.set_state(NP.vlabel)
        await show(cb, "آهنگ همان فایل پست است. نام نسخه را بنویسید (اختیاری).",
                   kb([B("⏭ بدون نام", "vl:skip")], [B("✖ لغو", "x:cancel", style="danger")]))
        return
    await ask_version_file(cb, state, len(d["versions"]) + 1)


@admin.message(NP.vfile)
async def np_vfile(m: Message, state: FSMContext):
    info = file_info(m)
    if not info:
        await m.answer("فایل صوتی (Audio، Voice یا فایل) بفرستید.", reply_markup=CANCEL_KB)
        return
    await state.update_data(pending=info)
    await state.set_state(NP.vlabel)
    await m.answer("نام نسخه را بنویسید (اختیاری).",
                   reply_markup=kb([B("⏭ بدون نام", "vl:skip")], [B("✖ لغو", "x:cancel", style="danger")]))


async def finish_version(target, state, label):
    d = await state.get_data()
    v = dict(d["pending"])
    v["label"] = label
    vs = d["versions"] + [v]
    await state.update_data(versions=vs, pending=None)
    rows = []
    if len(vs) < 8:
        rows.append([B("➕ نسخه دیگر", "vm:more", style="primary")])
    rows.append([B("✅ ادامه", "vm:done", style="success")])
    await state.set_state(None)
    await show(target, f"نسخه {len(vs)} ثبت شد ✅", kb(*rows))


@admin.callback_query(NP.vlabel, F.data == "vl:skip")
async def np_vl_skip(cb: CallbackQuery, state: FSMContext):
    await finish_version(cb, state, "")


@admin.message(NP.vlabel, F.text)
async def np_vlabel(m: Message, state: FSMContext):
    await finish_version(m, state, m.text.strip()[:30])


@admin.callback_query(F.data == "vm:more")
async def np_more(cb: CallbackQuery, state: FSMContext):
    d = await state.get_data()
    await ask_version_file(cb, state, len(d.get("versions", [])) + 1)


@admin.callback_query(F.data == "vm:done")
async def np_vdone(cb: CallbackQuery, state: FSMContext):
    await state.set_state(NP.cover)
    await show(cb, "کاور آهنگ را بفرستید (اختیاری، روی فایل آهنگ می‌نشیند).",
               kb([B("⏭ بدون کاور", "cov:skip")], [B("✖ لغو", "x:cancel", style="danger")]))


@admin.message(NP.cover, F.photo)
async def np_cover(m: Message, state: FSMContext, bot: Bot):
    await state.update_data(cover=m.photo[-1].file_id)
    await np_review(m, state, bot)


@admin.callback_query(NP.cover, F.data == "cov:skip")
async def np_cover_skip(cb: CallbackQuery, state: FSMContext, bot: Bot):
    await np_review(cb, state, bot)


async def np_review(target, state, bot):
    d = await state.get_data()
    chat_id = target.message.chat.id if isinstance(target, CallbackQuery) else target.chat.id
    if isinstance(target, CallbackQuery):
        await target.answer()
    cap = post_caption(d["title"], d["artist"], d["code"])
    markup = None
    if d["button_on"] and d["versions"]:
        markup = download_markup([(v["label"], song_url(0)) for v in d["versions"]], peek_color())
    try:
        await send_media(bot, chat_id, d["media_type"], d["media_id"], cap, markup)
    except Exception as e:
        await bot.send_message(chat_id, f"خطا در پیش‌نمایش: {esc(str(e))}")
    await state.set_state(None)
    await bot.send_message(chat_id, "👆 پیش‌نمایش پست. چه کنم؟", reply_markup=kb(
        [B("🟢 انتشار الان", "rv:pub", style="success"), B("🕒 زمان‌بندی", "rv:sched", style="primary")],
        [B("✖ لغو", "x:cancel", style="danger")]))


@admin.callback_query(F.data == "rv:pub")
async def rv_pub(cb: CallbackQuery, state: FSMContext, bot: Bot):
    d = await state.get_data()
    if not d.get("title"):
        await cb.answer("اطلاعات پست پیدا نشد، دوباره شروع کنید.", show_alert=True)
        return
    await show(cb, "⏳ در حال آماده‌سازی و انتشار...")
    post_id = await create_post(bot, d, cb.message.chat.id, "draft", by=cb.from_user.id)
    errs = await publish_post(bot, post_id)
    await state.clear()
    msg = "✅ پست منتشر شد." if not errs else "⚠️ مشکل در انتشار:\n" + "\n".join(esc(e) for e in errs)
    await bot.send_message(cb.message.chat.id, msg, reply_markup=kb([B("🎵 مدیریت این پست", f"p:post:{post_id}")], HOME_ROW))


@admin.callback_query(F.data == "rv:sched")
async def rv_sched(cb: CallbackQuery, state: FSMContext):
    await state.set_state(NP.when)
    await show(cb, "زمان انتشار را بفرستید:\n<code>21:30</code> (امروز یا فردا)\nیا <code>2026-12-01 21:30</code>\n"
                   f"(به وقت {TZ.key})", CANCEL_KB)


@admin.message(NP.when, F.text)
async def np_when(m: Message, state: FSMContext, bot: Bot):
    ts = parse_when(m.text)
    if not ts or ts <= now_ts():
        await m.answer("زمان معتبر نیست. نمونه: <code>21:30</code>", reply_markup=CANCEL_KB)
        return
    d = await state.get_data()
    wait = await m.answer("⏳ در حال آماده‌سازی...")
    post_id = await create_post(bot, d, m.chat.id, "scheduled", run_at=ts, by=m.from_user.id)
    await state.clear()
    await wait.edit_text(f"🕒 پست برای {fmt_ts(ts)} زمان‌بندی شد.", reply_markup=kb([B("🕒 زمان‌بندی‌ها", "p:sc")], HOME_ROW))


async def scheduler(bot):
    while True:
        try:
            for p in q("SELECT id, created_by, title FROM posts WHERE status='scheduled' AND run_at<=?", now_ts()):
                ex("UPDATE posts SET status='publishing' WHERE id=?", p["id"])
                errs = await publish_post(bot, p["id"])
                txt = f"🕒 پست زمان‌بندی‌شده «{esc(p['title'])}» " + ("منتشر شد ✅" if not errs else "با خطا مواجه شد ⚠️")
                if p["created_by"]:
                    try:
                        await bot.send_message(p["created_by"], txt)
                    except Exception:
                        pass
        except Exception:
            log.exception("scheduler error")
        await asyncio.sleep(20)


@admin.callback_query(F.data == "p:sc")
async def p_sched(cb: CallbackQuery):
    rows = q("SELECT * FROM posts WHERE status='scheduled' ORDER BY run_at")
    if not rows:
        await show(cb, "پست زمان‌بندی‌شده‌ای نیست.", kb(HOME_ROW))
        return
    text = "🕒 <b>پست‌های زمان‌بندی‌شده</b>\n" + "\n".join(
        f"• {esc(r['title'])} — {fmt_ts(r['run_at'])}" for r in rows)
    btns = [[B(f"🗑 لغو: {r['title'][:20]}", f"sc:d:{r['id']}", style="danger")] for r in rows]
    await show(cb, text, kb(*btns, HOME_ROW))


@admin.callback_query(F.data.startswith("sc:d:"))
async def sched_del(cb: CallbackQuery):
    pid = int(cb.data.split(":")[2])
    ex("UPDATE posts SET status='deleted' WHERE id=? AND status='scheduled'", pid)
    await p_sched(cb)


# ───────────────────────────── لیست و ویرایش آهنگ‌ها ─────────────────────────────

@admin.callback_query(F.data.startswith("p:list:"))
async def p_list(cb: CallbackQuery):
    page = int(cb.data.split(":")[2])
    per = 8
    rows = q("SELECT * FROM posts WHERE status IN ('published','scheduled') ORDER BY id DESC LIMIT ? OFFSET ?",
             per + 1, page * per)
    if not rows and page == 0:
        await show(cb, "هنوز پستی نیست.", kb(HOME_ROW))
        return
    btns = [[B(f"{r['code'] or '-'} · {r['title'][:28]}", f"p:post:{r['id']}", style="primary")] for r in rows[:per]]
    nav = []
    if page > 0:
        nav.append(B("◀️ قبلی", f"p:list:{page - 1}"))
    if len(rows) > per:
        nav.append(B("بعدی ▶️", f"p:list:{page + 1}"))
    await show(cb, "🎵 <b>پست‌ها</b> (جدیدترین اول)", kb(*btns, nav, HOME_ROW))


def post_panel(post_id):
    p = q1("SELECT * FROM posts WHERE id=?", post_id)
    if not p:
        return "پست پیدا نشد.", kb(HOME_ROW)
    songs = q("SELECT * FROM songs WHERE post_id=? ORDER BY pos,id", post_id)
    total = sum(s["downloads"] for s in songs)
    text = (f"🎵 <b>{esc(p['title'])}</b> — {esc(p['artist'] or '')}\n"
            f"کد: {esc(p['code'] or '')}\n"
            f"دکمه‌ی دانلود: {'🟢 روشن' if p['button_on'] else '🔴 خاموش'}\n"
            f"نسخه‌ها: {len(songs)} | کل دانلود: {total}\n"
            f"وضعیت: {p['status']}")
    return text, kb(
        [B("✏️ عنوان", f"pe:{post_id}:title"), B("✏️ خواننده", f"pe:{post_id}:artist"), B("✏️ کد", f"pe:{post_id}:code")],
        [B("🔘 روشن/خاموش دکمه", f"pb:{post_id}", style="primary"), B("🎧 نسخه‌ها", f"pv:{post_id}", style="primary")],
        [B("🗑 حذف پست", f"pd:{post_id}", style="danger")],
        [B("↩️ لیست", "p:list:0")])


@admin.callback_query(F.data.startswith("p:post:"))
async def p_post(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    text, markup = post_panel(int(cb.data.split(":")[2]))
    await show(cb, text, markup)


@admin.callback_query(F.data.startswith("pe:"))
async def pe_start(cb: CallbackQuery, state: FSMContext):
    _, pid, field = cb.data.split(":")
    await state.set_state(EF.val)
    await state.set_data({"pid": int(pid), "field": field})
    names = {"title": "نام آهنگ", "artist": "نام خواننده", "code": "کد"}
    await show(cb, f"{names.get(field, field)} جدید را بنویسید.", CANCEL_KB)


@admin.message(EF.val, F.text)
async def pe_val(m: Message, state: FSMContext, bot: Bot):
    d = await state.get_data()
    pid, field, val = d["pid"], d["field"], m.text.strip()
    if field == "code":
        if q1("SELECT 1 FROM posts WHERE lower(code)=lower(?) AND status!='deleted' AND id!=?", val, pid):
            await m.answer("این کد قبلاً هست ❌", reply_markup=CANCEL_KB)
            return
    if field.startswith("label:"):
        ex("UPDATE songs SET label=? WHERE id=?", "" if val == "-" else val[:30], int(field.split(":")[1]))
    elif field in ("title", "artist", "code"):
        ex(f"UPDATE posts SET {field}=? WHERE id=?", val[:200], pid)
    await state.clear()
    await refresh_post(bot, pid)
    text, markup = post_panel(pid)
    await m.answer("✅ ذخیره شد و پست کانال به‌روز شد.\n\n" + text, reply_markup=markup)


@admin.callback_query(F.data.startswith("pb:"))
async def pb_toggle(cb: CallbackQuery, bot: Bot):
    pid = int(cb.data[3:])
    p = q1("SELECT * FROM posts WHERE id=?", pid)
    n = q1("SELECT COUNT(*) c FROM songs WHERE post_id=?", pid)["c"]
    if not p["button_on"] and n == 0:
        await cb.answer("اول از «نسخه‌ها» یک آهنگ اضافه کنید.", show_alert=True)
        return
    ex("UPDATE posts SET button_on=? WHERE id=?", 0 if p["button_on"] else 1, pid)
    await refresh_post(bot, pid)
    text, markup = post_panel(pid)
    await show(cb, text, markup)


@admin.callback_query(F.data.startswith("pv:"))
async def pv_panel(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    pid = int(cb.data[3:])
    songs = q("SELECT * FROM songs WHERE post_id=? ORDER BY pos,id", pid)
    rows = []
    for i, s in enumerate(songs, 1):
        rows.append([B(f"{i}. {s['label'] or 'بدون نام'} ({s['downloads']})", f"pvn:{s['id']}"),
                     B("🏷", f"pvl:{s['id']}", style="primary"), B("🗑", f"pvd:{s['id']}", style="danger")])
    rows.append([B("➕ افزودن نسخه", f"pva:{pid}", style="success")])
    rows.append([B("↩️ بازگشت", f"p:post:{pid}")])
    await show(cb, "🎧 <b>نسخه‌ها</b>\n(🏷 تغییر نام، 🗑 حذف)", kb(*rows))


@admin.callback_query(F.data.startswith("pvn:"))
async def pv_noop(cb: CallbackQuery):
    await cb.answer()


@admin.callback_query(F.data.startswith("pvl:"))
async def pv_label(cb: CallbackQuery, state: FSMContext):
    sid = int(cb.data[4:])
    pid = q1("SELECT post_id FROM songs WHERE id=?", sid)["post_id"]
    await state.set_state(EF.val)
    await state.set_data({"pid": pid, "field": f"label:{sid}"})
    await show(cb, "نام جدید نسخه را بنویسید («-» برای خالی کردن).", CANCEL_KB)


@admin.callback_query(F.data.startswith("pvd:"))
async def pv_delete(cb: CallbackQuery, bot: Bot, state: FSMContext):
    sid = int(cb.data[4:])
    r = q1("SELECT post_id FROM songs WHERE id=?", sid)
    if not r:
        await cb.answer()
        return
    pid = r["post_id"]
    ex("DELETE FROM songs WHERE id=?", sid)
    if q1("SELECT COUNT(*) c FROM songs WHERE post_id=?", pid)["c"] == 0:
        ex("UPDATE posts SET button_on=0 WHERE id=?", pid)
    await refresh_post(bot, pid)
    cb.data = f"pv:{pid}"
    await pv_panel(cb, state)


@admin.callback_query(F.data.startswith("pva:"))
async def pv_add(cb: CallbackQuery, state: FSMContext):
    await state.set_state(PV.file)
    await state.set_data({"pid": int(cb.data[4:])})
    await show(cb, "فایل آهنگ کامل را بفرستید.", CANCEL_KB)


@admin.message(PV.file)
async def pv_file(m: Message, state: FSMContext):
    info = file_info(m)
    if not info:
        await m.answer("فایل صوتی بفرستید.", reply_markup=CANCEL_KB)
        return
    await state.update_data(info=info)
    await state.set_state(PV.label)
    await m.answer("نام نسخه (اختیاری):", reply_markup=kb([B("⏭ بدون نام", "pvs:skip")], [B("✖ لغو", "x:cancel", style="danger")]))


async def pv_finish(target, state, bot, label):
    d = await state.get_data()
    pid = d["pid"]
    p = q1("SELECT * FROM posts WHERE id=?", pid)
    chat = target.message.chat.id if isinstance(target, CallbackQuery) else target.chat.id
    fid, ft = await retag(bot, d["info"], p["title"], p["artist"], None, STORAGE_CHAT or chat)
    pos = q1("SELECT COALESCE(MAX(pos),-1)+1 c FROM songs WHERE post_id=?", pid)["c"]
    ex("INSERT INTO songs(post_id,pos,label,file_id,file_type) VALUES(?,?,?,?,?)", pid, pos, label, fid, ft)
    ex("UPDATE posts SET button_on=1 WHERE id=?", pid)
    await state.clear()
    await refresh_post(bot, pid)
    text, markup = post_panel(pid)
    await bot.send_message(chat, "✅ نسخه اضافه شد.\n\n" + text, reply_markup=markup)


@admin.callback_query(PV.label, F.data == "pvs:skip")
async def pv_skip(cb: CallbackQuery, state: FSMContext, bot: Bot):
    await cb.answer()
    await pv_finish(cb, state, bot, "")


@admin.message(PV.label, F.text)
async def pv_label_text(m: Message, state: FSMContext, bot: Bot):
    await pv_finish(m, state, bot, m.text.strip()[:30])


@admin.callback_query(F.data.startswith("pd:"))
async def pd_confirm(cb: CallbackQuery):
    pid = int(cb.data[3:])
    await show(cb, "مطمئنید؟ پست از کانال هم حذف می‌شود.", kb(
        [B("🔴 بله، حذف کن", f"pdc:{pid}", style="danger"), B("انصراف", f"p:post:{pid}")]))


@admin.callback_query(F.data.startswith("pdc:"))
async def pd_do(cb: CallbackQuery, bot: Bot):
    pid = int(cb.data[4:])
    for r in q("SELECT * FROM post_msgs WHERE post_id=?", pid):
        try:
            await bot.delete_message(r["chat_id"], r["message_id"])
        except Exception:
            pass
    ex("DELETE FROM post_msgs WHERE post_id=?", pid)
    ex("UPDATE posts SET status='deleted' WHERE id=?", pid)
    await show(cb, "🗑 پست حذف شد.", kb([B("↩️ لیست", "p:list:0")], HOME_ROW))


# ───────────────────────────── آمار ─────────────────────────────

@admin.callback_query(F.data == "p:stats")
async def p_stats(cb: CallbackQuery):
    users = q1("SELECT COUNT(*) c FROM users")["c"]
    week = q1("SELECT COUNT(*) c FROM users WHERE joined_at>=?", day_start(6))["c"]
    today = q1("SELECT COUNT(*) c FROM users WHERE joined_at>=?", day_start())["c"]
    dl_t = q1("SELECT COUNT(*) c FROM downloads WHERE ts>=?", day_start())["c"]
    dl_w = q1("SELECT COUNT(*) c FROM downloads WHERE ts>=?", day_start(6))["c"]
    dl_all = q1("SELECT COUNT(*) c FROM downloads")["c"]
    top = q("SELECT p.title, p.code, s.label, s.downloads FROM songs s JOIN posts p ON p.id=s.post_id "
            "WHERE p.status!='deleted' ORDER BY s.downloads DESC LIMIT 10")
    lines = [f"{i}. {esc(t['title'])}" + (f" ({esc(t['label'])})" if t["label"] else "") + f" — {t['downloads']}"
             for i, t in enumerate(top, 1)]
    text = (f"📊 <b>آمار</b>\n━━━━━━━━━━━━━━\n"
            f"کاربران: {users} | امروز: +{today} | هفته: +{week}\n"
            f"دانلود: امروز {dl_t} | هفته {dl_w} | کل {dl_all}\n\n"
            f"🔥 <b>پرطرفدارترین‌ها</b>\n" + ("\n".join(lines) if lines else "—"))
    await show(cb, text, kb([B("📢 آمار عضویت اجباری", "p:fj", style="primary")], HOME_ROW))


# ───────────────────────────── پیام پیوست ─────────────────────────────

MODE_NAMES = {"all": "همه با هم", "rotate": "چرخشی", "random": "شانسی"}


def attach_panel():
    items = q("SELECT * FROM attach ORDER BY id")
    ttl = int(gs("attach_ttl", "0"))
    text = (f"📎 <b>پیام پیوست</b> (بعد از هر دانلود)\n"
            f"حالت ارسال: {MODE_NAMES[gs('attach_mode', 'all')]}\n"
            f"حذف خودکار: {'خاموش' if not ttl else f'{ttl // 60} دقیقه'}\n━━━━━━━━━━━━━━\n")
    rows = []
    for i, it in enumerate(items, 1):
        plain = re.sub(r"<[^>]+>", "", it["html"] or "")[:25]
        rows.append([B(f"{i}. {'🟢' if it['enabled'] else '🔴'} {html.unescape(plain)}", f"at:{it['id']}", style="primary")])
    if not items:
        text += "هنوز پیامی نیست."
    rows.append([B("➕ افزودن", "at:new", style="success")])
    rows.append([B(("✅ " if gs("attach_mode") == m else "") + n, f"atm:{m}") for m, n in MODE_NAMES.items()])
    rows.append([B(("✅ " if ttl == s else "") + t, f"atx:{s}") for s, t in
                 [(0, "بدون حذف"), (60, "۱ دقیقه"), (300, "۵ دقیقه"), (1800, "۳۰ دقیقه")]])
    rows.append(HOME_ROW)
    return text, kb(*rows)


@admin.callback_query(F.data == "p:attach")
async def p_attach(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    t, m = attach_panel()
    await show(cb, t, m)


@admin.callback_query(F.data.startswith("atm:"))
async def at_mode(cb: CallbackQuery):
    ss("attach_mode", cb.data[4:])
    t, m = attach_panel()
    await show(cb, t, m)


@admin.callback_query(F.data.startswith("atx:"))
async def at_ttl(cb: CallbackQuery):
    ss("attach_ttl", cb.data[4:])
    t, m = attach_panel()
    await show(cb, t, m)


@admin.callback_query(F.data == "at:new")
async def at_new(cb: CallbackQuery, state: FSMContext):
    await state.set_state(AT.content)
    await state.set_data({})
    await show(cb, "متن پیام را بفرستید (می‌تواند لینک، بولد، ایمونجی داشته باشد؛ با عکس هم می‌شود).", CANCEL_KB)


@admin.message(AT.content)
async def at_content(m: Message, state: FSMContext):
    if m.photo:
        await state.update_data(html=m.html_text or "", photo=m.photo[-1].file_id)
    elif m.text:
        await state.update_data(html=m.html_text, photo=None)
    else:
        await m.answer("متن یا عکس همراه متن بفرستید.", reply_markup=CANCEL_KB)
        return
    await state.set_state(AT.button)
    await m.answer("دکمه می‌خواهید؟ به این شکل بفرستید:\n<code>متن دکمه | لینک</code>\nیا رد کنید.",
                   reply_markup=kb([B("⏭ بدون دکمه", "atb:skip")], [B("✖ لغو", "x:cancel", style="danger")]))


async def at_save(target, state, btn_text, btn_url):
    d = await state.get_data()
    if d.get("edit_id"):
        ex("UPDATE attach SET html=?, photo_id=?, btn_text=?, btn_url=? WHERE id=?",
           d["html"], d.get("photo"), btn_text, btn_url, d["edit_id"])
    else:
        ex("INSERT INTO attach(html,photo_id,btn_text,btn_url) VALUES(?,?,?,?)", d["html"], d.get("photo"), btn_text, btn_url)
    await state.clear()
    t, m = attach_panel()
    await show(target, "✅ ذخیره شد.\n\n" + t, m)


@admin.callback_query(AT.button, F.data == "atb:skip")
async def at_btn_skip(cb: CallbackQuery, state: FSMContext):
    await at_save(cb, state, None, None)


@admin.message(AT.button, F.text)
async def at_btn(m: Message, state: FSMContext):
    if "|" not in m.text:
        await m.answer("فرمت: <code>متن دکمه | لینک</code>", reply_markup=CANCEL_KB)
        return
    t, u = [x.strip() for x in m.text.split("|", 1)]
    if not re.match(r"^(https?://|tg://)", u):
        await m.answer("لینک باید با https:// یا tg:// شروع شود.", reply_markup=CANCEL_KB)
        return
    await at_save(m, state, t, u)


@admin.callback_query(F.data.regexp(r"^at:\d+$"))
async def at_detail(cb: CallbackQuery):
    iid = int(cb.data[3:])
    it = q1("SELECT * FROM attach WHERE id=?", iid)
    if not it:
        await cb.answer()
        return
    await show(cb, f"📎 پیام #{iid}: {'🟢 روشن' if it['enabled'] else '🔴 خاموش'}", kb(
        [B("🔄 روشن/خاموش", f"att:{iid}", style="primary"), B("✏️ ویرایش", f"ate:{iid}", style="primary")],
        [B("👁 پیش‌نمایش", f"atp:{iid}"), B("🗑 حذف", f"atd:{iid}", style="danger")],
        [B("↩️ بازگشت", "p:attach")]))


@admin.callback_query(F.data.startswith("att:"))
async def at_toggle(cb: CallbackQuery):
    iid = int(cb.data[4:])
    ex("UPDATE attach SET enabled=1-enabled WHERE id=?", iid)
    cb.data = f"at:{iid}"
    await at_detail(cb)


@admin.callback_query(F.data.startswith("atd:"))
async def at_delete(cb: CallbackQuery):
    ex("DELETE FROM attach WHERE id=?", int(cb.data[4:]))
    t, m = attach_panel()
    await show(cb, t, m)


@admin.callback_query(F.data.startswith("atp:"))
async def at_preview(cb: CallbackQuery, bot: Bot):
    it = q1("SELECT * FROM attach WHERE id=?", int(cb.data[4:]))
    await cb.answer()
    if it:
        await send_attach_item(bot, cb.message.chat.id, it)


@admin.callback_query(F.data.startswith("ate:"))
async def at_edit(cb: CallbackQuery, state: FSMContext):
    await state.set_state(AT.content)
    await state.set_data({"edit_id": int(cb.data[4:])})
    await show(cb, "متن جدید را بفرستید.", CANCEL_KB)


# ───────────────────────────── پیام همگانی ─────────────────────────────

@admin.callback_query(F.data == "p:bc")
async def p_bc(cb: CallbackQuery, state: FSMContext):
    await state.set_state(BC.msg)
    n = q1("SELECT COUNT(*) c FROM users WHERE active=1 AND blocked=0")["c"]
    await show(cb, f"📣 پیامی که می‌خواهید برای {n} کاربر بفرستید را بفرستید (متن، عکس، ویدیو و ...).", CANCEL_KB)


@admin.message(BC.msg)
async def bc_msg(m: Message, state: FSMContext, bot: Bot):
    await state.update_data(src_chat=m.chat.id, src_msg=m.message_id)
    await state.set_state(None)
    await bot.copy_message(m.chat.id, m.chat.id, m.message_id)
    await m.answer("👆 پیش‌نمایش. ارسال کنم؟", reply_markup=kb(
        [B("🟢 ارسال به همه", "bc:go", style="success"), B("✖ لغو", "x:cancel", style="danger")]))


async def run_broadcast(bot, admin_chat, src_chat, src_msg):
    users = [r["id"] for r in q("SELECT id FROM users WHERE active=1 AND blocked=0")]
    ok = fail = 0
    for uid in users:
        for attempt in range(2):
            try:
                await bot.copy_message(uid, src_chat, src_msg)
                ok += 1
                break
            except TelegramRetryAfter as e:
                await asyncio.sleep(e.retry_after + 1)
            except TelegramForbiddenError:
                ex("UPDATE users SET active=0 WHERE id=?", uid)
                fail += 1
                break
            except Exception:
                fail += 1
                break
        await asyncio.sleep(0.05)
    await bot.send_message(admin_chat, f"📣 <b>پایان ارسال همگانی</b>\n✅ موفق: {ok}\n❌ ناموفق: {fail}")


@admin.callback_query(F.data == "bc:go")
async def bc_go(cb: CallbackQuery, state: FSMContext, bot: Bot):
    d = await state.get_data()
    if not d.get("src_msg"):
        await cb.answer("پیامی پیدا نشد.", show_alert=True)
        return
    await state.clear()
    await show(cb, "⏳ ارسال شروع شد. بعد از پایان گزارش می‌دهم.")
    asyncio.create_task(run_broadcast(bot, d["src_chat"], d["src_chat"], d["src_msg"]))


# ───────────────────────────── عضویت اجباری ─────────────────────────────

def fj_stats(chid):
    def c(since, kinds=("join", "confirm")):
        return q1("SELECT COUNT(*) c FROM force_events WHERE ch_id=? AND ts>=? AND kind IN (?,?)",
                  chid, since, *kinds)["c"]
    return c(0), c(day_start()), c(day_start(6))


def fj_panel():
    chans = q("SELECT * FROM force_channels ORDER BY sort,id")
    text = f"📢 <b>عضویت اجباری</b> — {'🟢 روشن' if gs('force_on', '1') == '1' else '🔴 خاموش'}\n━━━━━━━━━━━━━━\n"
    rows = []
    for i, ch in enumerate(chans, 1):
        tot, today, week = fj_stats(ch["id"])
        kind = "🟢 چک‌دار" if ch["checked"] else "🟡 بدون چک"
        label = "عضو از طریق ربات" if ch["checked"] else "تأیید «عضو شدم»"
        text += (f"{i}. {esc(ch['title'])} {'' if ch['enabled'] else '(خاموش)'}\n"
                 f"   {kind} | {label}: {tot} | امروز: {today} | هفته: {week}\n")
        rows.append([B(f"{i}. {ch['title'][:25]}", f"fj:{ch['id']}", style="primary")])
    rows.append([B("➕ افزودن کانال", "fj:add", style="success")])
    rows.append([B("🔄 روشن/خاموش کل عضویت اجباری", "set:fj")])
    rows.append(HOME_ROW)
    return text, kb(*rows)


@admin.callback_query(F.data == "p:fj")
async def p_fj(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    t, m = fj_panel()
    await show(cb, t, m)


@admin.callback_query(F.data.regexp(r"^fj:\d+$"))
async def fj_detail(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    ch = q1("SELECT * FROM force_channels WHERE id=?", int(cb.data[3:]))
    if not ch:
        await cb.answer()
        return
    text = (f"📢 <b>{esc(ch['title'])}</b>\n{'🟢 چک‌دار (ربات ادمین است)' if ch['checked'] else '🟡 بدون چک (ربات ادمین نیست)'}\n"
            f"وضعیت: {'روشن' if ch['enabled'] else 'خاموش'}\nلینک: {esc(ch['link'] or '—')}")
    rows = [[B("🔄 روشن/خاموش", f"fjt:{ch['id']}", style="primary"), B("🔁 بررسی دوباره", f"fjc:{ch['id']}", style="primary")],
            [B("✏️ عنوان", f"fje:{ch['id']}:title"), B("🔗 لینک", f"fje:{ch['id']}:link")],
            [B("⬆️ بالاتر", f"fjm:{ch['id']}:-1"), B("⬇️ پایین‌تر", f"fjm:{ch['id']}:1")]]
    if not ch["is_main"]:
        rows.append([B("🗑 حذف", f"fjd:{ch['id']}", style="danger")])
    rows.append([B("↩️ بازگشت", "p:fj")])
    await show(cb, text, kb(*rows))


@admin.callback_query(F.data.startswith("fjt:"))
async def fj_toggle(cb: CallbackQuery, state: FSMContext):
    ex("UPDATE force_channels SET enabled=1-enabled WHERE id=?", int(cb.data[4:]))
    cb.data = f"fj:{cb.data[4:]}"
    await fj_detail(cb, state)


@admin.callback_query(F.data.startswith("fjc:"))
async def fj_recheck(cb: CallbackQuery, state: FSMContext, bot: Bot):
    ch = q1("SELECT * FROM force_channels WHERE id=?", int(cb.data[4:]))
    ok = bool(ch["chat_id"]) and await bot_is_admin(bot, ch["chat_id"])
    ex("UPDATE force_channels SET checked=? WHERE id=?", 1 if ok else 0, ch["id"])
    cb.data = f"fj:{ch['id']}"
    await fj_detail(cb, state)


@admin.callback_query(F.data.startswith("fjd:"))
async def fj_delete(cb: CallbackQuery):
    ex("DELETE FROM force_channels WHERE id=? AND is_main=0", int(cb.data[4:]))
    t, m = fj_panel()
    await show(cb, t, m)


@admin.callback_query(F.data.startswith("fjm:"))
async def fj_move(cb: CallbackQuery, state: FSMContext):
    _, cid, d = cb.data.split(":")
    chans = [r["id"] for r in q("SELECT id FROM force_channels ORDER BY sort,id")]
    i = chans.index(int(cid))
    j = i + int(d)
    if 0 <= j < len(chans):
        chans[i], chans[j] = chans[j], chans[i]
        for n, chid in enumerate(chans):
            ex("UPDATE force_channels SET sort=? WHERE id=?", n, chid)
    cb.data = f"fj:{cid}"
    await fj_detail(cb, state)


@admin.callback_query(F.data.startswith("fje:"))
async def fj_edit(cb: CallbackQuery, state: FSMContext):
    _, cid, field = cb.data.split(":")
    await state.set_state(FJ.edit)
    await state.set_data({"cid": int(cid), "field": field})
    await show(cb, "مقدار جدید را بفرستید." + ("\n(لینک باید با https:// شروع شود)" if field == "link" else ""), CANCEL_KB)


@admin.message(FJ.edit, F.text)
async def fj_edit_val(m: Message, state: FSMContext):
    d = await state.get_data()
    v = m.text.strip()
    if d["field"] == "link" and not v.startswith("http"):
        await m.answer("لینک معتبر نیست.", reply_markup=CANCEL_KB)
        return
    ex(f"UPDATE force_channels SET {d['field']}=? WHERE id=?", v[:200], d["cid"])
    await state.clear()
    t, mk = fj_panel()
    await m.answer("✅ ذخیره شد.\n\n" + t, reply_markup=mk)


@admin.callback_query(F.data == "fj:add")
async def fj_add(cb: CallbackQuery, state: FSMContext):
    await state.set_state(FJ.add)
    await state.set_data({})
    await show(cb, "یوزرنیم یا لینک کانال را بفرستید:\n<code>@channel</code> یا <code>t.me/channel</code> یا لینک دعوت <code>t.me/+xxxx</code>\n"
                   "یا آیدی عددی (برای کانال خصوصی).", CANCEL_KB)


async def fj_finish(target, state, bot):
    d = await state.get_data()
    chat_id = d.get("chat_id")
    checked = 1 if (chat_id and await bot_is_admin(bot, chat_id)) else 0
    n = q1("SELECT COALESCE(MAX(sort),0)+1 c FROM force_channels")["c"]
    ex("INSERT INTO force_channels(chat_id,title,link,enabled,checked,sort) VALUES(?,?,?,?,?,?)",
       chat_id, d["title"], d["link"], 1, checked, n)
    await state.clear()
    status = "✅ ربات ادمین است: عضویت چک می‌شود (🟢)" if checked else "⚠️ ربات ادمین نیست: فقط نمایش داده می‌شود (🟡)"
    t, mk = fj_panel()
    await show(target, f"کانال اضافه شد.\n{status}\n\n{t}", mk)


@admin.message(FJ.add, F.text)
async def fj_add_val(m: Message, state: FSMContext, bot: Bot):
    t = m.text.strip()
    if re.search(r"t\.me/(\+|joinchat/)", t):
        await state.update_data(chat_id=None, link=t if t.startswith("http") else "https://" + t)
        await state.set_state(FJ.title)
        await m.answer("عنوان دکمه‌ی این کانال را بنویسید.", reply_markup=CANCEL_KB)
        return
    chat = None
    try:
        um = re.search(r"(?:t\.me/|telegram\.me/|@)([A-Za-z][A-Za-z0-9_]{3,})", t)
        if um:
            chat = await bot.get_chat("@" + um.group(1))
        elif t.lstrip("-").isdigit():
            chat = await bot.get_chat(int(t))
    except Exception:
        chat = None
    if not chat:
        await m.answer("کانال پیدا نشد ❌ یوزرنیم، لینک عمومی یا لینک دعوت را بفرستید.", reply_markup=CANCEL_KB)
        return
    link = f"https://t.me/{chat.username}" if chat.username else None
    await state.update_data(chat_id=chat.id, title=chat.title or "کانال", link=link)
    if not link:
        await state.set_state(FJ.link)
        await m.answer("کانال یوزرنیم ندارد. لینک دعوت را بفرستید.", reply_markup=CANCEL_KB)
        return
    await fj_finish(m, state, bot)


@admin.message(FJ.title, F.text)
async def fj_title(m: Message, state: FSMContext, bot: Bot):
    await state.update_data(title=m.text.strip()[:60])
    await fj_finish(m, state, bot)


@admin.message(FJ.link, F.text)
async def fj_link(m: Message, state: FSMContext, bot: Bot):
    if not m.text.startswith("http"):
        await m.answer("لینک معتبر نیست.", reply_markup=CANCEL_KB)
        return
    await state.update_data(link=m.text.strip())
    await fj_finish(m, state, bot)


# ───────────────────────────── کانال‌های مدیریت‌شده ─────────────────────────────

async def mc_panel(bot):
    rows_ = q("SELECT * FROM managed ORDER BY added_at")
    text = "📡 <b>کانال‌های مدیریت‌شده</b>\n━━━━━━━━━━━━━━\n"
    btns = []
    for i, r in enumerate(rows_, 1):
        try:
            cnt = await bot.get_chat_member_count(r["chat_id"])
        except Exception:
            cnt = "؟"
        main = " (اصلی)" if r["chat_id"] == G["main_id"] else ""
        text += f"{i}. {esc(r['title'])}{main} — {'🟢 ارسال آهنگ' if r['send_songs'] else '🔴 بدون ارسال'} | اعضا: {cnt}\n"
        row = [B(f"🔄 {r['title'][:18]}", f"mc:t:{r['chat_id']}", style="primary")]
        if r["chat_id"] != G["main_id"]:
            row.append(B("🗑", f"mc:d:{r['chat_id']}", style="danger"))
        btns.append(row)
    btns.append([B("➕ افزودن کانال", "mc:add", style="success")])
    btns.append(HOME_ROW)
    text += "\nبرای افزودن، ربات را در کانال ادمین کنید؛ خودش به شما خبر می‌دهد."
    return text, kb(*btns)


@admin.callback_query(F.data == "p:mc")
async def p_mc(cb: CallbackQuery, state: FSMContext, bot: Bot):
    await state.clear()
    t, m = await mc_panel(bot)
    await show(cb, t, m)


@admin.callback_query(F.data.startswith("mc:t:"))
async def mc_toggle(cb: CallbackQuery, bot: Bot):
    ex("UPDATE managed SET send_songs=1-send_songs WHERE chat_id=?", int(cb.data[5:]))
    t, m = await mc_panel(bot)
    await show(cb, t, m)


@admin.callback_query(F.data.startswith("mc:d:"))
async def mc_delete(cb: CallbackQuery, bot: Bot):
    ex("DELETE FROM managed WHERE chat_id=? AND chat_id!=?", int(cb.data[5:]), G["main_id"])
    t, m = await mc_panel(bot)
    await show(cb, t, m)


@admin.callback_query(F.data.startswith("mc:y:"))
async def mc_yes(cb: CallbackQuery, bot: Bot):
    cid = int(cb.data[5:])
    try:
        chat = await bot.get_chat(cid)
        title = chat.title or str(cid)
    except Exception:
        title = str(cid)
    ex("INSERT OR IGNORE INTO managed(chat_id,title,send_songs,added_at) VALUES(?,?,0,?)", cid, title, now_ts())
    await show(cb, f"✅ «{esc(title)}» به کانال‌های مدیریت‌شده اضافه شد (بدون ارسال آهنگ).",
               kb([B("📡 کانال‌های مدیریت‌شده", "p:mc")], HOME_ROW))


@admin.callback_query(F.data.startswith("mc:n:"))
async def mc_no(cb: CallbackQuery):
    await show(cb, "باشه، اضافه نشد.")


@admin.callback_query(F.data == "mc:add")
async def mc_add(cb: CallbackQuery, state: FSMContext):
    await state.set_state(MC.add)
    await show(cb, "یوزرنیم یا آیدی عددی کانال را بفرستید (ربات باید در آن ادمین باشد).", CANCEL_KB)


@admin.message(MC.add, F.text)
async def mc_add_val(m: Message, state: FSMContext, bot: Bot):
    t = m.text.strip()
    try:
        um = re.search(r"(?:t\.me/|@)([A-Za-z][A-Za-z0-9_]{3,})", t)
        chat = await bot.get_chat("@" + um.group(1)) if um else await bot.get_chat(int(t))
    except Exception:
        await m.answer("کانال پیدا نشد ❌", reply_markup=CANCEL_KB)
        return
    if not await bot_is_admin(bot, chat.id):
        await m.answer("ربات در این کانال ادمین نیست. اول ادمینش کنید.", reply_markup=CANCEL_KB)
        return
    ex("INSERT OR IGNORE INTO managed(chat_id,title,send_songs,added_at) VALUES(?,?,0,?)",
       chat.id, chat.title or str(chat.id), now_ts())
    await state.clear()
    tt, mk = await mc_panel(bot)
    await m.answer("✅ اضافه شد.\n\n" + tt, reply_markup=mk)


# ───────────────────────────── بلاک ─────────────────────────────

@admin.callback_query(F.data.startswith("bk:"))
async def bk_ask(cb: CallbackQuery):
    uid = int(cb.data[3:])
    await cb.message.edit_reply_markup(reply_markup=kb(
        [B("🔴 بله، بلاک کن", f"bkc:{uid}", style="danger"), B("انصراف", f"bkx:{uid}")]))
    await cb.answer("مطمئنید؟")


@admin.callback_query(F.data.startswith("bkx:"))
async def bk_cancel(cb: CallbackQuery):
    uid = int(cb.data[4:])
    await cb.message.edit_reply_markup(reply_markup=block_kb(uid))
    await cb.answer()


@admin.callback_query(F.data.startswith("bkc:"))
async def bk_reason(cb: CallbackQuery):
    uid = int(cb.data[4:])
    rows = [[B(r, f"bkr:{uid}:{i}", style="danger") for i, r in enumerate(REASONS[:2])],
            [B(r, f"bkr:{uid}:{i + 2}", style="danger") for i, r in enumerate(REASONS[2:])],
            [B("انصراف", f"bkx:{uid}")]]
    await cb.message.edit_reply_markup(reply_markup=kb(*rows))
    await cb.answer("دلیل بلاک؟")


@admin.callback_query(F.data.startswith("bkr:"))
async def bk_do(cb: CallbackQuery, bot: Bot):
    _, uid, idx = cb.data.split(":")
    uid = int(uid)
    await do_block(bot, uid, REASONS[int(idx)])
    try:
        await cb.message.edit_reply_markup(reply_markup=block_kb(uid))
    except Exception:
        pass
    await cb.answer(f"⛔ بلاک شد ({REASONS[int(idx)]})", show_alert=True)


@admin.callback_query(F.data.startswith("ub:"))
async def ub_do(cb: CallbackQuery, bot: Bot, state: FSMContext):
    uid = int(cb.data[3:])
    await do_unblock(bot, uid)
    in_panel = bool(cb.message.text and "بلاک‌لیست" in cb.message.text.split("\n")[0])
    if in_panel:
        await p_bl(cb, state)
        return
    try:
        await cb.message.edit_reply_markup(reply_markup=block_kb(uid))
    except Exception:
        pass
    await cb.answer("🟢 آنبلاک شد", show_alert=True)


@admin.callback_query(F.data == "p:bl")
async def p_bl(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    rows_ = q("SELECT * FROM users WHERE blocked=1 ORDER BY blocked_at DESC LIMIT 25")
    text = "🚫 <b>بلاک‌لیست</b>\n━━━━━━━━━━━━━━\n"
    btns = []
    for r in rows_:
        text += f"• {esc(r['first_name'] or '')} | <code>{r['id']}</code> | {esc(r['block_reason'] or '')}\n"
        btns.append([B(f"🟢 آنبلاک {r['id']}", f"ub:{r['id']}", style="success")])
    if not rows_:
        text += "خالی است."
    btns.append([B("➕ بلاک با آیدی عددی", "bl:add", style="danger")])
    btns.append(HOME_ROW)
    await show(cb, text, kb(*btns))


@admin.callback_query(F.data == "bl:add")
async def bl_add(cb: CallbackQuery, state: FSMContext):
    await state.set_state(BL.uid)
    await show(cb, "آیدی عددی کاربر را بفرستید.", CANCEL_KB)


@admin.message(BL.uid, F.text)
async def bl_uid(m: Message, state: FSMContext):
    t = m.text.strip().translate(FA_DIGITS)
    if not t.isdigit():
        await m.answer("فقط عدد بفرستید.", reply_markup=CANCEL_KB)
        return
    await state.clear()
    uid = int(t)
    rows = [[B(r, f"bkr:{uid}:{i}", style="danger") for i, r in enumerate(REASONS[:2])],
            [B(r, f"bkr:{uid}:{i + 2}", style="danger") for i, r in enumerate(REASONS[2:])],
            [B("انصراف", "p:home")]]
    await m.answer(f"مطمئنید که <code>{uid}</code> بلاک شود؟ دلیل را انتخاب کنید:", reply_markup=kb(*rows))


# ───────────────────────────── تنظیمات ─────────────────────────────

def set_panel():
    rot = int(gs("rotate_every", "2"))
    sp = int(gs("spam_limit", "8"))
    text = (f"⚙️ <b>تنظیمات</b>\n━━━━━━━━━━━━━━\n"
            f"عضویت اجباری: {'🟢 روشن' if gs('force_on', '1') == '1' else '🔴 خاموش'}\n"
            f"تغییر رنگ دکمه: هر {rot} پست\n"
            f"هشدار اسپم: {'خاموش' if sp <= 0 else f'بیش از {sp} دانلود در دقیقه'}\n"
            f"ذخیره/فوروارد آهنگ: {'🔴 بسته' if gs('protect', '0') == '1' else '🟢 آزاد'}\n"
            f"گروه لاگ ورود: <code>{join_log_chat() or 'تنظیم نشده'}</code>\n"
            f"گروه لاگ دانلود: <code>{dl_log_chat() or 'تنظیم نشده'}</code>\n"
            f"ادمین‌ها: {len(all_admin_ids())}")
    return text, kb(
        [B("🔄 عضویت اجباری", "set:fj", style="primary"), B("🔄 ذخیره/فوروارد", "set:prot", style="primary")],
        [B(("✅ " if rot == n else "") + f"رنگ هر {n}", f"set:rot:{n}") for n in (1, 2, 3, 4)],
        [B(("✅ " if sp == n else "") + (f"اسپم {n}" if n else "اسپم خاموش"), f"set:spam:{n}") for n in (5, 8, 15, 0)],
        [B("👥 ادمین‌ها", "set:adm", style="primary")],
        HOME_ROW)


@admin.callback_query(F.data == "p:set")
async def p_set(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    t, m = set_panel()
    await show(cb, t + "\n\nبرای تعیین گروه لاگ: ربات را در گروه بیاورید و در آن گروه "
                       "<code>/setjoinlog</code> یا <code>/setdllog</code> بفرستید.", m)


@admin.callback_query(F.data.startswith("set:"))
async def set_do(cb: CallbackQuery, state: FSMContext):
    parts = cb.data.split(":")
    k = parts[1]
    if k == "fj":
        ss("force_on", "0" if gs("force_on", "1") == "1" else "1")
    elif k == "prot":
        ss("protect", "0" if gs("protect", "0") == "1" else "1")
    elif k == "rot":
        ss("rotate_every", parts[2])
    elif k == "spam":
        ss("spam_limit", parts[2])
    elif k == "adm":
        await adm_panel(cb)
        return
    t, m = set_panel()
    await show(cb, t, m)


async def adm_panel(cb):
    text = "👥 <b>ادمین‌ها</b>\n"
    btns = []
    for a in sorted(all_admin_ids()):
        fixed = a in ENV_ADMINS
        text += f"• <code>{a}</code> {'(اصلی)' if fixed else ''}\n"
        if not fixed:
            btns.append([B(f"🗑 حذف {a}", f"adm:d:{a}", style="danger")])
    btns.append([B("➕ افزودن ادمین", "adm:add", style="success")])
    btns.append([B("↩️ بازگشت", "p:set")])
    await show(cb, text, kb(*btns))


@admin.callback_query(F.data.startswith("adm:d:"))
async def adm_del(cb: CallbackQuery):
    ex("DELETE FROM admins WHERE id=?", int(cb.data[6:]))
    await adm_panel(cb)


@admin.callback_query(F.data == "adm:add")
async def adm_add(cb: CallbackQuery, state: FSMContext):
    await state.set_state(ADM.add)
    await show(cb, "آیدی عددی ادمین جدید را بفرستید.", CANCEL_KB)


@admin.message(ADM.add, F.text)
async def adm_add_val(m: Message, state: FSMContext, bot: Bot):
    t = m.text.strip().translate(FA_DIGITS)
    if not t.isdigit():
        await m.answer("فقط عدد بفرستید.", reply_markup=CANCEL_KB)
        return
    ex("INSERT OR IGNORE INTO admins(id) VALUES(?)", int(t))
    await state.clear()
    await setup_commands(bot)
    await m.answer("✅ ادمین اضافه شد.", reply_markup=kb([B("👥 ادمین‌ها", "set:adm")], HOME_ROW))


@admin.message(Command("setjoinlog"))
async def set_join_log(m: Message):
    ss("join_log", m.chat.id)
    await m.answer("✅ این گروه به‌عنوان «لاگ ورود و ترک» تنظیم شد.")


@admin.message(Command("setdllog"))
async def set_dl_log(m: Message):
    ss("dl_log", m.chat.id)
    await m.answer("✅ این گروه به‌عنوان «لاگ دانلود» تنظیم شد.")


# ───────────────────────────── راه‌اندازی ─────────────────────────────

async def setup_commands(bot):
    try:
        await bot.set_my_commands([BotCommand(command="channel", description="ورود به کانال")],
                                  scope=BotCommandScopeDefault())
        for aid in all_admin_ids():
            await bot.set_my_commands(
                [BotCommand(command="panel", description="پنل مدیریت"),
                 BotCommand(command="channel", description="ورود به کانال")],
                scope=BotCommandScopeChat(chat_id=aid))
    except Exception as e:
        log.warning("set commands failed: %s", e)


async def main():
    if not TOKEN or not MAIN_CHANNEL or not ENV_ADMINS:
        raise SystemExit("BOT_TOKEN ،MAIN_CHANNEL و ADMINS را در فایل .env تنظیم کنید.")
    bot = Bot(TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    me = await bot.get_me()
    G["bot_id"], G["bot_username"] = me.id, me.username
    chat = await bot.get_chat(MAIN_CHANNEL)
    G["main_id"], G["main_title"] = chat.id, chat.title or "Rudig Sounds"
    global CHANNEL_LINK
    if not CHANNEL_LINK:
        CHANNEL_LINK = f"https://t.me/{chat.username}" if chat.username else (chat.invite_link or "")
    if not CHANNEL_LINK:
        raise SystemExit("CHANNEL_LINK را در .env بنویسید (کانال یوزرنیم عمومی ندارد).")
    if not q1("SELECT 1 FROM force_channels WHERE is_main=1"):
        ex("INSERT INTO force_channels(chat_id,title,link,enabled,checked,is_main,sort) VALUES(?,?,?,?,?,?,?)",
           G["main_id"], G["main_title"], CHANNEL_LINK, 1, 1 if await bot_is_admin(bot, G["main_id"]) else 0, 1, 0)
    ex("INSERT OR IGNORE INTO managed(chat_id,title,send_songs,added_at) VALUES(?,?,1,?)",
       G["main_id"], G["main_title"], now_ts())
    if not await bot_is_admin(bot, G["main_id"]):
        log.warning("ربات در کانال اصلی ادمین نیست؛ انتشار پست و لاگ ترک کانال کار نمی‌کند.")

    dp = Dispatcher(storage=MemoryStorage())
    dp.message.outer_middleware(BlockMW())
    dp.callback_query.outer_middleware(BlockMW())
    dp.include_router(admin)
    dp.include_router(public)
    await setup_commands(bot)
    asyncio.create_task(scheduler(bot))
    await bot.delete_webhook(drop_pending_updates=False)
    log.info("Bot @%s started. main channel: %s", me.username, G["main_title"])
    await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())


if __name__ == "__main__":
    asyncio.run(main())
