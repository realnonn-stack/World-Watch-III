# -*- coding: utf-8 -*-
"""
=============================================================================
 WORLD WATCH  —  ศูนย์เฝ้าระวังสถานการณ์โลก → ผลกระทบต่อไทย
=============================================================================
 เฝ้าดู 3 อย่างพร้อมกันในหน้าเดียว
   1) จุดร้อนทางภูมิรัฐศาสตร์ที่อาจลุกลามเป็นสงครามใหญ่
   2) การเคลื่อนไหวผิดปกติของทองคำ / น้ำมัน / ค่าเงิน / ตลาดหุ้น
   3) แปลว่าอะไรกับประเทศไทย (ราคาทองบาท, ค่าครองชีพ, กำลังซื้อลูกค้าต่างชาติ)

 กฎเหล็กของไฟล์นี้
   - ไม่มีตัวเลข hard-code ไม่มีการเดา ไม่มีการ estimate เงียบ ๆ
   - ทุกตัวเลขดึงสดจากแหล่งจริง แล้วคำนวณจริงด้วยสูตรที่เขียนกำกับไว้
   - ดึงไม่ได้ = บอกว่าดึงไม่ได้ + โชว์ error ไม่แต่งข้อมูลมาแทน
   - ทุกข่าวมีลิงก์ต้นทาง + เวลา + ระดับความน่าเชื่อถือของแหล่ง
   - ข่าวที่ "น่าสนใจแต่ยังเชื่อไม่ได้" ถูกแยกกล่องและบอกเหตุผลว่าทำไม

 ใช้เฉพาะ API ฟรี ไม่ต้องใช้ key ไม่มีค่าใช้จ่ายรายเดือน

 วิธีรัน
     pip install flask
     python app.py
     เปิด http://127.0.0.1:5000
=============================================================================
"""

from __future__ import annotations

import csv
import gzip
import json
import math
import os
import re
import statistics
import sys
import threading
import time
import traceback
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from urllib.error import HTTPError, URLError
from urllib.parse import quote
from urllib.request import Request, urlopen
from xml.etree import ElementTree as ET

from flask import Flask, jsonify, render_template_string, request

# =============================================================================
# 1. ค่าคงที่ / การตั้งค่า
# =============================================================================

APP_TITLE_TH = "ศูนย์เฝ้าระวังสถานการณ์โลก"
APP_TITLE_EN = "World Watch"

TH_TZ = timezone(timedelta(hours=7))          # ไทยไม่มี DST ใช้ offset คงที่ปลอดภัยสุด
CACHE_TTL_SEC = 600                            # 10 นาที — กันยิงแหล่งข้อมูลถี่เกินไป
HTTP_TIMEOUT = 12
MAX_WORKERS = 8
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) WorldWatch/1.0"

# ราคาอสังหาฯ ตั้งต้นที่ใช้คำนวณกำลังซื้อลูกค้าต่างชาติ (ปรับได้ที่ ?property=)
DEFAULT_PROPERTY_THB = 10_000_000

# ค่าคงที่สำหรับแปลงทองคำโลก -> ทองคำแท่งไทย
GRAMS_PER_TROY_OZ = 31.1035     # 1 ทรอยออนซ์ = 31.1035 กรัม
GRAMS_PER_BAHT_GOLD = 15.244    # ทอง 1 บาท (ไทย) = 15.244 กรัม
THAI_GOLD_PURITY = 0.965        # ทองรูปพรรณ/แท่งไทย 96.5%

# ---- ระดับความน่าเชื่อถือของแหล่งข่าว -------------------------------------
TIERS = {
    "A": {
        "label_th": "ตรวจสอบได้ / องค์กรทางการ",
        "label_en": "Verified / official",
        "desc_th": "สำนักข่าวใหญ่ที่มีบรรณาธิการ หรือองค์กรระหว่างประเทศที่ประกาศเอง",
        "cls": "bg-emerald-500/15 text-emerald-300 border-emerald-500/40",
        "dot": "bg-emerald-400",
    },
    "B": {
        "label_th": "สื่อหลัก มีบรรณาธิการ",
        "label_en": "Major outlet",
        "desc_th": "เชื่อถือได้ระดับหนึ่ง แต่มีจุดยืน/มุมมองของประเทศตัวเอง",
        "cls": "bg-sky-500/15 text-sky-300 border-sky-500/40",
        "dot": "bg-sky-400",
    },
    "C": {
        "label_th": "ต้องตรวจสอบต้นทาง",
        "label_en": "Verify source",
        "desc_th": "ตัวรวมข่าว หรือสื่อเฉพาะทางที่มีผลประโยชน์ทับซ้อนกับราคาสินทรัพย์",
        "cls": "bg-amber-500/15 text-amber-300 border-amber-500/40",
        "dot": "bg-amber-400",
    },
    "D": {
        "label_th": "ระวังสูง — อ่านเอาท่าที ไม่ใช่เอาข้อเท็จจริง",
        "label_en": "High caution",
        "desc_th": "สื่อรัฐหรือสื่อที่มีประวัติเร้าอารมณ์ ใช้ดูว่าฝ่ายนั้นอยากให้คนเชื่ออะไร",
        "cls": "bg-rose-500/15 text-rose-300 border-rose-500/40",
        "dot": "bg-rose-400",
    },
}

# ---- แหล่งข่าว RSS ---------------------------------------------------------

def _gnews(query: str, hl: str = "en-US", gl: str = "US", ceid: str = "US:en") -> str:
    """สร้างลิงก์ RSS ของ Google News (รองรับคำค้นภาษาไทยด้วยการ encode ให้)"""
    return (f"https://news.google.com/rss/search?q={quote(query, safe='')}"
            f"&hl={hl}&gl={gl}&ceid={ceid}")


FEEDS = [
    {"name": "BBC World", "tier": "A", "home": "https://www.bbc.com/news/world",
     "url": "https://feeds.bbci.co.uk/news/world/rss.xml",
     "note_th": "สำนักข่าวอังกฤษ มีมาตรฐานตรวจสอบสูง"},
    {"name": "UN News", "tier": "A", "home": "https://news.un.org/en/",
     "url": "https://news.un.org/feed/subscribe/en/news/all/rss.xml",
     "note_th": "ประกาศจากองค์การสหประชาชาติโดยตรง"},
    {"name": "IAEA", "tier": "A", "home": "https://www.iaea.org/news",
     "url": "https://www.iaea.org/feeds/topnews",
     "note_th": "ทบวงการพลังงานปรมาณูฯ — ใช้เช็คประเด็นนิวเคลียร์"},
    {"name": "Al Jazeera", "tier": "B", "home": "https://www.aljazeera.com/",
     "url": "https://www.aljazeera.com/xml/rss/all.xml",
     "note_th": "แข็งเรื่องตะวันออกกลาง แต่มีมุมมองของกาตาร์"},
    {"name": "DW (เยอรมนี)", "tier": "B", "home": "https://www.dw.com/en/",
     "url": "https://rss.dw.com/rdf/rss-en-world",
     "note_th": "สื่อสาธารณะเยอรมนี มุมมองยุโรป/NATO"},
    {"name": "France 24", "tier": "B", "home": "https://www.france24.com/en/",
     "url": "https://www.france24.com/en/rss",
     "note_th": "สื่อสาธารณะฝรั่งเศส"},
    {"name": "CNBC World", "tier": "B", "home": "https://www.cnbc.com/world/",
     "url": "https://search.cnbc.com/rs/search/combinedcms/view.xml?partnerId=wrss01&id=100727362",
     "note_th": "มุมตลาดเงินตลาดทุน"},
    {"name": "Bangkok Post", "tier": "B", "home": "https://www.bangkokpost.com/",
     "url": "https://www.bangkokpost.com/rss/data/topstories.xml",
     "note_th": "ผลกระทบฝั่งไทยโดยตรง"},
    {"name": "Reuters (ผ่าน Google News)", "tier": "B", "home": "https://www.reuters.com/",
     "url": _gnews("site:reuters.com (war OR military OR sanctions OR missile OR oil OR gold) when:2d"),
     "note_th": "ต้นทางคือสำนักข่าว Reuters แต่ดึงผ่านตัวรวมข่าว ควรกดเข้าไปอ่านที่ต้นทางเสมอ"},
    {"name": "SCMP (ฮ่องกง)", "tier": "B", "home": "https://www.scmp.com/",
     "url": "https://www.scmp.com/rss/91/feed",
     "note_th": "แข็งเรื่องจีน/ไต้หวัน/เอเชีย แต่ตั้งอยู่ในฮ่องกงจึงมีข้อจำกัดในการรายงานบางเรื่อง"},
    {"name": "Google News (จุดร้อนทหาร)", "tier": "C", "home": "https://news.google.com/",
     "url": _gnews("(Taiwan OR Iran OR Ukraine OR \"South China Sea\") "
                   "(military OR missile OR strike OR mobilization) when:2d"),
     "note_th": "ตัวรวมข่าว — ต้องกดดูว่าต้นทางเป็นใครก่อนเชื่อ"},
    {"name": "Google News ไทย (เศรษฐกิจ/ชายแดน)", "tier": "C", "home": "https://news.google.com/",
     "url": _gnews("(ทองคำ OR ค่าเงินบาท OR ราคาน้ำมัน OR ชายแดน OR สงคราม) when:2d",
                   "th", "TH", "TH:th"),
     "note_th": "ข่าวไทยจากตัวรวมข่าว คุณภาพขึ้นกับต้นทางของแต่ละชิ้น ต้องกดดูก่อนเชื่อ"},
    {"name": "Investing.com (สินค้าโภคภัณฑ์)", "tier": "C", "home": "https://www.investing.com/commodities/",
     "url": "https://www.investing.com/rss/commodities.rss",
     "note_th": "บทวิเคราะห์ราคาทอง/น้ำมัน — เป็นความเห็นของนักวิเคราะห์ ไม่ใช่ข้อเท็จจริง และเว็บมีผลประโยชน์จากยอดเทรด"},
    {"name": "ZeroHedge", "tier": "D", "home": "https://www.zerohedge.com/",
     "url": "https://feeds.feedburner.com/zerohedge/feed",
     "note_th": "พาดหัวเร้าอารมณ์ ชอบเกินจริง แต่บางทีจับประเด็นก่อนสื่อใหญ่ — ห้ามเชื่อเดี่ยว ๆ"},
    {"name": "TASS (สื่อรัฐรัสเซีย)", "tier": "D", "home": "https://tass.com/",
     "url": "https://tass.com/rss/v2.xml",
     "note_th": "สื่อรัฐรัสเซีย ใช้ดูว่าเครมลินอยากสื่ออะไร ไม่ใช่ข้อเท็จจริงกลาง"},
    {"name": "Global Times (สื่อรัฐจีน)", "tier": "D", "home": "https://www.globaltimes.cn/",
     "url": _gnews("site:globaltimes.cn when:3d"),
     "note_th": "สื่อรัฐจีน ใช้ดูท่าทีปักกิ่งเรื่องไต้หวัน/ทะเลจีนใต้ ไม่ใช่ข้อเท็จจริงกลาง"},
]

# ---- คำที่บ่งชี้การยกระดับความรุนแรง (ยิ่งคะแนนสูง ยิ่งใกล้สงครามใหญ่) ----
ESCALATION_KEYWORDS = {
    # ระดับ 10 — สัญญาณสงครามใหญ่ของจริง
    "nuclear strike": 10, "nuclear weapon": 10, "nuclear test": 10, "tactical nuclear": 10,
    "article 5": 10, "declares war": 10, "declaration of war": 10, "state of war": 10,
    "general mobilization": 10, "nuclear alert": 10, "defcon": 10, "world war": 10,
    # ระดับ 7 — ปฏิบัติการทางทหารตรง ๆ
    "mobilization": 7, "missile strike": 7, "ballistic missile": 7, "hypersonic": 7,
    "airstrike": 7, "air strike": 7, "invasion": 7, "invade": 7, "blockade": 7,
    "strait of hormuz": 7, "taiwan strait": 7, "no-fly zone": 7, "icbm": 7,
    "carrier strike group": 7, "troops deployed": 7, "martial law": 7, "cyberattack": 7,
    # ระดับ 5 — ตึงเครียดแต่ยังไม่ปะทะเต็มรูปแบบ
    "sanctions": 5, "ceasefire collapse": 5, "border clash": 5, "drone attack": 5,
    "escalation": 5, "escalate": 5, "ultimatum": 5, "evacuate embassy": 5,
    "recalls ambassador": 5, "military exercise": 5, "war games": 5, "airspace violation": 5,
    "oil embargo": 5, "swift": 5, "shot down": 5, "seizes tanker": 5,
    # ระดับ 3 — ควรรู้ไว้
    "troop buildup": 3, "arms deal": 3, "defense budget": 3, "conscription": 3,
    "reservists": 3, "nato": 3, "war": 3,
}

# คำที่บ่งชี้การผ่อนคลาย — หักคะแนนออก
DEESCALATION_KEYWORDS = [
    "ceasefire agreement", "peace deal", "peace talks", "truce", "de-escalation",
    "withdraw troops", "sanctions lifted", "prisoner exchange", "agreement signed",
    "resume talks", "diplomatic breakthrough",
]

# คำกำกวมที่แปลว่า "ยังไม่ยืนยัน" — เจอแล้วต้องติดป้ายเตือน
HEDGE_WORDS = [
    "reportedly", "allegedly", "alleged", "claims", "claimed", "rumor", "rumour",
    "unconfirmed", "sources say", "according to sources", "reports suggest",
    "may have", "could be", "might be", "speculation", "unverified", "leaked",
    "อ้างว่า", "ลือ", "ยังไม่ยืนยัน", "คาดว่า",
]

# ---- โซนที่ต้องจับตา ------------------------------------------------------
THEATRES = [
    {"key": "ukraine", "emoji": "🇺🇦", "name_th": "ยูเครน – รัสเซีย – NATO", "name_en": "Ukraine / Russia / NATO",
     "why_th": "ถ้า NATO เข้าเป็นคู่สงครามโดยตรง = ยกระดับเป็นสงครามระหว่างมหาอำนาจทันที",
     "kw": ["ukraine", "russia", "russian", "kremlin", "putin", "zelensky", "nato", "kyiv",
            "moscow", "belarus", "kaliningrad", "baltic", "poland", "crimea", "donetsk"]},
    {"key": "mideast", "emoji": "🕌", "name_th": "ตะวันออกกลาง – อิหร่าน", "name_en": "Middle East / Iran",
     "why_th": "ช่องแคบฮอร์มุซคือทางผ่านน้ำมันโลก ปิดเมื่อไหร่ ราคาน้ำมันพุ่งทันที ไทยกระทบเต็ม ๆ",
     "kw": ["iran", "israel", "gaza", "hezbollah", "houthi", "red sea", "hormuz", "lebanon",
            "syria", "yemen", "idf", "tehran", "iraq", "netanyahu", "strait of hormuz"]},
    {"key": "taiwan", "emoji": "🇹🇼", "name_th": "ไต้หวัน – ทะเลจีนใต้", "name_en": "Taiwan / South China Sea",
     "why_th": "ใกล้ไทยที่สุด กระทบเส้นทางเดินเรือ ชิป และนักท่องเที่ยว/ผู้ซื้อจีนโดยตรง",
     "kw": ["taiwan", "china", "chinese", "beijing", "pla ", "south china sea", "philippines",
            "senkaku", "xi jinping", "taipei", "japan", "okinawa"]},
    {"key": "korea", "emoji": "🇰🇵", "name_th": "คาบสมุทรเกาหลี", "name_en": "Korean Peninsula",
     "why_th": "มีอาวุธนิวเคลียร์จริงและยิงทดสอบบ่อย เป็นตัวจุดชนวนที่คาดเดายาก",
     "kw": ["north korea", "pyongyang", "kim jong", "south korea", "seoul", "dprk"]},
    {"key": "southasia", "emoji": "🇮🇳", "name_th": "อินเดีย – ปากีสถาน", "name_en": "India / Pakistan",
     "why_th": "สองประเทศมีนิวเคลียร์ที่ติดชายแดนกันและปะทะกันเป็นระยะ",
     "kw": ["india", "pakistan", "kashmir", "new delhi", "islamabad"]},
    {"key": "thailand", "emoji": "🇹🇭", "name_th": "ไทยและเพื่อนบ้าน", "name_en": "Thailand & neighbours",
     "why_th": "กระทบเราตรง ๆ ทั้งชายแดน การท่องเที่ยว และความเชื่อมั่นผู้ซื้อต่างชาติ",
     "kw": ["thailand", "thai", "bangkok", "phuket", "cambodia", "myanmar", "mekong",
            "laos", "malaysia", "asean"]},
    {"key": "global", "emoji": "🌐", "name_th": "อื่น ๆ / เศรษฐกิจสงคราม", "name_en": "Other / war economy",
     "why_th": "มาตรการคว่ำบาตร ห่วงโซ่อุปทาน พลังงาน อาหาร ที่ไม่ผูกกับสมรภูมิเดียว",
     "kw": []},
]

# ---- สินทรัพย์ที่เฝ้าดู ----------------------------------------------------
# sources = ลำดับแหล่งที่จะลองดึง (ตัวแรกสำเร็จก็หยุด) ทุกตัวฟรี ไม่ต้องใช้ key
ASSETS = [
    {"key": "gold", "group": "โลหะมีค่า", "name_th": "ทองคำ (XAU/USD)", "unit": "USD/ออนซ์",
     "sources": [("stooq", "xauusd"), ("yahoo", "GC=F")], "dp": 2,
     "why_th": "ทองคือที่หลบภัยอันดับหนึ่งของโลก ทองวิ่งแรงผิดปกติ = เงินใหญ่กำลังกลัวอะไรบางอย่าง"},
    {"key": "silver", "group": "โลหะมีค่า", "name_th": "เงิน (XAG/USD)", "unit": "USD/ออนซ์",
     "sources": [("stooq", "xagusd"), ("yahoo", "SI=F")], "dp": 2,
     "why_th": "เงินเป็นทั้งที่หลบภัยและโลหะอุตสาหกรรม ใช้เช็คว่าที่ทองขึ้นเป็นเพราะกลัวหรือเพราะเงินเฟ้อ"},
    {"key": "wti", "group": "พลังงาน", "name_th": "น้ำมันดิบ WTI", "unit": "USD/บาร์เรล",
     "sources": [("stooq", "cl.f"), ("yahoo", "CL=F")], "dp": 2,
     "why_th": "น้ำมันขึ้นแรง = ตลาดกลัวเส้นทางขนส่งพลังงานถูกตัด ไทยนำเข้าน้ำมันเกือบทั้งหมด กระทบทันที"},
    {"key": "brent", "group": "พลังงาน", "name_th": "น้ำมันดิบ Brent", "unit": "USD/บาร์เรล",
     "sources": [("yahoo", "BZ=F"), ("stooq", "cb.f")], "dp": 2,
     "why_th": "Brent อิงตลาดยุโรป/ตะวันออกกลาง ไวต่อเหตุการณ์ฝั่งอิหร่านมากกว่า WTI"},
    {"key": "natgas", "group": "พลังงาน", "name_th": "ก๊าซธรรมชาติ", "unit": "USD/MMBtu",
     "sources": [("stooq", "ng.f"), ("yahoo", "NG=F")], "dp": 3,
     "why_th": "ก๊าซคือเชื้อเพลิงหลักผลิตไฟฟ้าของไทย ก๊าซแพง = ค่า Ft และค่าไฟบ้านขึ้นตาม"},
    {"key": "usdthb", "group": "ค่าเงิน", "name_th": "ดอลลาร์ / บาท", "unit": "บาทต่อ 1 USD",
     "sources": [("stooq", "usdthb"), ("yahoo", "THB=X")], "dp": 4,
     "why_th": "ตัวเลขนี้ตัดสินทุกอย่างของงานอสังหาฯ — บาทอ่อน ลูกค้าต่างชาติซื้อได้ถูกลงทันที"},
    {"key": "eurusd", "group": "ค่าเงิน", "name_th": "ยูโร / ดอลลาร์", "unit": "USD ต่อ 1 EUR",
     "sources": [("stooq", "eurusd"), ("yahoo", "EURUSD=X")], "dp": 4,
     "why_th": "ยูโรอ่อนผิดปกติมักแปลว่ายุโรปกำลังเจอแรงกดดันด้านพลังงานหรือความมั่นคง"},
    {"key": "usdjpy", "group": "ค่าเงิน", "name_th": "ดอลลาร์ / เยน", "unit": "เยนต่อ 1 USD",
     "sources": [("stooq", "usdjpy"), ("yahoo", "JPY=X")], "dp": 3,
     "why_th": "เยนเป็นที่หลบภัยเอเชีย เยนแข็งเร็วผิดปกติ = เงินกำลังหนีความเสี่ยง"},
    {"key": "usdcny", "group": "ค่าเงิน", "name_th": "ดอลลาร์ / หยวน", "unit": "หยวนต่อ 1 USD",
     "sources": [("stooq", "usdcny"), ("yahoo", "CNY=X")], "dp": 4,
     "why_th": "หยวนอ่อนแรง ๆ กระทบกำลังซื้อของลูกค้าจีนที่มาซื้อคอนโด/วิลล่าในไทย"},
    {"key": "usdrub", "group": "ค่าเงิน", "name_th": "ดอลลาร์ / รูเบิล", "unit": "รูเบิลต่อ 1 USD",
     "sources": [("stooq", "usdrub"), ("yahoo", "RUB=X")], "dp": 3,
     "why_th": "รูเบิลคือมาตรวัดแรงกดดันต่อรัสเซีย และเป็นกำลังซื้อของลูกค้ารัสเซียในภูเก็ต"},
    {"key": "gbpusd", "group": "ค่าเงิน", "name_th": "ปอนด์ / ดอลลาร์", "unit": "USD ต่อ 1 GBP",
     "sources": [("stooq", "gbpusd"), ("yahoo", "GBPUSD=X")], "dp": 4,
     "why_th": "ใช้คำนวณกำลังซื้อของลูกค้าอังกฤษ"},
    {"key": "vix", "group": "ความเสี่ยง", "name_th": "ดัชนีความกลัว VIX", "unit": "จุด",
     "sources": [("stooq", "^vix"), ("yahoo", "^VIX")], "dp": 2,
     "why_th": "VIX คือมาตรวัดความกลัวของตลาดหุ้นสหรัฐฯ เกิน 25 = เริ่มตื่น เกิน 35 = แตกตื่น"},
    {"key": "spx", "group": "ความเสี่ยง", "name_th": "ดัชนี S&P 500", "unit": "จุด",
     "sources": [("stooq", "^spx"), ("yahoo", "^GSPC")], "dp": 2,
     "why_th": "ตลาดหุ้นสหรัฐฯ คือตัวตั้งอารมณ์ของตลาดทั้งโลก รวมถึงเงินที่ไหลเข้า-ออกไทย"},
    {"key": "set", "group": "ความเสี่ยง", "name_th": "ดัชนี SET (ไทย)", "unit": "จุด",
     "sources": [("yahoo", "^SET.BK"), ("stooq", "^set")], "dp": 2,
     "why_th": "ตลาดหุ้นไทยสะท้อนความเชื่อมั่นต่อประเทศเราโดยตรง"},
    {"key": "defense", "group": "ความเสี่ยง", "name_th": "หุ้นกลุ่มอาวุธ (ETF: ITA)", "unit": "USD",
     "sources": [("stooq", "ita.us"), ("yahoo", "ITA")], "dp": 2,
     "why_th": "กองทุนหุ้นอุตสาหกรรมป้องกันประเทศ ถ้าวิ่งแรงกว่าตลาดรวม = เงินกำลังเดิมพันว่าจะมีสงครามยาว"},
    {"key": "wheat", "group": "อาหาร/อื่น ๆ", "name_th": "ข้าวสาลี", "unit": "เซนต์/บุชเชล",
     "sources": [("stooq", "zw.f"), ("yahoo", "ZW=F")], "dp": 2,
     "why_th": "สงครามในเขตผลิตอาหารดันราคาธัญพืชโลก ส่งผ่านมาถึงราคาอาหารสัตว์และค่าอาหารในไทย"},
    {"key": "btc", "group": "อาหาร/อื่น ๆ", "name_th": "บิตคอยน์", "unit": "USD",
     "sources": [("stooq", "btcusd"), ("yahoo", "BTC-USD")], "dp": 0,
     "why_th": "ช่วงวิกฤตจริง บิตคอยน์มักลงพร้อมหุ้น ไม่ใช่ที่หลบภัยอย่างที่หลายคนเชื่อ ใช้เช็คว่าเป็นการหนีความเสี่ยงจริงไหม"},
    {"key": "us10y", "group": "อาหาร/อื่น ๆ", "name_th": "พันธบัตรสหรัฐฯ 10 ปี", "unit": "% ต่อปี",
     "sources": [("stooq", "10usy.b"), ("yahoo", "^TNX")], "dp": 3,
     "why_th": "ผลตอบแทนร่วงเร็ว = เงินแห่เข้าพันธบัตรเพื่อหลบภัย เป็นสัญญาณกลัวที่ชัดที่สุดอันหนึ่ง"},
]

ASSET_GROUPS = ["โลหะมีค่า", "พลังงาน", "ค่าเงิน", "ความเสี่ยง", "อาหาร/อื่น ๆ"]

THAI_MONTHS = ["", "ม.ค.", "ก.พ.", "มี.ค.", "เม.ย.", "พ.ค.", "มิ.ย.",
               "ก.ค.", "ส.ค.", "ก.ย.", "ต.ค.", "พ.ย.", "ธ.ค."]


# =============================================================================
# 2. เครื่องมือพื้นฐาน
# =============================================================================

def th_datetime(dt: datetime) -> str:
    """แปลง datetime เป็นข้อความไทย เช่น '1 ก.ย. 2569 14:32 น.'"""
    d = dt.astimezone(TH_TZ)
    return f"{d.day} {THAI_MONTHS[d.month]} {d.year + 543} {d:%H:%M} น."


def time_ago_th(dt: datetime | None) -> str:
    if dt is None:
        return "ไม่ระบุเวลา"
    delta = datetime.now(timezone.utc) - dt.astimezone(timezone.utc)
    mins = int(delta.total_seconds() // 60)
    if mins < 0:
        return "เพิ่งประกาศ"
    if mins < 60:
        return f"{mins} นาทีที่แล้ว"
    if mins < 60 * 24:
        return f"{mins // 60} ชม.ที่แล้ว"
    return f"{mins // 1440} วันที่แล้ว"


def http_get(url: str, timeout: int = HTTP_TIMEOUT) -> bytes:
    req = Request(url, headers={
        "User-Agent": USER_AGENT,
        "Accept": "*/*",
        "Accept-Language": "en-US,en;q=0.8,th;q=0.6",
    })
    with urlopen(req, timeout=timeout) as resp:
        raw = resp.read()
    # บางแหล่ง (เช่น UN News) ส่ง gzip มาให้เสมอแม้ไม่ได้ขอ — คลายให้ก่อน
    if raw[:2] == b"\x1f\x8b":
        raw = gzip.decompress(raw)
    return raw


def describe_error(exc: Exception) -> str:
    """ข้อความ error สั้น ๆ ที่เอาไปโชว์หน้าเว็บได้ (โปร่งใสว่าพังตรงไหน)"""
    if isinstance(exc, HTTPError):
        return f"HTTP {exc.code} จากเซิร์ฟเวอร์ต้นทาง"
    if isinstance(exc, URLError):
        return f"เชื่อมต่อไม่ได้ ({exc.reason})"
    if isinstance(exc, TimeoutError):
        return "ต้นทางตอบช้าเกิน timeout"
    msg = str(exc).strip() or exc.__class__.__name__
    return msg[:160]


# =============================================================================
# 3. ดึงราคาสินทรัพย์  (Stooq เป็นหลัก, Yahoo Finance เป็นตัวสำรอง — ฟรีทั้งคู่)
# =============================================================================

def fetch_stooq(symbol: str) -> list[dict]:
    """ดึงราคาปิดรายวันจาก stooq.com (CSV ฟรี ไม่ต้องใช้ key)"""
    end = datetime.now(timezone.utc).date()
    start = end - timedelta(days=560)
    url = (f"https://stooq.com/q/d/l/?s={quote(symbol)}&i=d"
           f"&d1={start:%Y%m%d}&d2={end:%Y%m%d}")
    text = http_get(url).decode("utf-8", "replace").strip()
    lines = text.splitlines()
    if not lines or not lines[0].lower().startswith("date"):
        raise ValueError(f"stooq ตอบไม่ใช่ CSV: {text[:70]}")
    rows: list[dict] = []
    for row in csv.DictReader(lines):
        close = (row.get("Close") or "").strip()
        if not close or close.upper() in ("N/A", "NULL"):
            continue
        try:
            rows.append({"date": row["Date"], "close": float(close)})
        except ValueError:
            continue
    if len(rows) < 30:
        raise ValueError(f"ข้อมูลน้อยเกินไป ({len(rows)} วัน) เชื่อถือไม่ได้")
    rows.sort(key=lambda r: r["date"])
    return rows


def fetch_yahoo(symbol: str) -> list[dict]:
    """ดึงราคาปิดรายวันจาก Yahoo Finance chart API (ฟรี ไม่ต้องใช้ key)"""
    url = ("https://query1.finance.yahoo.com/v8/finance/chart/"
           f"{quote(symbol)}?range=2y&interval=1d")
    payload = json.loads(http_get(url).decode("utf-8", "replace"))
    chart = payload.get("chart") or {}
    if chart.get("error"):
        raise ValueError(str(chart["error"])[:80])
    result = (chart.get("result") or [None])[0]
    if not result:
        raise ValueError("Yahoo ไม่ส่งข้อมูลกลับมา")
    stamps = result.get("timestamp") or []
    closes = (result.get("indicators", {}).get("quote") or [{}])[0].get("close") or []
    rows = [
        {"date": datetime.fromtimestamp(t, timezone.utc).strftime("%Y-%m-%d"),
         "close": float(c)}
        for t, c in zip(stamps, closes) if c is not None
    ]
    if len(rows) < 30:
        raise ValueError(f"ข้อมูลน้อยเกินไป ({len(rows)} วัน)")
    rows.sort(key=lambda r: r["date"])
    return rows


FETCHERS = {"stooq": fetch_stooq, "yahoo": fetch_yahoo}
SOURCE_LABEL = {"stooq": "Stooq", "yahoo": "Yahoo Finance"}
SOURCE_HOME = {"stooq": "https://stooq.com/", "yahoo": "https://finance.yahoo.com/"}


def fetch_series(asset: dict) -> dict:
    """ลองดึงตามลำดับแหล่งที่กำหนด — สำเร็จตัวไหนใช้ตัวนั้น พร้อมจดว่าใช้แหล่งไหน"""
    attempts = []
    for kind, symbol in asset["sources"]:
        try:
            rows = FETCHERS[kind](symbol)
            return {
                "ok": True, "series": rows,
                "source_kind": kind, "source_label": SOURCE_LABEL[kind],
                "source_symbol": symbol, "source_home": SOURCE_HOME[kind],
                "attempts": attempts,
            }
        except Exception as exc:                      # noqa: BLE001 — ต้องกันทุกกรณี
            attempts.append(f"{SOURCE_LABEL[kind]}/{symbol}: {describe_error(exc)}")
    return {"ok": False, "series": [], "attempts": attempts,
            "error": " | ".join(attempts) or "ไม่มีแหล่งข้อมูล"}


# =============================================================================
# 4. คณิตศาสตร์ตรวจจับความผิดปกติ
#    ทุกตัวเลขคำนวณจากราคาปิดจริง สูตรเขียนกำกับไว้ให้ตรวจย้อนได้
# =============================================================================

def pct_change_back(closes: list[float], n: int) -> float | None:
    """% เปลี่ยนแปลงเทียบกับ n วันทำการก่อนหน้า"""
    if len(closes) <= n or closes[-1 - n] == 0:
        return None
    return (closes[-1] / closes[-1 - n] - 1) * 100


def sparkline_points(closes: list[float], width: int = 240, height: int = 48) -> str:
    """สร้างพิกัดกราฟเส้นเล็ก ๆ (SVG polyline) จากราคาปิด 90 วันล่าสุด"""
    pts = closes[-90:]
    if len(pts) < 2:
        return ""
    lo, hi = min(pts), max(pts)
    span = (hi - lo) or 1.0
    n = len(pts)
    coords = []
    for i, v in enumerate(pts):
        x = i / (n - 1) * width
        y = height - 2 - (v - lo) / span * (height - 4)
        coords.append(f"{x:.1f},{y:.1f}")
    return " ".join(coords)


def analyse_series(series: list[dict]) -> dict:
    """
    คำนวณสัญญาณผิดปกติจากอนุกรมราคา

    z-score  = (ผลตอบแทนวันนี้ − ค่าเฉลี่ยผลตอบแทน 90 วัน) ÷ ส่วนเบี่ยงเบนมาตรฐาน 90 วัน
               ใช้ log return เพื่อให้เทียบข้ามสินทรัพย์ได้อย่างเป็นธรรม
               |z| ≥ 2 = เกิดขึ้นราว 5% ของวัน   |z| ≥ 3 = ราว 0.3% ของวัน
    ความผันผวน = ส่วนเบี่ยงเบนมาตรฐานผลตอบแทนรายวัน × √252 (แปลงเป็นต่อปี)
    """
    closes = [r["close"] for r in series]
    dates = [r["date"] for r in series]
    out: dict = {"last": closes[-1], "last_date": dates[-1], "points": len(closes)}

    # ผลตอบแทนรายวันแบบ log
    rets: list[float] = []
    for prev, cur in zip(closes, closes[1:]):
        if prev > 0 and cur > 0:
            rets.append(math.log(cur / prev))
        else:
            rets.append(0.0)

    out["chg_1d"] = pct_change_back(closes, 1)
    out["chg_5d"] = pct_change_back(closes, 5)
    out["chg_20d"] = pct_change_back(closes, 20)
    out["chg_63d"] = pct_change_back(closes, 63)

    # ---- z-score ของการเคลื่อนไหววันล่าสุด ----
    z = None
    baseline = rets[-91:-1]          # 90 วันก่อนหน้า (ไม่รวมวันล่าสุด กันตัวเองปนเบสไลน์)
    if len(baseline) >= 30 and rets:
        mu = statistics.fmean(baseline)
        sd = statistics.pstdev(baseline)
        if sd > 0:
            z = (rets[-1] - mu) / sd
    out["z"] = z

    # ---- ความผันผวน ----
    vol20 = vol90 = ratio = None
    if len(rets) >= 20:
        vol20 = statistics.pstdev(rets[-20:]) * math.sqrt(252) * 100
    if len(rets) >= 90:
        vol90 = statistics.pstdev(rets[-90:]) * math.sqrt(252) * 100
    if vol20 and vol90 and vol90 > 0:
        ratio = vol20 / vol90
    out["vol20"], out["vol90"], out["vol_ratio"] = vol20, vol90, ratio

    # ---- ระยะห่างจากเส้นค่าเฉลี่ย 50 วัน ----
    ma50 = statistics.fmean(closes[-50:]) if len(closes) >= 50 else None
    out["ma50"] = ma50
    out["ma_dist"] = ((closes[-1] / ma50 - 1) * 100) if ma50 else None

    # ---- ตำแหน่งในกรอบ 52 สัปดาห์ ----
    window = closes[-252:] if len(closes) >= 252 else closes
    hi, lo = max(window), min(window)
    out["hi52"], out["lo52"] = hi, lo
    out["pos52"] = ((closes[-1] - lo) / (hi - lo) * 100) if hi > lo else 50.0
    out["at_high"] = closes[-1] >= hi - 1e-9
    out["at_low"] = closes[-1] <= lo + 1e-9

    # ---- สรุประดับความผิดปกติ + เหตุผลที่มีตัวเลขกำกับ ----
    reasons: list[str] = []
    az = abs(z) if z is not None else 0.0
    if z is not None and az >= 1.5:
        direction = "ขึ้น" if z > 0 else "ลง"
        reasons.append(
            f"วันล่าสุด{direction} {out['chg_1d']:+.2f}% คิดเป็น {z:+.2f} เท่าของส่วนเบี่ยงเบนมาตรฐาน "
            f"90 วัน (ปกติควรอยู่ในกรอบ ±2)"
        )
    if ratio is not None and ratio >= 1.5:
        reasons.append(
            f"ความผันผวน 20 วัน {vol20:.1f}% ต่อปี สูงกว่าค่าปกติ 90 วัน ({vol90:.1f}%) อยู่ {ratio:.2f} เท่า"
        )
    if out["at_high"]:
        reasons.append(f"ทำจุดสูงสุดในรอบ 52 สัปดาห์ที่ {hi:,.2f}")
    if out["at_low"]:
        reasons.append(f"ทำจุดต่ำสุดในรอบ 52 สัปดาห์ที่ {lo:,.2f}")
    if out["ma_dist"] is not None and abs(out["ma_dist"]) >= 8:
        reasons.append(f"ห่างเส้นค่าเฉลี่ย 50 วันถึง {out['ma_dist']:+.1f}%")

    if az >= 3:
        level, level_th = "extreme", "ผิดปกติรุนแรง"
    elif az >= 2:
        level, level_th = "odd", "ผิดปกติ"
    elif az >= 1.5 or (ratio or 0) >= 1.6 or out["at_high"] or out["at_low"]:
        level, level_th = "watch", "เริ่มน่าจับตา"
    else:
        level, level_th = "calm", "ปกติ"
        reasons.append("อยู่ในกรอบการเคลื่อนไหวปกติของ 90 วันที่ผ่านมา")

    out["level"], out["level_th"], out["reasons"] = level, level_th, reasons
    out["spark"] = sparkline_points(closes)
    out["spark_up"] = (out["chg_20d"] or 0) >= 0
    return out


LEVEL_STYLE = {
    "extreme": {"cls": "border-rose-500/60 bg-rose-500/10", "badge": "bg-rose-500 text-white",
                "text": "text-rose-300", "rank": 3},
    "odd": {"cls": "border-amber-500/60 bg-amber-500/10", "badge": "bg-amber-500 text-slate-900",
            "text": "text-amber-300", "rank": 2},
    "watch": {"cls": "border-sky-500/50 bg-sky-500/5", "badge": "bg-sky-500 text-slate-900",
              "text": "text-sky-300", "rank": 1},
    "calm": {"cls": "border-slate-800 bg-slate-900/40", "badge": "bg-slate-700 text-slate-200",
             "text": "text-slate-400", "rank": 0},
    "error": {"cls": "border-slate-700 bg-slate-900/40 border-dashed", "badge": "bg-slate-700 text-slate-300",
              "text": "text-slate-400", "rank": -1},
}


# =============================================================================
# 5. ดึงและให้คะแนนข่าว
# =============================================================================

def _text(el) -> str:
    return "".join(el.itertext()).strip() if el is not None else ""


def _local(tag) -> str:
    """ตัด namespace ออก เหลือแต่ชื่อแท็ก — ทำให้อ่าน RSS/RDF/Atom ด้วยโค้ดชุดเดียวได้"""
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) else ""


def _kids(node, *names):
    return [el for el in node if _local(el.tag) in names]


def _first(node, *names) -> str:
    found = _kids(node, *names)
    return _text(found[0]) if found else ""


def parse_feed(raw: bytes) -> list[dict]:
    """อ่าน RSS 2.0 / RDF / Atom ด้วย ElementTree (ไม่ต้องลง feedparser)"""
    root = ET.fromstring(raw)
    items: list[dict] = []

    nodes = [el for el in root.iter() if _local(el.tag) in ("item", "entry")]
    for node in nodes[:40]:
        title = _first(node, "title")
        if not title:
            continue

        link = _first(node, "link")
        if not link:                                    # Atom เก็บ URL ไว้ใน attribute href
            for ln in _kids(node, "link"):
                if ln.get("rel") in (None, "alternate") and ln.get("href"):
                    link = ln.get("href")
                    break
        if not link:
            link = _first(node, "guid", "id")

        summary = _first(node, "description", "summary", "encoded")
        summary = re.sub(r"<[^>]+>", " ", summary)
        summary = re.sub(r"\s+", " ", summary).strip()

        raw_date = _first(node, "pubDate", "date", "updated", "published")
        published = None
        if raw_date:
            try:
                published = parsedate_to_datetime(raw_date)
            except (TypeError, ValueError):
                try:
                    published = datetime.fromisoformat(raw_date.replace("Z", "+00:00"))
                except ValueError:
                    published = None
            if published is not None and published.tzinfo is None:
                published = published.replace(tzinfo=timezone.utc)

        items.append({"title": title, "link": link, "summary": summary[:400],
                      "published": published})
    return items


def score_item(item: dict) -> dict:
    """ให้คะแนนความรุนแรง + จัดโซน + ตรวจคำกำกวม (ทุกอย่างโชว์หลักฐานว่าจับคำไหนได้)"""
    blob = f"{item['title']} {item['summary']}".lower()

    matched: list[str] = []
    weight = 0
    for kw, w in ESCALATION_KEYWORDS.items():
        if kw in blob:
            matched.append(kw)
            weight = max(weight, w) + (2 if weight else 0)   # คำแรกให้เต็ม คำถัดไปบวกทีละ 2
    weight = min(weight, 14)

    calming = [k for k in DEESCALATION_KEYWORDS if k in blob]
    if calming:
        weight = max(0, weight - 5)

    best_key, best_hits = "global", 0
    for th in THEATRES:
        hits = sum(1 for k in th["kw"] if k in blob)
        if hits > best_hits:
            best_key, best_hits = th["key"], hits

    hedges = [h for h in HEDGE_WORDS if h in blob]

    item.update({
        "weight": weight, "matched": matched[:5], "calming": calming[:3],
        "theatre": best_key, "hedges": hedges[:3], "hedged": bool(hedges),
    })
    return item


def fetch_feed(feed: dict) -> dict:
    """ดึงหนึ่งแหล่ง แล้วคืนสถานะพร้อมข่าวที่ให้คะแนนแล้ว"""
    result = {"name": feed["name"], "tier": feed["tier"], "url": feed["url"],
              "home": feed["home"], "note_th": feed["note_th"],
              "ok": False, "count": 0, "error": None, "items": []}
    try:
        raw = http_get(feed["url"])
        cutoff = datetime.now(timezone.utc) - timedelta(days=5)
        items = []
        for it in parse_feed(raw):
            if it["published"] and it["published"] < cutoff:
                continue
            it["source"] = feed["name"]
            it["tier"] = feed["tier"]
            it["source_note"] = feed["note_th"]
            it["published_th"] = th_datetime(it["published"]) if it["published"] else "ไม่ระบุเวลา"
            it["ago"] = time_ago_th(it["published"])
            it["sort_key"] = (it["published"] or datetime(1970, 1, 1, tzinfo=timezone.utc)).timestamp()
            items.append(score_item(it))
        result.update({"ok": True, "count": len(items), "items": items})
    except Exception as exc:                              # noqa: BLE001
        result["error"] = describe_error(exc)
    return result


# =============================================================================
# 6. ดัชนีความตึงเครียด (คำนวณเองทั้งหมด — เปิดสูตรให้ตรวจได้)
# =============================================================================

def build_tension(news: list[dict], assets_by_key: dict) -> dict:
    now = datetime.now(timezone.utc)

    # ---- องค์ประกอบที่ 1: ข่าวยกระดับความรุนแรงจากแหล่งที่เชื่อถือได้ (เต็ม 40) ----
    recent = [n for n in news
              if n["tier"] in ("A", "B") and n["weight"] >= 5
              and n["published"] and (now - n["published"]) <= timedelta(hours=48)]
    news_raw = sum(n["weight"] for n in recent)
    news_score = min(40.0, news_raw * 0.7)

    # ---- องค์ประกอบที่ 2: จำนวนสินทรัพย์ที่เคลื่อนไหวผิดปกติ (เต็ม 35) ----
    odd_assets = []
    market_raw = 0.0
    for a in assets_by_key.values():
        if not a.get("ok") or a.get("z") is None:
            continue
        az = abs(a["z"])
        if az >= 1.5:
            market_raw += (min(az, 4.0) - 1.0) * 4.0
            odd_assets.append(f"{a['name_th']} (z={a['z']:+.1f})")
    market_score = min(35.0, market_raw)

    # ---- องค์ประกอบที่ 3: รูปแบบ "หนีเข้าที่หลบภัย" (เต็ม 25) ----
    haven_score = 0.0
    haven_notes: list[str] = []

    def g(key):
        a = assets_by_key.get(key)
        return a if a and a.get("ok") else None

    gold, vix, spx, wti, us10y = g("gold"), g("vix"), g("spx"), g("wti"), g("us10y")
    if gold and (gold.get("chg_5d") or 0) >= 2:
        haven_score += 8
        haven_notes.append(f"ทองคำ 5 วัน {gold['chg_5d']:+.1f}% — เงินไหลเข้าที่หลบภัย")
    if vix and (vix["last"] >= 25 or (vix.get("z") or 0) >= 1.5):
        haven_score += 7
        haven_notes.append(f"VIX อยู่ที่ {vix['last']:.1f} จุด (เกิน 25 = ตลาดเริ่มตื่นตัว)")
    if wti and abs(wti.get("chg_5d") or 0) >= 5:
        haven_score += 5
        haven_notes.append(f"น้ำมัน WTI 5 วัน {wti['chg_5d']:+.1f}% — ตลาดกังวลเรื่องอุปทานพลังงาน")
    if spx and (spx.get("chg_5d") or 0) <= -3:
        haven_score += 3
        haven_notes.append(f"S&P 500 5 วัน {spx['chg_5d']:+.1f}% — ตลาดหุ้นหนีความเสี่ยง")
    if us10y and (us10y.get("chg_5d") or 0) <= -5:
        haven_score += 2
        haven_notes.append(f"ผลตอบแทนพันธบัตรสหรัฐฯ 10 ปี 5 วัน {us10y['chg_5d']:+.1f}% — เงินแห่เข้าพันธบัตร")
    haven_score = min(25.0, haven_score)
    if not haven_notes:
        haven_notes.append("ยังไม่พบรูปแบบการหนีเข้าที่หลบภัยพร้อมกันหลายตลาด")

    total = round(news_score + market_score + haven_score, 1)

    if total >= 85:
        label, color, advice = "วิกฤต", "rose", "สถานการณ์เข้าขั้นวิกฤต ควรติดตามรายชั่วโมงและทบทวนแผนการเงิน"
    elif total >= 65:
        label, color, advice = "อันตราย", "rose", "หลายสัญญาณตรงกัน ควรติดตามใกล้ชิดและเตรียมแผนสำรอง"
    elif total >= 45:
        label, color, advice = "ตึงตัว", "amber", "เริ่มมีสัญญาณผิดปกติชัดเจน ควรตามข่าวทุกวัน"
    elif total >= 25:
        label, color, advice = "เฝ้าระวัง", "amber", "มีเรื่องต้องจับตา แต่ยังไม่ถึงขั้นผิดปกติในภาพรวม"
    else:
        label, color, advice = "ปกติ", "emerald", "ยังอยู่ในกรอบปกติ ไม่มีสัญญาณผิดปกติที่หลายตลาดยืนยันตรงกัน"

    return {
        "score": total, "label": label, "color": color, "advice": advice,
        "components": [
            {"name": "ข่าวยกระดับความรุนแรง (48 ชม.)", "score": round(news_score, 1), "max": 40,
             "formula": "ผลรวมน้ำหนักคำสำคัญของข่าวจากแหล่งระดับ A/B × 0.7 (เพดาน 40)",
             "detail": (f"พบ {len(recent)} ข่าวเข้าเกณฑ์ น้ำหนักรวมดิบ {news_raw}"
                        if recent else "ไม่พบข่าวยกระดับความรุนแรงจากแหล่งที่เชื่อถือได้ใน 48 ชม."),
             "items": [f"{n['source']}: {n['title'][:90]}" for n in
                       sorted(recent, key=lambda x: -x["weight"])[:4]]},
            {"name": "สินทรัพย์เคลื่อนไหวผิดปกติ", "score": round(market_score, 1), "max": 35,
             "formula": "ผลรวมของ (|z| − 1) × 4 เฉพาะตัวที่ |z| ≥ 1.5 (เพดาน 35)",
             "detail": (f"ผิดปกติ {len(odd_assets)} รายการ" if odd_assets
                        else "ทุกสินทรัพย์เคลื่อนไหวในกรอบปกติ"),
             "items": odd_assets[:6]},
            {"name": "รูปแบบหนีเข้าที่หลบภัย", "score": round(haven_score, 1), "max": 25,
             "formula": "ทอง +8 / VIX +7 / น้ำมัน +5 / หุ้นสหรัฐฯ +3 / พันธบัตร +2 เมื่อเข้าเงื่อนไข",
             "detail": "ดูว่าหลายตลาดกลัวพร้อมกันหรือไม่ (สัญญาณเดี่ยวมักเป็นเรื่องเฉพาะตัว)",
             "items": haven_notes},
        ],
    }


# =============================================================================
# 7. แปลผลมาที่ประเทศไทย  (คำนวณจากราคาจริงทั้งหมด)
# =============================================================================

def align_series(a: list[dict], b: list[dict]) -> list[dict]:
    """จับคู่สองอนุกรมตามวันที่ที่ตรงกัน คืน [{date, a, b}]"""
    mb = {r["date"]: r["close"] for r in b}
    return [{"date": r["date"], "a": r["close"], "b": mb[r["date"]]}
            for r in a if r["date"] in mb]


def build_thailand(raw_series: dict, assets_by_key: dict, property_thb: int) -> dict:
    out: dict = {"cards": [], "fx_rows": [], "property_thb": property_thb,
                 "gold": None, "gold_error": None, "fx_error": None}

    xau = raw_series.get("gold", {}).get("series") or []
    thb = raw_series.get("usdthb", {}).get("series") or []

    # ---- 1) ราคาทองคำแท่ง 96.5% ต่อ 1 บาท (คำนวณจากทองโลก × ค่าเงิน) ----
    if xau and thb:
        paired = align_series(xau, thb)
        if len(paired) >= 60:
            gold_thb = [
                {"date": p["date"],
                 "close": p["a"] / GRAMS_PER_TROY_OZ * GRAMS_PER_BAHT_GOLD * THAI_GOLD_PURITY * p["b"]}
                for p in paired
            ]
            an = analyse_series(gold_thb)
            an.update({
                "name_th": "ทองคำแท่ง 96.5% (คำนวณ) — บาทละ",
                "unit": "บาท / ทอง 1 บาท", "dp": 0,
                "formula": (f"(XAU/USD ÷ {GRAMS_PER_TROY_OZ} × {GRAMS_PER_BAHT_GOLD} × "
                            f"{THAI_GOLD_PURITY}) × USD/THB"),
                "inputs": (f"XAU/USD = {paired[-1]['a']:,.2f} · USD/THB = {paired[-1]['b']:,.4f} "
                           f"(ราคาปิด {paired[-1]['date']})"),
            })
            out["gold"] = an
        else:
            out["gold_error"] = "วันที่ของราคาทองกับค่าเงินตรงกันน้อยเกินไป คำนวณแล้วไม่น่าเชื่อถือ"
    else:
        out["gold_error"] = "ดึงราคาทองคำโลกหรือค่าเงินบาทไม่สำเร็จ จึงไม่คำนวณราคาทองไทยให้"

    # ---- 2) กำลังซื้อลูกค้าต่างชาติ (อสังหาฯ ราคาเท่าเดิม แต่เขาจ่ายกี่สกุลเงินตัวเอง) ----
    if thb:
        usdthb_now = thb[-1]["close"]

        def thb_per_unit(cur_key: str) -> tuple[float | None, list[float] | None]:
            """คืน (อัตราบาทต่อ 1 หน่วยเงินต่างชาติ ณ วันล่าสุด, อนุกรมย้อนหลัง)"""
            if cur_key == "USD":
                return usdthb_now, [r["close"] for r in thb]
            src = {"EUR": "eurusd", "GBP": "gbpusd", "CNY": "usdcny", "RUB": "usdrub"}[cur_key]
            rows = raw_series.get(src, {}).get("series") or []
            if not rows:
                return None, None
            paired = align_series(rows, thb)
            if len(paired) < 70:
                return None, None
            if cur_key in ("EUR", "GBP"):        # ตัวคูณ: EURUSD × USDTHB
                vals = [p["a"] * p["b"] for p in paired]
            else:                                 # ตัวหาร: USDTHB ÷ USDCNY
                vals = [p["b"] / p["a"] for p in paired if p["a"]]
            return vals[-1], vals

        currencies = [
            ("USD", "🇺🇸", "ลูกค้าอเมริกัน / ผู้ถือดอลลาร์"),
            ("EUR", "🇪🇺", "ลูกค้ายุโรป"),
            ("GBP", "🇬🇧", "ลูกค้าอังกฤษ"),
            ("CNY", "🇨🇳", "ลูกค้าจีน"),
            ("RUB", "🇷🇺", "ลูกค้ารัสเซีย"),
        ]
        for code, flag, who in currencies:
            rate, vals = thb_per_unit(code)
            if not rate or not vals:
                out["fx_rows"].append({"code": code, "flag": flag, "who": who, "ok": False,
                                       "error": "ดึงข้อมูลอัตราแลกเปลี่ยนไม่สำเร็จ"})
                continue
            cost_now = property_thb / rate
            row = {"code": code, "flag": flag, "who": who, "ok": True,
                   "rate": rate, "cost_now": cost_now}
            for label, back in (("20d", 20), ("63d", 63)):
                if len(vals) > back and vals[-1 - back]:
                    old_rate = vals[-1 - back]
                    cost_old = property_thb / old_rate
                    row[f"cost_{label}"] = cost_old
                    row[f"chg_{label}"] = (cost_now / cost_old - 1) * 100
                else:
                    row[f"cost_{label}"] = None
                    row[f"chg_{label}"] = None
            out["fx_rows"].append(row)
    else:
        out["fx_error"] = "ดึงค่าเงินบาทไม่สำเร็จ จึงคำนวณกำลังซื้อลูกค้าต่างชาติไม่ได้"

    # ---- 3) การ์ดกลไกส่งผ่านผลกระทบ (ข้อความอิงตัวเลขที่คำนวณได้จริงเท่านั้น) ----
    def card(icon, title, asset_key, mech, source_name, source_url, fmt=None):
        a = assets_by_key.get(asset_key)
        if not a or not a.get("ok"):
            return {"icon": icon, "title": title, "ok": False,
                    "error": (a or {}).get("error", "ไม่มีข้อมูล"), "mech": mech,
                    "source_name": source_name, "source_url": source_url}
        return {"icon": icon, "title": title, "ok": True, "mech": mech,
                "value": (fmt or (lambda v: f"{v:,.2f}"))(a["last"]),
                "unit": a["unit"], "chg_5d": a.get("chg_5d"), "chg_20d": a.get("chg_20d"),
                "level_th": a["level_th"], "level": a["level"],
                "asset_name": a["name_th"], "last_date": a["last_date"],
                "source_name": source_name, "source_url": source_url}

    out["cards"] = [
        card("🛢️", "ค่าครองชีพ & ค่าขนส่ง", "brent",
             "ไทยนำเข้าน้ำมันดิบเกือบทั้งหมด ราคาโลกขึ้น → ราคาขายปลีกหน้าปั๊มและค่าขนส่งสินค้าขึ้นตาม "
             "แล้วค่อยส่งผ่านไปที่ราคาสินค้าทั่วไปในอีกไม่กี่สัปดาห์",
             "สนพ. กระทรวงพลังงาน (ราคาขายปลีกจริงในไทย)", "https://www.eppo.go.th/index.php/th/petroleum/oil-price"),
        card("⚡", "ค่าไฟฟ้า (ค่า Ft)", "natgas",
             "ไฟฟ้าไทยผลิตจากก๊าซธรรมชาติเป็นหลัก ราคาก๊าซโลกขึ้น → ต้นทุนเชื้อเพลิงขึ้น → "
             "เป็นแรงกดดันให้ค่า Ft ในรอบถัดไปปรับขึ้น",
             "กกพ. (ประกาศค่า Ft อย่างเป็นทางการ)", "https://www.erc.or.th/"),
        card("💱", "กำลังซื้อลูกค้าต่างชาติ", "usdthb",
             "บาทอ่อน = ลูกค้าต่างชาติจ่ายเงินสกุลตัวเองน้อยลงเพื่อซื้อทรัพย์ราคาบาทเท่าเดิม "
             "เป็นจังหวะปิดดีลที่ดีขึ้น / บาทแข็ง = ตรงกันข้าม",
             "ธนาคารแห่งประเทศไทย (อัตราอ้างอิงทางการ)", "https://www.bot.or.th/th/statistics/exchange-rate.html",
             lambda v: f"{v:,.4f}"),
        card("📉", "ความเชื่อมั่นตลาดไทย", "set",
             "ต่างชาติมักขายหุ้นตลาดเกิดใหม่ก่อนเมื่อความเสี่ยงโลกสูงขึ้น SET ที่ร่วงพร้อมบาทอ่อน "
             "คือภาพเงินทุนไหลออก ซึ่งกดความเชื่อมั่นการลงทุนในประเทศ",
             "ตลาดหลักทรัพย์แห่งประเทศไทย", "https://www.set.or.th/th/home"),
        card("🌾", "ราคาอาหาร & อาหารสัตว์", "wheat",
             "สงครามในเขตผลิตธัญพืชดันราคาข้าวสาลีโลก ซึ่งเป็นวัตถุดิบอาหารสัตว์ที่ไทยนำเข้า "
             "ต้นทุนเลี้ยงสัตว์ขึ้น → ราคาเนื้อสัตว์และอาหารในประเทศขยับตาม",
             "FAO Food Price Index", "https://www.fao.org/worldfoodsituation/foodpricesindex/en/"),
    ]
    return out


# =============================================================================
# 8. ประกอบข้อมูลทั้งหมด (พร้อมแคช 10 นาที)
# =============================================================================

_cache: dict = {"data": None, "ts": 0.0}
_cache_lock = threading.Lock()


def build_snapshot(property_thb: int = DEFAULT_PROPERTY_THB) -> dict:
    started = time.time()

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
        feed_future = pool.map(fetch_feed, FEEDS)
        asset_future = pool.map(fetch_series, ASSETS)
        feed_results = list(feed_future)
        series_results = list(asset_future)

    # ---------- สินทรัพย์ ----------
    raw_series: dict = {}
    assets: list[dict] = []
    assets_by_key: dict = {}
    for meta, res in zip(ASSETS, series_results):
        raw_series[meta["key"]] = res
        row = {"key": meta["key"], "group": meta["group"], "name_th": meta["name_th"],
               "unit": meta["unit"], "why_th": meta["why_th"], "dp": meta["dp"]}
        if res["ok"]:
            try:
                row.update(analyse_series(res["series"]))
                row.update({"ok": True, "source_label": res["source_label"],
                            "source_symbol": res["source_symbol"],
                            "source_home": res["source_home"]})
            except Exception as exc:                       # noqa: BLE001
                row.update({"ok": False, "level": "error", "level_th": "คำนวณไม่ได้",
                            "error": describe_error(exc)})
        else:
            row.update({"ok": False, "level": "error", "level_th": "ดึงข้อมูลไม่ได้",
                        "error": res.get("error", "ไม่ทราบสาเหตุ")})
        assets.append(row)
        assets_by_key[meta["key"]] = row

    # เรียงตามความผิดปกติก่อน แล้วค่อยตามขนาดของ z
    assets.sort(key=lambda a: (-LEVEL_STYLE[a["level"]]["rank"], -abs(a.get("z") or 0)))

    # ---------- ข่าว ----------
    all_items: list[dict] = []
    seen: set[str] = set()
    for fr in feed_results:
        for it in fr["items"]:
            fingerprint = re.sub(r"[^a-z0-9ก-๙]", "", it["title"].lower())[:70]
            if fingerprint in seen:
                continue
            seen.add(fingerprint)
            all_items.append(it)

    # จุดที่ต้องจับตา
    theatres = []
    for th in THEATRES:
        mine = [n for n in all_items if n["theatre"] == th["key"]]
        hot = sorted(mine, key=lambda n: (-n["weight"], -n["sort_key"]))
        trusted_hot = [n for n in hot if n["tier"] in ("A", "B")]
        top_w = max((n["weight"] for n in trusted_hot), default=0)
        if top_w >= 8:
            state, state_cls = "ร้อน", "bg-rose-500/15 text-rose-300 border-rose-500/40"
        elif top_w >= 5:
            state, state_cls = "ตึง", "bg-amber-500/15 text-amber-300 border-amber-500/40"
        elif mine:
            state, state_cls = "เฝ้าดู", "bg-slate-700/40 text-slate-300 border-slate-600/50"
        else:
            state, state_cls = "ไม่มีข่าวใหม่", "bg-slate-800/60 text-slate-500 border-slate-700"
        theatres.append({**{k: th[k] for k in ("key", "emoji", "name_th", "name_en", "why_th")},
                         "count": len(mine), "top_weight": top_w,
                         "state": state, "state_cls": state_cls,
                         "items": hot[:4]})
    theatres.sort(key=lambda t: (-t["top_weight"], -t["count"]))

    # ข่าวที่ต้องจับตา = แหล่งเชื่อถือได้ + น้ำหนักสูง
    watchlist = sorted(
        [n for n in all_items if n["tier"] in ("A", "B") and n["weight"] >= 5 and not n["hedged"]],
        key=lambda n: (-n["weight"], -n["sort_key"]))[:14]

    # ข่าวน่าสนใจแต่ยังเชื่อไม่ได้ = แหล่งระดับ C/D หรือมีคำกำกวม
    unverified = []
    for n in all_items:
        reasons = []
        if n["tier"] == "D":
            reasons.append(f"แหล่ง “{n['source']}” อยู่ในกลุ่มต้องระวังสูง — {n['source_note']}")
        elif n["tier"] == "C":
            reasons.append(f"แหล่ง “{n['source']}” ต้องตรวจสอบต้นทางก่อน — {n['source_note']}")
        if n["hedged"]:
            reasons.append("พาดหัวใช้คำกำกวมที่แปลว่ายังไม่ยืนยัน: "
                           + ", ".join(f"“{h}”" for h in n["hedges"]))
        if reasons and n["weight"] >= 3:
            unverified.append({**n, "warn_reasons": reasons})
    unverified.sort(key=lambda n: (-n["weight"], -n["sort_key"]))
    unverified = unverified[:12]

    tension = build_tension(all_items, assets_by_key)
    thailand = build_thailand(raw_series, assets_by_key, property_thb)

    sources = []
    for fr in feed_results:
        sources.append({"name": fr["name"], "tier": fr["tier"], "url": fr["url"],
                        "home": fr["home"], "note_th": fr["note_th"],
                        "ok": fr["ok"], "count": fr["count"], "error": fr["error"],
                        "kind": "ข่าว"})
    for meta, res in zip(ASSETS, series_results):
        sources.append({
            "name": f"{meta['name_th']}", "tier": "A", "kind": "ราคา",
            "url": res.get("source_home", "https://stooq.com/"),
            "home": res.get("source_home", "https://stooq.com/"),
            "note_th": (f"ดึงจาก {res['source_label']} (สัญลักษณ์ {res['source_symbol']})"
                        if res["ok"] else "ดึงไม่สำเร็จทุกแหล่งที่ตั้งไว้"),
            "ok": res["ok"], "count": len(res.get("series", [])),
            "error": res.get("error"),
        })

    now = datetime.now(timezone.utc)
    return {
        "generated_iso": now.isoformat(),
        "generated_th": th_datetime(now),
        "build_seconds": round(time.time() - started, 1),
        "tension": tension,
        "theatres": theatres,
        "watchlist": watchlist,
        "unverified": unverified,
        "assets": assets,
        "asset_groups": ASSET_GROUPS,
        "thailand": thailand,
        "sources": sources,
        "tiers": TIERS,
        "stats": {
            "news_total": len(all_items),
            "feeds_ok": sum(1 for f in feed_results if f["ok"]),
            "feeds_total": len(feed_results),
            "assets_ok": sum(1 for a in assets if a.get("ok")),
            "assets_total": len(assets),
            "assets_odd": sum(1 for a in assets if a["level"] in ("odd", "extreme")),
        },
    }


def get_snapshot(force: bool = False, property_thb: int = DEFAULT_PROPERTY_THB) -> dict:
    with _cache_lock:
        fresh = (_cache["data"] is not None
                 and (time.time() - _cache["ts"]) < CACHE_TTL_SEC
                 and _cache["data"]["thailand"]["property_thb"] == property_thb)
        if fresh and not force:
            data = dict(_cache["data"])
            data["cached"] = True
            data["cache_age_min"] = int((time.time() - _cache["ts"]) // 60)
            return data
        data = build_snapshot(property_thb)
        _cache["data"] = data
        _cache["ts"] = time.time()
        out = dict(data)
        out["cached"] = False
        out["cache_age_min"] = 0
        return out


# =============================================================================
# 9. หน้าเว็บ (Tailwind CDN + Noto Sans Thai)
# =============================================================================

PAGE = r"""<!doctype html>
<html lang="th" class="scroll-smooth">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{{ title_th }} — World Watch</title>
<script src="https://cdn.tailwindcss.com"></script>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@300;400;500;600;700;800&family=JetBrains+Mono:wght@400;600&display=swap" rel="stylesheet">
<script>
tailwind.config = {
  theme: {
    extend: {
      fontFamily: {
        sans: ['Noto Sans Thai', 'ui-sans-serif', 'system-ui'],
        mono: ['JetBrains Mono', 'ui-monospace', 'monospace']
      }
    }
  }
}
</script>
<style>
  body { background:
    radial-gradient(1100px 600px at 12% -8%, rgba(56,189,248,.10), transparent 60%),
    radial-gradient(900px 520px at 88% 0%, rgba(244,63,94,.10), transparent 55%),
    #020617; }
  /* ไม่ใช้ backdrop-filter กับการ์ด เพราะมีหลายสิบใบ กินแรงเครื่องและทำให้จอมือถือกระตุก */
  .card { box-shadow: 0 1px 2px rgba(0,0,0,.35); }
  details > summary { list-style: none; cursor: pointer; }
  details > summary::-webkit-details-marker { display: none; }
  .pulse-dot { animation: pulse 2.2s cubic-bezier(.4,0,.6,1) infinite; }
  @keyframes pulse { 0%,100%{opacity:1} 50%{opacity:.35} }
  ::-webkit-scrollbar { width: 10px; height: 10px; }
  ::-webkit-scrollbar-thumb { background: #1e293b; border-radius: 8px; }
</style>
</head>
<body class="font-sans text-slate-200 antialiased min-h-screen">

<!-- ═══════════ HEADER ═══════════ -->
<header class="sticky top-0 z-40 border-b border-slate-800/80 bg-slate-950/85 backdrop-blur">
  <div class="mx-auto max-w-7xl px-4 py-3 flex flex-wrap items-center gap-x-4 gap-y-2">
    <div class="flex items-center gap-3 mr-auto">
      <div class="grid h-10 w-10 place-items-center rounded-xl bg-gradient-to-br from-sky-500 to-rose-500 text-lg shadow-lg shadow-sky-900/40">🛰️</div>
      <div>
        <h1 class="text-base sm:text-lg font-bold leading-tight" data-i18n="brand">{{ title_th }}</h1>
        <p class="text-[11px] text-slate-400 leading-tight" data-i18n="tagline">
          จุดร้อนทั่วโลก · ความผิดปกติของราคาสินทรัพย์ · แล้วไทยกระทบอะไร
        </p>
      </div>
    </div>

    <div class="flex items-center gap-2 text-xs">
      <span class="hidden sm:inline text-slate-400">
        <span data-i18n="updated">อัปเดตล่าสุด</span>
        <b class="text-slate-200">{{ data.generated_th }}</b>
        {% if data.cached %}<span class="text-slate-500">(แคช {{ data.cache_age_min }} นาที)</span>{% endif %}
      </span>
      <button onclick="toggleLang()" id="langBtn"
        class="rounded-lg border border-slate-700 px-2.5 py-1.5 font-semibold text-slate-300 hover:bg-slate-800">EN</button>
      {% if static_mode %}
      <span class="rounded-lg border border-slate-700 px-3 py-1.5 font-semibold text-slate-400">สร้างใหม่ทุก 30 นาที</span>
      {% else %}
      <a href="?refresh=1"
        class="rounded-lg bg-sky-500 px-3 py-1.5 font-semibold text-slate-950 hover:bg-sky-400"
        data-i18n="refresh">ดึงข้อมูลใหม่</a>
      {% endif %}
    </div>
  </div>

  <!-- แถบสรุปสถานะแหล่งข้อมูล -->
  <div class="border-t border-slate-800/60 bg-slate-900/40">
    <div class="mx-auto max-w-7xl px-4 py-1.5 flex flex-wrap items-center gap-x-5 gap-y-1 text-[11px] text-slate-400">
      <span>📡 แหล่งข่าว <b class="text-slate-200">{{ data.stats.feeds_ok }}/{{ data.stats.feeds_total }}</b> ใช้งานได้</span>
      <span>📈 ราคาสินทรัพย์ <b class="text-slate-200">{{ data.stats.assets_ok }}/{{ data.stats.assets_total }}</b> ดึงสำเร็จ</span>
      <span>📰 ข่าวที่ประมวลผล <b class="text-slate-200">{{ data.stats.news_total }}</b> ชิ้น</span>
      <span>⚠️ สินทรัพย์ผิดปกติ <b class="{% if data.stats.assets_odd %}text-rose-300{% else %}text-slate-200{% endif %}">{{ data.stats.assets_odd }}</b> รายการ</span>
      {% if static_mode %}
      <span class="ml-auto text-slate-500">หน้านี้สร้างไว้ล่วงหน้าเมื่อ {{ data.generated_th }} · GitHub สร้างใหม่ให้ทุก 30 นาที</span>
      {% else %}
      <span class="ml-auto text-slate-500">ประมวลผลใน {{ data.build_seconds }} วินาที · รีเฟรชอัตโนมัติทุก 10 นาที</span>
      {% endif %}
    </div>
  </div>
</header>

<main class="mx-auto max-w-7xl px-4 py-6 space-y-10">

  <!-- ═══════════ 1. ดัชนีความตึงเครียด ═══════════ -->
  <section>
    <div class="grid gap-4 lg:grid-cols-[minmax(0,340px)_1fr]">

      <div class="card rounded-2xl border border-slate-800 bg-slate-900/50 p-5">
        <p class="text-xs font-semibold uppercase tracking-wider text-slate-400" data-i18n="gaugeTitle">ระดับความตึงเครียดของโลก</p>

        {% set c = data.tension.color %}
        <div class="relative mt-3 flex justify-center">
          <svg viewBox="0 0 200 116" class="w-full max-w-[280px]">
            <path d="M14 104 A86 86 0 0 1 186 104" fill="none" stroke="#1e293b" stroke-width="16" stroke-linecap="round"/>
            <path d="M14 104 A86 86 0 0 1 186 104" fill="none" stroke-width="16" stroke-linecap="round"
                  stroke="url(#g1)" stroke-dasharray="270"
                  stroke-dashoffset="{{ 270 - (270 * data.tension.score / 100) }}"/>
            <defs>
              <linearGradient id="g1" x1="0" y1="0" x2="1" y2="0">
                <stop offset="0%" stop-color="#34d399"/><stop offset="45%" stop-color="#fbbf24"/>
                <stop offset="100%" stop-color="#fb7185"/>
              </linearGradient>
            </defs>
            <text x="100" y="86" text-anchor="middle" class="fill-white" style="font-size:34px;font-weight:800">{{ data.tension.score }}</text>
            <text x="100" y="104" text-anchor="middle" class="fill-slate-400" style="font-size:11px">จาก 100 คะแนน</text>
          </svg>
        </div>

        <div class="mt-1 text-center">
          <span class="inline-flex items-center gap-2 rounded-full border px-3 py-1 text-sm font-bold
            {% if c == 'rose' %}border-rose-500/50 bg-rose-500/15 text-rose-300
            {% elif c == 'amber' %}border-amber-500/50 bg-amber-500/15 text-amber-300
            {% else %}border-emerald-500/50 bg-emerald-500/15 text-emerald-300{% endif %}">
            <span class="pulse-dot h-2 w-2 rounded-full
              {% if c == 'rose' %}bg-rose-400{% elif c == 'amber' %}bg-amber-400{% else %}bg-emerald-400{% endif %}"></span>
            {{ data.tension.label }}
          </span>
          <p class="mt-2 text-xs leading-relaxed text-slate-400">{{ data.tension.advice }}</p>
        </div>

        <p class="mt-4 rounded-lg border border-slate-800 bg-slate-950/60 p-2.5 text-[11px] leading-relaxed text-slate-500">
          ⚠️ ดัชนีนี้เครื่องมือนี้<b class="text-slate-400">คำนวณขึ้นเอง</b> ไม่ใช่ดัชนีมาตรฐานสากล
          ใช้เพื่อจัดลำดับว่าควรสนใจอะไรก่อน ไม่ใช่การพยากรณ์ว่าจะเกิดสงคราม
        </p>
      </div>

      <div class="card rounded-2xl border border-slate-800 bg-slate-900/50 p-5">
        <p class="text-xs font-semibold uppercase tracking-wider text-slate-400 mb-3">คะแนนนี้มาจากไหน — เปิดดูสูตรได้ทุกข้อ</p>
        <div class="space-y-3">
          {% for comp in data.tension.components %}
          <details class="group rounded-xl border border-slate-800 bg-slate-950/50 p-3">
            <summary class="flex items-center gap-3">
              <span class="flex-1 text-sm font-semibold text-slate-200">{{ comp.name }}</span>
              <span class="font-mono text-sm text-slate-300">{{ comp.score }}<span class="text-slate-600">/{{ comp.max }}</span></span>
              <span class="text-slate-500 transition group-open:rotate-180">▾</span>
            </summary>
            <div class="mt-2 h-1.5 w-full overflow-hidden rounded-full bg-slate-800">
              <div class="h-full rounded-full bg-gradient-to-r from-sky-500 to-rose-500"
                   style="width: {{ (comp.score / comp.max * 100) | round(1) }}%"></div>
            </div>
            <div class="mt-3 space-y-2 text-xs">
              <p class="text-slate-400"><b class="text-slate-300">สูตร:</b> <span class="font-mono">{{ comp.formula }}</span></p>
              <p class="text-slate-400">{{ comp.detail }}</p>
              {% if comp["items"] %}
              <ul class="space-y-1 border-l-2 border-slate-800 pl-3 text-slate-400">
                {% for line in comp["items"] %}<li>• {{ line }}</li>{% endfor %}
              </ul>
              {% endif %}
            </div>
          </details>
          {% endfor %}
        </div>
      </div>
    </div>
  </section>

  <!-- ═══════════ 2. จุดที่ต้องจับตา ═══════════ -->
  <section>
    <div class="mb-3 flex items-end justify-between gap-3">
      <div>
        <h2 class="text-lg font-bold" data-i18n="theatres">🌍 จุดที่ต้องจับตา</h2>
        <p class="text-xs text-slate-400">จัดกลุ่มข่าวอัตโนมัติตามสมรภูมิ เรียงจากที่มีข่าวรุนแรงที่สุด</p>
      </div>
    </div>

    <div class="grid gap-3 sm:grid-cols-2 lg:grid-cols-3">
      {% for t in data.theatres %}
      <div class="card rounded-2xl border border-slate-800 bg-slate-900/50 p-4 flex flex-col">
        <div class="flex items-start gap-3">
          <span class="text-2xl leading-none">{{ t.emoji }}</span>
          <div class="flex-1 min-w-0">
            <h3 class="text-sm font-bold leading-tight">{{ t.name_th }}</h3>
            <p class="text-[11px] text-slate-500">{{ t.name_en }}</p>
          </div>
          <span class="shrink-0 rounded-full border px-2 py-0.5 text-[11px] font-semibold {{ t.state_cls }}">{{ t.state }}</span>
        </div>

        <p class="mt-2 text-[11px] leading-relaxed text-slate-400">{{ t.why_th }}</p>

        <div class="mt-3 space-y-2 flex-1">
          {% for n in t["items"] %}
          <a href="{{ n.link }}" target="_blank" rel="noopener"
             class="block rounded-lg border border-slate-800/80 bg-slate-950/50 p-2 hover:border-slate-600 transition">
            <div class="flex items-center gap-1.5 text-[10px] mb-0.5">
              <span class="rounded border px-1 py-px font-semibold {{ data.tiers[n.tier].cls }}">{{ n.source }}</span>
              <span class="text-slate-500">{{ n.ago }}</span>
              {% if n.weight >= 7 %}<span class="ml-auto rounded bg-rose-500/20 px-1 py-px font-bold text-rose-300">รุนแรง {{ n.weight }}</span>
              {% elif n.weight >= 5 %}<span class="ml-auto rounded bg-amber-500/20 px-1 py-px font-bold text-amber-300">ตึง {{ n.weight }}</span>{% endif %}
            </div>
            <p class="text-[12px] leading-snug text-slate-300 line-clamp-2">{{ n.title }}</p>
          </a>
          {% else %}
          <p class="rounded-lg border border-dashed border-slate-800 p-3 text-center text-[11px] text-slate-600">
            ยังไม่พบข่าวใหม่ในโซนนี้จากแหล่งที่ตั้งไว้
          </p>
          {% endfor %}
        </div>

        <p class="mt-2 text-right text-[10px] text-slate-600">พบข่าวในโซนนี้ {{ t.count }} ชิ้น (5 วันล่าสุด)</p>
      </div>
      {% endfor %}
    </div>
  </section>

  <!-- ═══════════ 3. ข่าวที่ต้องจับตาเป็นพิเศษ ═══════════ -->
  <section>
    <h2 class="mb-1 text-lg font-bold" data-i18n="watch">🚨 แจ้งเตือนให้จับตา</h2>
    <p class="mb-3 text-xs text-slate-400">
      เฉพาะข่าวจากแหล่งระดับ A/B ที่จับคำสำคัญของการยกระดับความรุนแรงได้ · กดที่การ์ดเพื่อไปอ่านต้นทาง
    </p>

    {% if data.watchlist %}
    <div class="grid gap-2.5 md:grid-cols-2">
      {% for n in data.watchlist %}
      <a href="{{ n.link }}" target="_blank" rel="noopener"
         class="card group rounded-xl border border-slate-800 bg-slate-900/50 p-3.5 hover:border-sky-600/60 transition flex gap-3">
        <div class="shrink-0 grid h-11 w-11 place-items-center rounded-lg font-mono text-sm font-bold
          {% if n.weight >= 10 %}bg-rose-500/20 text-rose-300
          {% elif n.weight >= 7 %}bg-amber-500/20 text-amber-300
          {% else %}bg-sky-500/20 text-sky-300{% endif %}">{{ n.weight }}</div>
        <div class="min-w-0">
          <div class="flex flex-wrap items-center gap-1.5 text-[10px] mb-1">
            <span class="rounded border px-1.5 py-px font-semibold {{ data.tiers[n.tier].cls }}">
              {{ n.source }} · {{ data.tiers[n.tier].label_th }}
            </span>
            <span class="text-slate-500">{{ n.ago }} · {{ n.published_th }}</span>
          </div>
          <p class="text-sm font-semibold leading-snug text-slate-100 group-hover:text-sky-300">{{ n.title }}</p>
          {% if n.matched %}
          <p class="mt-1.5 text-[10px] text-slate-500">
            คำที่ทำให้ถูกยกขึ้นมา:
            {% for m in n.matched %}<span class="mr-1 rounded bg-slate-800 px-1 py-px font-mono text-slate-400">{{ m }}</span>{% endfor %}
          </p>
          {% endif %}
          {% if n.calming %}
          <p class="mt-1 text-[10px] text-emerald-400">✓ มีสัญญาณผ่อนคลายในข่าวเดียวกัน: {{ n.calming | join(', ') }}</p>
          {% endif %}
        </div>
      </a>
      {% endfor %}
    </div>
    {% else %}
    <div class="rounded-xl border border-dashed border-slate-800 p-8 text-center">
      <p class="text-3xl">🕊️</p>
      <p class="mt-2 text-sm font-semibold text-slate-300">ยังไม่มีข่าวยกระดับความรุนแรงจากแหล่งที่เชื่อถือได้</p>
      <p class="mt-1 text-xs text-slate-500">
        นี่คือ “ข่าวดี” ในบริบทนี้ — แต่ก็แปลว่าแหล่งที่ตั้งไว้ยังไม่รายงาน ไม่ได้แปลว่าโลกไม่มีอะไรเกิดขึ้น
      </p>
    </div>
    {% endif %}
  </section>

  <!-- ═══════════ 4. ความผิดปกติของราคาสินทรัพย์ ═══════════ -->
  <section>
    <div class="mb-3">
      <h2 class="text-lg font-bold" data-i18n="assets">📊 การเคลื่อนไหวผิดปกติของทองคำและสินทรัพย์อื่น</h2>
      <p class="text-xs text-slate-400">
        เรียงจากผิดปกติมากที่สุด · ทุกตัวเลขคำนวณจากราคาปิดจริงย้อนหลังกว่า 1 ปี ไม่มีการประมาณค่า
      </p>
    </div>

    <details class="mb-4 rounded-xl border border-slate-800 bg-slate-900/40 p-3">
      <summary class="flex items-center gap-2 text-xs font-semibold text-slate-300">
        <span class="rounded bg-slate-800 px-2 py-0.5">?</span> อ่านค่า z-score ยังไง (กดเพื่อดู)
        <span class="ml-auto text-slate-500">▾</span>
      </summary>
      <div class="mt-3 grid gap-3 text-xs text-slate-400 sm:grid-cols-2">
        <div class="rounded-lg bg-slate-950/60 p-3">
          <p class="font-mono text-[11px] text-sky-300">z = (ผลตอบแทนวันนี้ − ค่าเฉลี่ย 90 วัน) ÷ ส่วนเบี่ยงเบนมาตรฐาน 90 วัน</p>
          <p class="mt-2 leading-relaxed">
            พูดง่าย ๆ คือ “วันนี้มันวิ่งแรงกว่าปกติกี่เท่า” โดยเทียบกับนิสัยของสินทรัพย์ตัวนั้นเองใน 90 วันที่ผ่านมา
            ทำแบบนี้ทำให้เทียบทองกับบิตคอยน์ได้อย่างเป็นธรรม
          </p>
        </div>
        <ul class="space-y-1.5 rounded-lg bg-slate-950/60 p-3">
          <li><b class="text-slate-300 font-mono">|z| &lt; 1.5</b> — ปกติ เกิดขึ้นเกือบทุกวัน</li>
          <li><b class="text-sky-300 font-mono">|z| ≥ 1.5</b> — เริ่มน่าจับตา</li>
          <li><b class="text-amber-300 font-mono">|z| ≥ 2</b> — ผิดปกติ เกิดราว 5% ของวันทำการ</li>
          <li><b class="text-rose-300 font-mono">|z| ≥ 3</b> — ผิดปกติรุนแรง เกิดราว 0.3% ของวัน (ปีละ ~1 ครั้ง)</li>
        </ul>
      </div>
    </details>

    {% for group in data.asset_groups %}
      {% set rows = data.assets | selectattr('group', 'equalto', group) | list %}
      {% if rows %}
      <h3 class="mb-2 mt-4 text-xs font-bold uppercase tracking-wider text-slate-500">{{ group }}</h3>
      <div class="grid gap-3 sm:grid-cols-2 xl:grid-cols-3">
        {% for a in rows %}
        {% set st = level_style[a.level] %}
        <div class="card rounded-2xl border p-4 {{ st.cls }}">
          <div class="flex items-start gap-2">
            <div class="min-w-0 flex-1">
              <h4 class="text-sm font-bold leading-tight text-slate-100">{{ a.name_th }}</h4>
              <p class="text-[10px] text-slate-500">{{ a.unit }}</p>
            </div>
            <span class="shrink-0 rounded-full px-2 py-0.5 text-[10px] font-bold {{ st.badge }}">{{ a.level_th }}</span>
          </div>

          {% if a.ok %}
          <div class="mt-3 flex items-end gap-3">
            <div>
              <p class="font-mono text-2xl font-bold leading-none text-white">
                {{ '{:,.{}f}'.format(a.last, a.dp) }}
              </p>
              <p class="mt-1 text-[10px] text-slate-500">ราคาปิด {{ a.last_date }}</p>
            </div>
            <div class="ml-auto text-right">
              {% if a.chg_1d is not none %}
              <p class="font-mono text-sm font-bold {% if a.chg_1d >= 0 %}text-emerald-400{% else %}text-rose-400{% endif %}">
                {{ '%+.2f'|format(a.chg_1d) }}%
              </p>
              <p class="text-[10px] text-slate-500">1 วัน</p>
              {% endif %}
            </div>
          </div>

          {% if a.spark %}
          <svg viewBox="0 0 240 48" preserveAspectRatio="none" class="mt-2 h-10 w-full">
            <polyline points="{{ a.spark }}" fill="none" stroke-width="1.8" stroke-linejoin="round" stroke-linecap="round"
              stroke="{% if a.spark_up %}#34d399{% else %}#fb7185{% endif %}"/>
          </svg>
          <p class="text-right text-[9px] text-slate-600">90 วันล่าสุด</p>
          {% endif %}

          <div class="mt-2 grid grid-cols-4 gap-1 text-center">
            {% for label, val in [('1 วัน', a.chg_1d), ('5 วัน', a.chg_5d), ('20 วัน', a.chg_20d), ('63 วัน', a.chg_63d)] %}
            <div class="rounded bg-slate-950/50 py-1">
              <p class="font-mono text-[11px] font-semibold {% if val is none %}text-slate-600{% elif val >= 0 %}text-emerald-400{% else %}text-rose-400{% endif %}">
                {% if val is none %}—{% else %}{{ '%+.1f'|format(val) }}%{% endif %}
              </p>
              <p class="text-[9px] text-slate-600">{{ label }}</p>
            </div>
            {% endfor %}
          </div>

          {% if a.z is not none %}
          <div class="mt-2.5">
            <div class="flex items-center justify-between text-[10px] text-slate-500">
              <span>ความผิดปกติวันล่าสุด (z-score)</span>
              <span class="font-mono font-bold {{ st.text }}">{{ '%+.2f'|format(a.z) }} σ</span>
            </div>
            <div class="relative mt-1 h-1.5 rounded-full bg-slate-800">
              <div class="absolute inset-y-0 left-1/2 w-px bg-slate-600"></div>
              {% set pct = (a.z / 4 * 50) %}
              {% set pct = 50 if pct > 50 else (-50 if pct < -50 else pct) %}
              <div class="absolute inset-y-0 rounded-full {% if a.z >= 0 %}bg-emerald-400{% else %}bg-rose-400{% endif %}"
                   style="{% if a.z >= 0 %}left:50%;width:{{ pct }}%{% else %}right:50%;width:{{ -pct }}%{% endif %}"></div>
            </div>
          </div>
          {% endif %}

          <ul class="mt-2.5 space-y-1 text-[10.5px] leading-relaxed text-slate-400">
            {% for r in a.reasons %}<li class="flex gap-1.5"><span class="{{ st.text }}">▸</span><span>{{ r }}</span></li>{% endfor %}
          </ul>

          <details class="mt-2 border-t border-slate-800/70 pt-2">
            <summary class="text-[10px] text-slate-500 hover:text-slate-300">ทำไมต้องดูตัวนี้ + แหล่งข้อมูล ▾</summary>
            <p class="mt-1.5 text-[10.5px] leading-relaxed text-slate-400">{{ a.why_th }}</p>
            <p class="mt-1.5 text-[10px] text-slate-600">
              ที่มา: <a href="{{ a.source_home }}" target="_blank" rel="noopener" class="text-sky-400 underline decoration-dotted">{{ a.source_label }}</a>
              · สัญลักษณ์ <span class="font-mono">{{ a.source_symbol }}</span>
              · ใช้ข้อมูล {{ a.points }} วันทำการ
            </p>
          </details>

          {% else %}
          <div class="mt-3 rounded-lg border border-dashed border-slate-700 bg-slate-950/50 p-3">
            <p class="text-xs font-semibold text-slate-400">⚠️ ดึงข้อมูลไม่สำเร็จ — ไม่แสดงตัวเลขเดา</p>
            <p class="mt-1 break-words font-mono text-[10px] leading-relaxed text-slate-600">{{ a.error }}</p>
          </div>
          {% endif %}
        </div>
        {% endfor %}
      </div>
      {% endif %}
    {% endfor %}
  </section>

  <!-- ═══════════ 5. ผลกระทบต่อประเทศไทย ═══════════ -->
  <section>
    <div class="mb-3">
      <h2 class="text-lg font-bold" data-i18n="thailand">🇹🇭 แล้วกระทบประเทศไทยยังไง</h2>
      <p class="text-xs text-slate-400">
        แปลตัวเลขโลกให้เป็นเรื่องใกล้ตัว — ราคาทองที่เราซื้อขายกันจริง ค่าไฟ ค่าน้ำมัน และกำลังซื้อของลูกค้าต่างชาติ
      </p>
    </div>

    <!-- 5.1 ทองคำไทย -->
    <div class="card mb-4 rounded-2xl border border-amber-500/30 bg-gradient-to-br from-amber-500/10 to-slate-900/50 p-5">
      {% if data.thailand.gold %}
      {% set g = data.thailand.gold %}
      <div class="flex flex-wrap items-start gap-5">
        <div>
          <p class="text-xs font-semibold text-amber-300">🥇 {{ g.name_th }}</p>
          <p class="mt-1 font-mono text-3xl font-extrabold text-white">
            {{ '{:,.0f}'.format(g.last) }} <span class="text-base font-normal text-slate-400">บาท</span>
          </p>
          <p class="text-[11px] text-slate-500">อ้างอิงราคาปิด {{ g.last_date }}</p>
        </div>

        <div class="grid grid-cols-4 gap-2 text-center">
          {% for label, val in [('1 วัน', g.chg_1d), ('5 วัน', g.chg_5d), ('20 วัน', g.chg_20d), ('63 วัน', g.chg_63d)] %}
          <div class="rounded-lg bg-slate-950/50 px-3 py-1.5">
            <p class="font-mono text-sm font-bold {% if val is none %}text-slate-600{% elif val >= 0 %}text-emerald-400{% else %}text-rose-400{% endif %}">
              {% if val is none %}—{% else %}{{ '%+.1f'|format(val) }}%{% endif %}
            </p>
            <p class="text-[10px] text-slate-500">{{ label }}</p>
          </div>
          {% endfor %}
        </div>

        <div class="ml-auto text-right">
          <span class="rounded-full px-2.5 py-1 text-[11px] font-bold {{ level_style[g.level].badge }}">{{ g.level_th }}</span>
          {% if g.z is not none %}
          <p class="mt-1 font-mono text-[11px] text-slate-400">z = {{ '%+.2f'|format(g.z) }} σ</p>
          {% endif %}
        </div>
      </div>

      <ul class="mt-3 space-y-1 text-[11.5px] leading-relaxed text-slate-300">
        {% for r in g.reasons %}<li>▸ {{ r }}</li>{% endfor %}
      </ul>

      <div class="mt-3 rounded-lg border border-amber-500/25 bg-slate-950/50 p-3 text-[11px] leading-relaxed text-slate-400">
        <p><b class="text-amber-300">สูตรที่ใช้:</b> <span class="font-mono">{{ g.formula }}</span></p>
        <p class="mt-1"><b class="text-slate-300">ค่าที่ใส่เข้าไป:</b> <span class="font-mono">{{ g.inputs }}</span></p>
        <p class="mt-2 text-amber-200/80">
          ⚠️ นี่คือราคา<b>ที่คำนวณจากทองคำโลก</b> ไม่ใช่ราคาประกาศของสมาคมค้าทองคำ
          ราคาหน้าร้านจริงจะต่างจากนี้เพราะมีค่ากำเหน็จ ส่วนต่างซื้อ-ขาย และอุปสงค์ในประเทศ
          — เช็คราคาประกาศจริงที่
          <a href="https://www.goldtraders.or.th/" target="_blank" rel="noopener" class="text-amber-300 underline">สมาคมค้าทองคำ</a>
        </p>
      </div>
      {% else %}
      <p class="text-sm text-slate-400">🥇 ราคาทองคำไทย (คำนวณ)</p>
      <p class="mt-2 rounded-lg border border-dashed border-slate-700 p-3 text-xs text-slate-500">
        ⚠️ {{ data.thailand.gold_error }} — จึงไม่แสดงตัวเลข เพราะการเดาราคาทองอันตรายกว่าการไม่บอก
      </p>
      {% endif %}
    </div>

    <!-- 5.2 กำลังซื้อลูกค้าต่างชาติ -->
    <div class="card mb-4 rounded-2xl border border-slate-800 bg-slate-900/50 p-5">
      <div class="flex flex-wrap items-end justify-between gap-3">
        <div>
          <h3 class="text-sm font-bold text-slate-100">💱 กำลังซื้อของลูกค้าต่างชาติ (มุมอสังหาฯ)</h3>
          <p class="text-xs text-slate-400">
            สมมติทรัพย์ราคา <b class="text-slate-200"><span id="propLabel">{{ '{:,.0f}'.format(data.thailand.property_thb) }}</span> บาท</b>
            ราคาไทยไม่เปลี่ยนเลย — แต่ลูกค้าต่างชาติต้องควักเงินสกุลตัวเองเท่าไหร่
          </p>
        </div>
        <label class="flex items-center gap-2 text-xs">
          <span class="text-slate-400">ใส่ราคาทรัพย์จริง</span>
          <input id="propInput" type="number" value="{{ data.thailand.property_thb }}" step="500000" min="100000"
                 oninput="recalcFX()"
                 class="w-40 rounded-lg border border-slate-700 bg-slate-950 px-2 py-1.5 font-mono text-slate-200">
          <span class="text-slate-500">บาท</span>
        </label>
      </div>

      {% if data.thailand.fx_rows %}
      <div class="mt-3 overflow-x-auto">
        <table class="w-full min-w-[640px] text-sm">
          <thead>
            <tr class="border-b border-slate-800 text-[11px] uppercase tracking-wider text-slate-500">
              <th class="py-2 text-left font-semibold">ลูกค้า</th>
              <th class="py-2 text-right font-semibold">อัตราแลกเปลี่ยน</th>
              <th class="py-2 text-right font-semibold">ต้องจ่ายวันนี้</th>
              <th class="py-2 text-right font-semibold">เทียบ 20 วันก่อน</th>
              <th class="py-2 text-right font-semibold">เทียบ 63 วันก่อน</th>
              <th class="py-2 text-left font-semibold">แปลว่า</th>
            </tr>
          </thead>
          <tbody class="divide-y divide-slate-800/70">
            {% for r in data.thailand.fx_rows %}
            <tr>
              {% if r.ok %}
              <td class="py-2.5">
                <span class="mr-1">{{ r.flag }}</span>
                <b class="font-mono">{{ r.code }}</b>
                <span class="block text-[10px] text-slate-500">{{ r.who }}</span>
              </td>
              <td class="py-2.5 text-right font-mono text-xs text-slate-400">{{ '%.4f'|format(r.rate) }} บาท</td>
              <td class="py-2.5 text-right font-mono font-bold text-slate-100"
                  data-fx-code="{{ r.code }}" data-fx-rate="{{ r.rate }}">{{ '{:,.0f}'.format(r.cost_now) }} {{ r.code }}</td>
              {% for key in ['chg_20d', 'chg_63d'] %}
              <td class="py-2.5 text-right font-mono text-xs">
                {% set v = r[key] %}
                {% if v is none %}<span class="text-slate-600">—</span>
                {% else %}<span class="{% if v <= 0 %}text-emerald-400{% else %}text-rose-400{% endif %}">{{ '%+.1f'|format(v) }}%</span>{% endif %}
              </td>
              {% endfor %}
              <td class="py-2.5 text-left text-[11px] leading-tight">
                {% set v = r.chg_63d %}
                {% if v is none %}<span class="text-slate-600">ข้อมูลย้อนหลังไม่พอ</span>
                {% elif v <= -2 %}<span class="text-emerald-300">ถูกลง {{ '%.1f'|format(-v) }}% ใน 3 เดือน — จังหวะดีสำหรับผู้ซื้อกลุ่มนี้</span>
                {% elif v >= 2 %}<span class="text-rose-300">แพงขึ้น {{ '%.1f'|format(v) }}% ใน 3 เดือน — ผู้ซื้อกลุ่มนี้จะลังเลขึ้น</span>
                {% else %}<span class="text-slate-500">แทบไม่เปลี่ยน ({{ '%+.1f'|format(v) }}%)</span>{% endif %}
              </td>
              {% else %}
              <td class="py-2.5"><span class="mr-1">{{ r.flag }}</span><b class="font-mono">{{ r.code }}</b></td>
              <td colspan="5" class="py-2.5 text-xs text-slate-500">⚠️ {{ r.error }} — ไม่แสดงตัวเลขเดา</td>
              {% endif %}
            </tr>
            {% endfor %}
          </tbody>
        </table>
      </div>
      <p class="mt-2 text-[10px] leading-relaxed text-slate-500">
        คำนวณจากอัตราแลกเปลี่ยนตลาดโลก (cross rate) ไม่รวมสเปรดของธนาคารและค่าธรรมเนียมโอนเงินระหว่างประเทศ
        ซึ่งของจริงจะกินอีกราว 1–3% · “20/63 วัน” คือวันทำการ ≈ 1 เดือน และ ≈ 3 เดือน
        · อัตราอ้างอิงทางการดูที่ <a href="https://www.bot.or.th/th/statistics/exchange-rate.html" target="_blank" rel="noopener" class="text-sky-400 underline">ธปท.</a>
      </p>
      {% else %}
      <p class="mt-3 rounded-lg border border-dashed border-slate-700 p-3 text-xs text-slate-500">⚠️ {{ data.thailand.fx_error }}</p>
      {% endif %}
    </div>

    <!-- 5.3 กลไกส่งผ่านอื่น ๆ -->
    <div class="grid gap-3 sm:grid-cols-2 lg:grid-cols-3">
      {% for c in data.thailand.cards %}
      <div class="card rounded-2xl border border-slate-800 bg-slate-900/50 p-4">
        <div class="flex items-start gap-2">
          <span class="text-xl">{{ c.icon }}</span>
          <h4 class="flex-1 text-sm font-bold text-slate-100">{{ c.title }}</h4>
          {% if c.ok %}
          <span class="rounded-full px-2 py-0.5 text-[10px] font-bold {{ level_style[c.level].badge }}">{{ c.level_th }}</span>
          {% endif %}
        </div>

        {% if c.ok %}
        <div class="mt-2 flex items-end gap-3">
          <div>
            <p class="font-mono text-xl font-bold text-white">{{ c.value }}</p>
            <p class="text-[10px] text-slate-500">{{ c.asset_name }} · {{ c.unit }} · {{ c.last_date }}</p>
          </div>
          <div class="ml-auto text-right text-[11px]">
            {% for label, v in [('5 วัน', c.chg_5d), ('20 วัน', c.chg_20d)] %}
            <p class="font-mono {% if v is none %}text-slate-600{% elif v >= 0 %}text-emerald-400{% else %}text-rose-400{% endif %}">
              {{ label }} {% if v is none %}—{% else %}{{ '%+.1f'|format(v) }}%{% endif %}
            </p>
            {% endfor %}
          </div>
        </div>
        {% else %}
        <p class="mt-2 rounded border border-dashed border-slate-700 p-2 text-[10px] text-slate-500">⚠️ ดึงข้อมูลไม่ได้: {{ c.error }}</p>
        {% endif %}

        <p class="mt-2.5 text-[11.5px] leading-relaxed text-slate-400">{{ c.mech }}</p>
        <p class="mt-2 border-t border-slate-800 pt-2 text-[10px] text-slate-500">
          ตัวเลขจริงฝั่งไทยต้องดูที่
          <a href="{{ c.source_url }}" target="_blank" rel="noopener" class="text-sky-400 underline decoration-dotted">{{ c.source_name }}</a>
        </p>
      </div>
      {% endfor %}
    </div>

    <p class="mt-3 rounded-xl border border-slate-800 bg-slate-900/40 p-3 text-[11px] leading-relaxed text-slate-500">
      📌 ข้อความในส่วนนี้อธิบาย <b class="text-slate-400">กลไกการส่งผ่านผลกระทบ</b> ที่เป็นความรู้ทั่วไปทางเศรษฐกิจ
      ไม่ใช่การพยากรณ์ว่าราคาจะขึ้นหรือลงเท่าไหร่ และไม่ใช่คำแนะนำการลงทุน
      ขนาดและจังหวะของผลกระทบจริงขึ้นกับนโยบายรัฐ กองทุนน้ำมัน และค่า Ft ที่ประกาศเป็นรอบ ๆ
    </p>
  </section>

  <!-- ═══════════ 6. น่าสนใจแต่ยังเชื่อไม่ได้ ═══════════ -->
  <section>
    <div class="mb-3">
      <h2 class="text-lg font-bold text-amber-300" data-i18n="unverified">⚠️ น่าสนใจ แต่ยังเชื่อไม่ได้</h2>
      <p class="text-xs text-slate-400">
        ข่าวที่มาจากแหล่งที่ต้องระวัง หรือใช้คำกำกวมแบบ “มีรายงานว่า / อ้างว่า”
        — เก็บไว้ดูเป็นสัญญาณล่วงหน้าได้ แต่<b class="text-amber-300">ห้ามเอาไปตัดสินใจก่อนมีแหล่งระดับ A ยืนยัน</b>
      </p>
    </div>

    {% if data.unverified %}
    <div class="grid gap-2.5 md:grid-cols-2">
      {% for n in data.unverified %}
      <div class="card rounded-xl border border-amber-500/30 bg-amber-500/[0.06] p-3.5">
        <div class="flex flex-wrap items-center gap-1.5 text-[10px]">
          <span class="rounded border px-1.5 py-px font-semibold {{ data.tiers[n.tier].cls }}">
            {{ n.source }} · ระดับ {{ n.tier }}
          </span>
          <span class="text-slate-500">{{ n.ago }}</span>
          <span class="ml-auto rounded bg-slate-800 px-1.5 py-px font-mono text-slate-400">น้ำหนักข่าว {{ n.weight }}</span>
        </div>

        <a href="{{ n.link }}" target="_blank" rel="noopener"
           class="mt-1.5 block text-sm font-semibold leading-snug text-slate-100 hover:text-amber-300">{{ n.title }}</a>

        <div class="mt-2 space-y-1 rounded-lg bg-slate-950/60 p-2">
          <p class="text-[10px] font-bold uppercase tracking-wider text-amber-400">ทำไมยังเชื่อไม่ได้</p>
          {% for r in n.warn_reasons %}
          <p class="text-[11px] leading-relaxed text-slate-400">• {{ r }}</p>
          {% endfor %}
        </div>

        <p class="mt-2 text-[10px] text-slate-500">
          🔍 วิธีเช็ก: เอาคำสำคัญในพาดหัวไปค้นในแหล่งระดับ A (BBC / UN / IAEA) ถ้าไม่มีใครรายงานตรงกันภายใน 24 ชม. ให้ถือว่ายังไม่จริง
        </p>
      </div>
      {% endfor %}
    </div>
    {% else %}
    <p class="rounded-xl border border-dashed border-slate-800 p-6 text-center text-sm text-slate-500">
      ตอนนี้ไม่มีข่าวกลุ่มนี้ที่น้ำหนักถึงเกณฑ์
    </p>
    {% endif %}
  </section>

  <!-- ═══════════ 7. แหล่งข้อมูลทั้งหมด ═══════════ -->
  <section>
    <h2 class="mb-1 text-lg font-bold" data-i18n="sources">🔗 แหล่งข้อมูลทั้งหมด และเกณฑ์ความน่าเชื่อถือ</h2>
    <p class="mb-3 text-xs text-slate-400">เปิดให้ตรวจสอบย้อนกลับได้ทุกแหล่ง รวมถึงแหล่งที่ดึงไม่สำเร็จในรอบนี้</p>

    <div class="mb-4 grid gap-2 sm:grid-cols-2 lg:grid-cols-4">
      {% for key, t in data.tiers.items() %}
      <div class="rounded-xl border p-3 {{ t.cls }}">
        <p class="text-xs font-bold">ระดับ {{ key }} — {{ t.label_th }}</p>
        <p class="mt-1 text-[11px] leading-relaxed opacity-80">{{ t.desc_th }}</p>
      </div>
      {% endfor %}
    </div>

    <div class="overflow-x-auto rounded-xl border border-slate-800">
      <table class="w-full min-w-[720px] text-xs">
        <thead class="bg-slate-900/60">
          <tr class="text-[10px] uppercase tracking-wider text-slate-500">
            <th class="px-3 py-2 text-left font-semibold">สถานะ</th>
            <th class="px-3 py-2 text-left font-semibold">ประเภท</th>
            <th class="px-3 py-2 text-left font-semibold">แหล่ง</th>
            <th class="px-3 py-2 text-left font-semibold">ระดับ</th>
            <th class="px-3 py-2 text-left font-semibold">หมายเหตุ / สิ่งที่ต้องระวัง</th>
            <th class="px-3 py-2 text-right font-semibold">รายการที่ได้</th>
          </tr>
        </thead>
        <tbody class="divide-y divide-slate-800/70">
          {% for s in data.sources %}
          <tr class="{% if not s.ok %}bg-rose-500/[0.04]{% endif %}">
            <td class="px-3 py-2">
              {% if s.ok %}<span class="rounded bg-emerald-500/15 px-1.5 py-0.5 text-[10px] font-semibold text-emerald-300">ใช้ได้</span>
              {% else %}<span class="rounded bg-rose-500/15 px-1.5 py-0.5 text-[10px] font-semibold text-rose-300">ล้มเหลว</span>{% endif %}
            </td>
            <td class="px-3 py-2 text-slate-500">{{ s.kind }}</td>
            <td class="px-3 py-2">
              <a href="{{ s.home }}" target="_blank" rel="noopener" class="font-semibold text-sky-400 hover:underline">{{ s.name }}</a>
            </td>
            <td class="px-3 py-2">
              <span class="rounded border px-1.5 py-px text-[10px] font-semibold {{ data.tiers[s.tier].cls }}">{{ s.tier }}</span>
            </td>
            <td class="px-3 py-2 text-slate-400">
              {{ s.note_th }}
              {% if s.error %}<span class="mt-0.5 block font-mono text-[10px] text-rose-400/80">{{ s.error }}</span>{% endif %}
            </td>
            <td class="px-3 py-2 text-right font-mono text-slate-400">{{ s.count }}</td>
          </tr>
          {% endfor %}
        </tbody>
      </table>
    </div>
  </section>
</main>

<footer class="mt-10 border-t border-slate-800 bg-slate-950/80">
  <div class="mx-auto max-w-7xl px-4 py-6 text-[11px] leading-relaxed text-slate-500 space-y-2">
    <p>
      <b class="text-slate-400">ข้อจำกัดที่ต้องรู้ก่อนใช้:</b>
      เครื่องมือนี้อ่านข่าวด้วยการจับคำสำคัญ ไม่ได้เข้าใจบริบทเหมือนคน จึงมีทั้งการเตือนเกินจริงและการพลาดข่าวสำคัญได้
      ราคาสินทรัพย์เป็น<b class="text-slate-400">ราคาปิดรายวัน ไม่ใช่ราคาเรียลไทม์</b>
      และดัชนีความตึงเครียดเป็นการให้คะแนนของเครื่องมือนี้เอง ไม่ใช่มาตรฐานที่ใครยอมรับ
    </p>
    <p>
      ทุกอย่างในหน้านี้เป็นข้อมูลเพื่อการติดตามสถานการณ์เท่านั้น
      <b class="text-slate-400">ไม่ใช่คำแนะนำการลงทุน</b> และไม่ใช่การพยากรณ์สงคราม
      ก่อนตัดสินใจใด ๆ ให้กดเข้าไปอ่านต้นทางที่ลิงก์ไว้ทุกจุด
    </p>
    <p class="pt-2 text-slate-600">
      อัปเดตล่าสุด {{ data.generated_th }} · ใช้เฉพาะแหล่งข้อมูลสาธารณะที่ไม่มีค่าใช้จ่าย ·
      <a href="{% if static_mode %}snapshot.json{% else %}/api/snapshot{% endif %}" class="text-sky-500/70 hover:underline">ดูข้อมูลดิบเป็น JSON</a>
    </p>
  </div>
</footer>

<script>
// รีเฟรชอัตโนมัติทุก 10 นาที (ตรงกับอายุแคชฝั่งเซิร์ฟเวอร์ จึงไม่ยิงแหล่งข้อมูลถี่เกินจำเป็น)
setTimeout(function () { location.reload(); }, 10 * 60 * 1000);

// คำนวณกำลังซื้อลูกค้าต่างชาติใหม่ทันทีที่พิมพ์ — ทำฝั่งเบราว์เซอร์ จึงใช้ได้ทั้งบนเซิร์ฟเวอร์และหน้าเว็บนิ่ง
//   เงินที่ลูกค้าต้องจ่าย = ราคาทรัพย์ (บาท) ÷ อัตราแลกเปลี่ยน (บาทต่อ 1 หน่วยสกุลนั้น)
// คอลัมน์ % ไม่ต้องคำนวณใหม่ เพราะเป็นอัตราส่วนระหว่างอัตราแลกเปลี่ยน ไม่ขึ้นกับราคาทรัพย์
function recalcFX() {
  var input = document.getElementById("propInput");
  if (!input) return;
  var label = document.getElementById("propLabel");
  var baht = parseFloat(input.value);
  if (!isFinite(baht) || baht <= 0) {
    if (label) label.textContent = "—";
    return;
  }
  if (label) label.textContent = Math.round(baht).toLocaleString("en-US");
  document.querySelectorAll("[data-fx-code]").forEach(function (td) {
    var rate = parseFloat(td.dataset.fxRate);
    if (!isFinite(rate) || rate <= 0) return;
    td.textContent = Math.round(baht / rate).toLocaleString("en-US") + " " + td.dataset.fxCode;
  });
}

// สลับภาษาเฉพาะป้ายกำกับหลัก (เนื้อข่าวคงภาษาต้นทางเสมอ)
var I18N = {
  brand:      { th: "ศูนย์เฝ้าระวังสถานการณ์โลก", en: "World Watch" },
  tagline:    { th: "จุดร้อนทั่วโลก · ความผิดปกติของราคาสินทรัพย์ · แล้วไทยกระทบอะไร",
                en: "Global flashpoints · Abnormal asset moves · What it means for Thailand" },
  updated:    { th: "อัปเดตล่าสุด", en: "Updated" },
  refresh:    { th: "ดึงข้อมูลใหม่", en: "Refresh" },
  gaugeTitle: { th: "ระดับความตึงเครียดของโลก", en: "Global tension level" },
  theatres:   { th: "🌍 จุดที่ต้องจับตา", en: "🌍 Flashpoints to watch" },
  watch:      { th: "🚨 แจ้งเตือนให้จับตา", en: "🚨 Escalation alerts" },
  assets:     { th: "📊 การเคลื่อนไหวผิดปกติของทองคำและสินทรัพย์อื่น",
                en: "📊 Abnormal moves in gold and other assets" },
  thailand:   { th: "🇹🇭 แล้วกระทบประเทศไทยยังไง", en: "🇹🇭 Impact on Thailand" },
  unverified: { th: "⚠️ น่าสนใจ แต่ยังเชื่อไม่ได้", en: "⚠️ Interesting but unverified" },
  sources:    { th: "🔗 แหล่งข้อมูลทั้งหมด และเกณฑ์ความน่าเชื่อถือ", en: "🔗 All sources & credibility tiers" }
};
var lang = localStorage.getItem("ww_lang") || "th";
function applyLang() {
  document.querySelectorAll("[data-i18n]").forEach(function (el) {
    var entry = I18N[el.dataset.i18n];
    if (entry && entry[lang]) el.textContent = entry[lang];
  });
  document.getElementById("langBtn").textContent = lang === "th" ? "EN" : "ไทย";
}
function toggleLang() {
  lang = lang === "th" ? "en" : "th";
  localStorage.setItem("ww_lang", lang);
  applyLang();
}
applyLang();
</script>
</body>
</html>
"""

ERROR_PAGE = r"""<!doctype html>
<html lang="th"><head><meta charset="utf-8"><title>เกิดข้อผิดพลาด</title>
<script src="https://cdn.tailwindcss.com"></script></head>
<body class="bg-slate-950 text-slate-200 p-8 font-sans">
  <div class="mx-auto max-w-3xl rounded-2xl border border-rose-500/40 bg-rose-500/10 p-6">
    <h1 class="text-xl font-bold text-rose-300">⚠️ ประกอบข้อมูลไม่สำเร็จ</h1>
    <p class="mt-2 text-sm text-slate-300">
      ระบบเลือกที่จะไม่แสดงข้อมูลเดา จึงหยุดไว้ตรงนี้ · สาเหตุที่แท้จริงอยู่ด้านล่าง
    </p>
    <pre class="mt-4 overflow-x-auto rounded-lg bg-slate-950 p-4 text-xs text-rose-200">{{ detail }}</pre>
    <a href="/?refresh=1" class="mt-4 inline-block rounded-lg bg-sky-500 px-4 py-2 text-sm font-semibold text-slate-950">ลองใหม่</a>
  </div>
</body></html>
"""


# =============================================================================
# 10. Flask
# =============================================================================

app = Flask(__name__)


def _property_arg() -> int:
    try:
        val = int(request.args.get("property", DEFAULT_PROPERTY_THB))
        return max(500_000, min(val, 2_000_000_000))
    except (TypeError, ValueError):
        return DEFAULT_PROPERTY_THB


@app.route("/")
def index():
    try:
        data = get_snapshot(force=request.args.get("refresh") == "1",
                            property_thb=_property_arg())
        return render_template_string(PAGE, data=data, level_style=LEVEL_STYLE,
                                      title_th=APP_TITLE_TH, title_en=APP_TITLE_EN,
                                      static_mode=False)
    except Exception:                                    # noqa: BLE001
        return render_template_string(ERROR_PAGE, detail=traceback.format_exc()), 500


def json_safe(obj):
    """ตัดของที่ JSON แปลงไม่ได้ออก (datetime, NaN) และตัดคีย์ที่ใช้เฉพาะภายใน"""
    if isinstance(obj, dict):
        return {k: json_safe(v) for k, v in obj.items() if k not in ("published", "sort_key")}
    if isinstance(obj, list):
        return [json_safe(v) for v in obj]
    if isinstance(obj, datetime):
        return obj.isoformat()
    if isinstance(obj, float) and (math.isnan(obj) or math.isinf(obj)):
        return None
    return obj


@app.route("/api/snapshot")
def api_snapshot():
    """ข้อมูลดิบทั้งหมดเป็น JSON — เอาไปต่อยอด เช่น ส่งเข้าไลน์ตอนคะแนนพุ่ง"""
    data = get_snapshot(force=request.args.get("refresh") == "1",
                        property_thb=_property_arg())
    return jsonify(json_safe(data))


@app.route("/health")
def health():
    return jsonify({"status": "ok", "cached": _cache["data"] is not None,
                    "cache_age_sec": int(time.time() - _cache["ts"]) if _cache["ts"] else None})


# =============================================================================
# 11. โหมดสร้างหน้าเว็บนิ่ง (สำหรับ GitHub Pages)
# =============================================================================

def build_static(out_dir: str, property_thb: int = DEFAULT_PROPERTY_THB) -> dict:
    """
    เรนเดอร์หน้าเว็บเป็นไฟล์นิ่ง index.html + snapshot.json

    ใช้โค้ดคำนวณและเทมเพลตชุดเดียวกับตอนรันเป็นเซิร์ฟเวอร์ทุกบรรทัด
    ต่างแค่ซ่อนปุ่มที่ต้องพึ่งเซิร์ฟเวอร์ (ปุ่มดึงข้อมูลใหม่) เพราะหน้านิ่งกดแล้วไม่มีอะไรเกิดขึ้น
    ส่วนเครื่องคำนวณกำลังซื้อยังใช้ได้ปกติ เพราะย้ายไปคำนวณฝั่งเบราว์เซอร์แล้ว
    """
    data = get_snapshot(force=True, property_thb=property_thb)
    with app.app_context():
        html = render_template_string(PAGE, data=data, level_style=LEVEL_STYLE,
                                      title_th=APP_TITLE_TH, title_en=APP_TITLE_EN,
                                      static_mode=True)

    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, "index.html"), "w", encoding="utf-8") as fh:
        fh.write(html)
    with open(os.path.join(out_dir, "snapshot.json"), "w", encoding="utf-8") as fh:
        json.dump(json_safe(data), fh, ensure_ascii=False, indent=1)
    # .nojekyll บอก GitHub Pages ว่าไม่ต้องเอา Jekyll มายุ่งกับไฟล์ของเรา
    with open(os.path.join(out_dir, ".nojekyll"), "w", encoding="utf-8"):
        pass
    return data


if __name__ == "__main__":
    # คอนโซล Windows ปกติเป็น cp874/cp1252 พิมพ์ภาษาไทยแล้วพัง — บังคับเป็น UTF-8 ก่อน
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    except Exception:                                    # noqa: BLE001
        pass

    # ---- โหมดสร้างไฟล์นิ่ง:  python app.py --build <โฟลเดอร์>  ----
    if "--build" in sys.argv:
        pos = sys.argv.index("--build")
        out_dir = sys.argv[pos + 1] if len(sys.argv) > pos + 1 else "site"
        print(f"กำลังสร้างหน้าเว็บนิ่งลงโฟลเดอร์ {out_dir}/ ...")
        snap = build_static(out_dir)
        st = snap["stats"]
        print(f"  แหล่งข่าว {st['feeds_ok']}/{st['feeds_total']}"
              f" · ราคา {st['assets_ok']}/{st['assets_total']}"
              f" · ข่าว {st['news_total']} ชิ้น"
              f" · ความตึงเครียด {snap['tension']['score']} ({snap['tension']['label']})")
        # ถ้าดึงอะไรไม่ได้เลย หน้าที่ได้จะว่างเปล่าไม่มีประโยชน์ — ให้ถือว่าล้มเหลว ดีกว่าเผยแพร่หน้าเปล่า
        if st["assets_ok"] == 0 or st["feeds_ok"] == 0:
            print("ล้มเหลว: ดึงข้อมูลไม่ได้เลยสักแหล่ง จึงไม่เผยแพร่หน้าเปล่า")
            sys.exit(1)
        print(f"เสร็จแล้ว → {out_dir}/index.html")
        sys.exit(0)

    # ---- โหมดเซิร์ฟเวอร์ ----
    # บนเครื่องตัวเองผูกกับ 127.0.0.1 (คนอื่นในวงเน็ตเข้าไม่ได้)
    # แต่ถ้าโฮสต์ตั้ง PORT ให้ (Render / Cloud Run) ต้องเปิดเป็น 0.0.0.0 ไม่งั้นเข้าไม่ถึง
    env_port = os.environ.get("PORT")
    host = os.environ.get("HOST", "0.0.0.0" if env_port else "127.0.0.1")
    port = int(env_port or 5000)

    print("=" * 68)
    print(" World Watch — ศูนย์เฝ้าระวังสถานการณ์โลก")
    print(f" เปิดที่  http://{'127.0.0.1' if host == '127.0.0.1' else host}:{port}")
    print(" โหลดครั้งแรกใช้เวลาราว 10-25 วินาที (ดึงข่าวและราคาสด)")
    print(" สร้างหน้าเว็บนิ่งแทน:  python app.py --build site")
    print("=" * 68)
    app.run(host=host, port=port, debug=False)
