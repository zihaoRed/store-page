(function () {
  'use strict';

  const wrap = document.getElementById('canvasWrap');
  const canvasEl = document.getElementById('c');
  const fileInput = document.getElementById('fileInput');
  const btnUndo = document.getElementById('btnUndo');
  const btnRedo = document.getElementById('btnRedo');
  const btnClear = document.getElementById('btnClear');
  const btnGrid = document.getElementById('btnGrid');
  const btnCalibrate = document.getElementById('btnCalibrate');
  const btnExport = document.getElementById('btnExport');
  const brushColor = document.getElementById('brushColor');
  const brushWidth = document.getElementById('brushWidth');
  const brushWidthVal = document.getElementById('brushWidthVal');
  const selLenBlock = document.getElementById('selLenBlock');
  const totalLenBlock = document.getElementById('totalLenBlock');
  const calibNote = document.getElementById('calibNote');
  const btnToLine = document.getElementById('btnToLine');
  const btnToCurve = document.getElementById('btnToCurve');
  const btnUnfoldStraight = document.getElementById('btnUnfoldStraight');
  const btnRestoreUnfold = document.getElementById('btnRestoreUnfold');
  const btnDeleteSel = document.getElementById('btnDeleteSel');
  const panHint = document.getElementById('panHint');
  const toolBtns = document.querySelectorAll('.tool-btn');

  const EXTRA_PROPS = [
    'isBackground',
    'isUserStroke',
    'isCurveGroup',
    'curveHandle',
    'strokeUniform',
    'isChordCompareLine',
    'isArcUnfoldLine',
    'isUnfoldDemoLine',
    'strokeDashArray',
  ];

  let pxPerCm = null;
  /** 点「标定」时的 canvas.getZoom()，用于「屏上约」按缩放比修正 */
  let calibrationZoom = 1;
  /** 未标定时用屏幕参考比例换算公制（约 96dpi：1 英寸=96px，1 英寸=2.54 厘米） */
  const DEFAULT_PX_PER_CM = 96 / 2.54;

  let tool = 'brush';
  let linePoints = [];
  let lineSegments = [];
  let spaceDown = false;
  let isPanning = false;
  let panLast = null;

  const history = [];
  let historyIndex = -1;
  const MAX_HISTORY = 40;

  let unfoldAnimating = false;
  /** 拉直前克隆的原始对象（不在画布上），与 unfoldRestoreMorphRef 成对使用 */
  let unfoldRestoreClone = null;
  let unfoldRestoreMorphRef = null;

  function clearUnfoldBackup() {
    unfoldRestoreClone = null;
    unfoldRestoreMorphRef = null;
  }

  function hasUnfoldRestore() {
    if (!unfoldRestoreClone || !unfoldRestoreMorphRef) return false;
    if (canvas.getObjects().indexOf(unfoldRestoreMorphRef) < 0) {
      clearUnfoldBackup();
      return false;
    }
    return true;
  }

  function resizeCanvas() {
    const w = wrap.clientWidth;
    const h = wrap.clientHeight;
    canvas.setDimensions({ width: w, height: h });
    canvas.requestRenderAll();
  }

  const canvas = new fabric.Canvas('c', {
    selection: true,
    preserveObjectStacking: true,
    stopContextMenu: true,
    fireRightClick: false,
  });

  resizeCanvas();
  window.addEventListener('resize', resizeCanvas);

  canvas.freeDrawingBrush = new fabric.PencilBrush(canvas);
  canvas.freeDrawingBrush.color = brushColor.value;
  canvas.freeDrawingBrush.width = parseInt(brushWidth.value, 10);
  canvas.isDrawingMode = true;

  function setBrushFromUI() {
    canvas.freeDrawingBrush.color = brushColor.value;
    canvas.freeDrawingBrush.width = parseInt(brushWidth.value, 10);
  }

  brushColor.addEventListener('input', setBrushFromUI);
  brushWidth.addEventListener('input', function () {
    brushWidthVal.textContent = brushWidth.value;
    setBrushFromUI();
  });

  function lineAbsEndpoints(line, parentMat) {
    const m = parentMat
      ? fabric.util.multiplyTransformMatrices(parentMat, line.calcTransformMatrix())
      : line.calcTransformMatrix();
    const a = fabric.util.transformPoint(new fabric.Point(line.x1, line.y1), m);
    const b = fabric.util.transformPoint(new fabric.Point(line.x2, line.y2), m);
    return { a, b };
  }

  function lineLengthPx(line, canvasMat) {
    const { a, b } = lineAbsEndpoints(line, canvasMat || undefined);
    return Math.hypot(b.x - a.x, b.y - a.y);
  }

  function pathPixelLengthWithMatrix(pathObj, m) {
    const segs = pathObj.path;
    if (!segs || !segs.length) return 0;
    let len = 0;
    let cx = 0;
    let cy = 0;
    let sx = 0;
    let sy = 0;

    function map(x, y) {
      return fabric.util.transformPoint(new fabric.Point(x, y), m);
    }

    function dist(p1, p2) {
      return Math.hypot(p2.x - p1.x, p2.y - p1.y);
    }

    function quadLenP(p0, p1, p2) {
      let px = p0.x;
      let py = p0.y;
      let acc = 0;
      const steps = 24;
      for (let i = 1; i <= steps; i++) {
        const t = i / steps;
        const ox =
          (1 - t) * (1 - t) * p0.x + 2 * (1 - t) * t * p1.x + t * t * p2.x;
        const oy =
          (1 - t) * (1 - t) * p0.y + 2 * (1 - t) * t * p1.y + t * t * p2.y;
        acc += dist({ x: px, y: py }, { x: ox, y: oy });
        px = ox;
        py = oy;
      }
      return acc;
    }

    for (let i = 0; i < segs.length; i++) {
      const sub = segs[i];
      const cmd = sub[0];
      if (cmd === 'M') {
        const p = map(sub[1], sub[2]);
        cx = p.x;
        cy = p.y;
        sx = cx;
        sy = cy;
      } else if (cmd === 'L') {
        const p = map(sub[1], sub[2]);
        len += dist({ x: cx, y: cy }, p);
        cx = p.x;
        cy = p.y;
      } else if (cmd === 'Q') {
        const p1 = map(sub[1], sub[2]);
        const p2 = map(sub[3], sub[4]);
        len += quadLenP({ x: cx, y: cy }, p1, p2);
        cx = p2.x;
        cy = p2.y;
      } else if (cmd === 'C') {
        const p1 = map(sub[1], sub[2]);
        const p2 = map(sub[3], sub[4]);
        const p3 = map(sub[5], sub[6]);
        let px = cx;
        let py = cy;
        const steps = 32;
        for (let s = 1; s <= steps; s++) {
          const t = s / steps;
          const t1 = 1 - t;
          const ox =
            t1 * t1 * t1 * cx +
            3 * t1 * t1 * t * p1.x +
            3 * t1 * t * t * p2.x +
            t * t * t * p3.x;
          const oy =
            t1 * t1 * t1 * cy +
            3 * t1 * t1 * t * p1.y +
            3 * t1 * t * t * p2.y +
            t * t * t * p3.y;
          len += Math.hypot(ox - px, oy - py);
          px = ox;
          py = oy;
        }
        cx = p3.x;
        cy = p3.y;
      } else if (cmd === 'Z' || cmd === 'z') {
        len += dist({ x: cx, y: cy }, { x: sx, y: sy });
        cx = sx;
        cy = sy;
      }
    }
    return len;
  }

  function objectPixelLength(obj) {
    if (!obj) return 0;
    if (obj.isBackground) return 0;

    if (obj.type === 'line') {
      return lineLengthPx(obj, null);
    }

    if (obj.type === 'path') {
      return pathPixelLengthWithMatrix(obj, obj.calcTransformMatrix());
    }

    if (obj.type === 'polyline') {
      const pts = obj.points || [];
      const m = obj.calcTransformMatrix();
      let plen = 0;
      for (let i = 0; i < pts.length - 1; i++) {
        const a = fabric.util.transformPoint(new fabric.Point(pts[i].x, pts[i].y), m);
        const b = fabric.util.transformPoint(new fabric.Point(pts[i + 1].x, pts[i + 1].y), m);
        plen += Math.hypot(b.x - a.x, b.y - a.y);
      }
      return plen;
    }

    if (obj.type === 'group' && obj.getObjects) {
      const gMat = obj.calcTransformMatrix();
      return obj.getObjects().reduce(function (acc, o) {
        if (o.type === 'line') {
          const m = fabric.util.multiplyTransformMatrices(gMat, o.calcTransformMatrix());
          return acc + lineLengthPx(o, m);
        }
        if (o.type === 'path') {
          const m = fabric.util.multiplyTransformMatrices(gMat, o.calcTransformMatrix());
          return acc + pathPixelLengthWithMatrix(o, m);
        }
        if (o.type === 'circle' && o.curveHandle) return acc;
        return acc;
      }, 0);
    }

    return 0;
  }

  function isCalibrated() {
    return pxPerCm != null && pxPerCm > 0;
  }

  function effectivePxPerCm() {
    return isCalibrated() ? pxPerCm : DEFAULT_PX_PER_CM;
  }

  function appendFourMetricRows(container, cmLen) {
    const rows = [
      { name: '米', val: (cmLen / 100).toFixed(4) },
      { name: '分米', val: (cmLen / 10).toFixed(3) },
      { name: '厘米', val: cmLen.toFixed(2) },
      { name: '毫米', val: (cmLen * 10).toFixed(1) },
    ];
    rows.forEach(function (r) {
      const line = document.createElement('div');
      line.className = 'unit-line';
      const val = document.createElement('span');
      val.className = 'unit-val';
      val.textContent = r.val;
      const name = document.createElement('span');
      name.className = 'unit-name';
      name.textContent = r.name;
      line.appendChild(val);
      line.appendChild(name);
      container.appendChild(line);
    });
  }

  function realValueToCm(value, unitToken) {
    const u = String(unitToken || 'cm')
      .trim()
      .toLowerCase();
    if (u === 'm' || u === '米' || u === 'meter' || u === 'meters') return value * 100;
    if (u === 'dm' || u === '分米') return value * 10;
    if (u === 'cm' || u === '厘米' || u === '公分') return value;
    if (u === 'mm' || u === '毫米' || u === '公厘') return value * 0.1;
    return null;
  }

  function fillMetricBlock(el, pxLen, opts) {
    const empty = opts && opts.empty;
    el.innerHTML = '';
    if (empty) {
      const sp = document.createElement('span');
      sp.className = 'stat-placeholder';
      sp.textContent = '—';
      el.appendChild(sp);
      return;
    }
    const pxRounded = Math.round(pxLen);
    const scale = effectivePxPerCm();
    const zoom = opts && opts.zoom != null ? opts.zoom : 1;
    const zCal =
      opts && opts.calibrationZoom != null && opts.calibrationZoom > 0
        ? opts.calibrationZoom
        : 1;
    const zoomRatio = zoom / zCal;
    const intrinsicCm = pxLen / scale;
    const screenCm = intrinsicCm * zoomRatio;

    const h1 = document.createElement('div');
    h1.className = 'stat-subhead';
    h1.textContent = '图上换算（画布里的几何长度，不随放大/缩小视图改变）';
    el.appendChild(h1);
    appendFourMetricRows(el, intrinsicCm);

    const h2 = document.createElement('div');
    h2.className = 'stat-subhead';
    if (isCalibrated()) {
      h2.textContent =
        '屏上约（用尺子在屏幕/投影上量时，会随缩放变；≈ 上图 × 当前缩放 ' +
        zoom.toFixed(2) +
        '× ÷ 标定时 ' +
        zCal.toFixed(2) +
        '×）';
    } else {
      h2.textContent =
        '屏上约（示意：上图 × 当前缩放 ' +
        zoom.toFixed(2) +
        '×；未标定时假定对照基准为 1×）';
    }
    el.appendChild(h2);
    appendFourMetricRows(el, screenCm);

    if (isCalibrated()) {
      const pxRow = document.createElement('div');
      pxRow.className = 'unit-line unit-px';
      pxRow.textContent = '（画布坐标约 ' + pxRounded + ' px）';
      el.appendChild(pxRow);
    }
  }

  function pulseEl(el) {
    el.classList.remove('pulse');
    void el.offsetWidth;
    el.classList.add('pulse');
  }

  function updateMeasures() {
    const active = canvas.getActiveObject();
    let selPx = 0;
    const hasSel = active && !active.isBackground;
    if (hasSel) {
      selPx = objectPixelLength(active);
    }
    const zNow = canvas.getZoom();
    const measureOpts = { zoom: zNow, calibrationZoom: calibrationZoom };

    fillMetricBlock(selLenBlock, selPx, Object.assign({ empty: !hasSel }, measureOpts));
    pulseEl(selLenBlock);

    let total = 0;
    canvas.getObjects().forEach(function (o) {
      total += objectPixelLength(o);
    });
    fillMetricBlock(totalLenBlock, total, Object.assign({ empty: false }, measureOpts));
    pulseEl(totalLenBlock);

    calibNote.textContent = isCalibrated()
      ? '已标定：1 厘米 ≈ ' +
        pxPerCm.toFixed(2) +
        ' 画布像素；标定时视图为 ×' +
        calibrationZoom.toFixed(2) +
        '，当前 ×' +
        zNow.toFixed(2) +
        '。「图上换算」表示教具/图上实物长度；「屏上约」按缩放比估算在屏幕上用尺量的变化。'
      : '未标定：按约 1 厘米 ≈ ' +
        DEFAULT_PX_PER_CM.toFixed(1) +
        ' 像素做示意。「图上换算」不随缩放变；「屏上约」会随当前 ×' +
        zNow.toFixed(2) +
        ' 变化。老师请用「标定」并尽量在**上课常用缩放**下标定。';

    updateConvertButtons(active);
  }

  function isFreehandPath(o) {
    return o && o.type === 'path' && o.isUserStroke && !o.isBackground;
  }

  function isStraightLine(o) {
    return o && o.type === 'line' && o.isUserStroke;
  }

  function isPolylineGroup(o) {
    return (
      o &&
      o.type === 'group' &&
      o.isUserStroke &&
      o._objects &&
      o._objects.length &&
      o._objects.every(function (x) {
        return x.type === 'line';
      })
    );
  }

  function isCurveGroup(o) {
    return o && o.type === 'group' && o.isCurveGroup;
  }

  function pathHasCloseCommand(pathObj) {
    const segs = pathObj.path;
    if (!segs) return false;
    return segs.some(function (s) {
      return s[0] === 'Z' || s[0] === 'z';
    });
  }

  function pathEndpointsClose(pathObj, parentMat) {
    const ep = pathEndpointsCanvas(pathObj, parentMat);
    if (!ep || !ep.a || !ep.b) return false;
    const sw = pathObj.strokeWidth || 4;
    const tol = Math.max(28, sw * 8);
    return Math.hypot(ep.b.x - ep.a.x, ep.b.y - ep.a.y) <= tol;
  }

  function isClosedFreehandPath(o) {
    if (!isFreehandPath(o)) return false;
    if (pathHasCloseCommand(o)) return true;
    return pathEndpointsClose(o, null);
  }

  function polylineGroupIsClosed(grp) {
    if (!isPolylineGroup(grp)) return false;
    const ep = polylineGroupEndpoints(grp);
    if (!ep || !ep.a || !ep.b) return false;
    const tol = 32;
    return Math.hypot(ep.b.x - ep.a.x, ep.b.y - ep.a.y) <= tol;
  }

  function canUnfoldStraightDemo(active) {
    return isClosedFreehandPath(active) || polylineGroupIsClosed(active);
  }

  function strokeWidthOf(o) {
    if (!o) return 4;
    if (o.strokeWidth != null) return o.strokeWidth;
    if (o.getObjects) {
      const first = o.getObjects()[0];
      if (first && first.strokeWidth != null) return first.strokeWidth;
    }
    return 4;
  }

  function updateConvertButtons(active) {
    const canLine =
      isFreehandPath(active) ||
      isPolylineGroup(active) ||
      isCurveGroup(active) ||
      (active && active.type === 'path' && active.isUserStroke);
    btnToLine.disabled = !canLine;
    btnToCurve.disabled = !isStraightLine(active);
    btnUnfoldStraight.disabled =
      unfoldAnimating ||
      !canUnfoldStraightDemo(active) ||
      hasUnfoldRestore();
    btnRestoreUnfold.disabled = !hasUnfoldRestore() || unfoldAnimating;
    btnDeleteSel.disabled = !active || active.isBackground;
  }

  function snapshot() {
    const json = canvas.toJSON(EXTRA_PROPS);
    if (historyIndex < history.length - 1) {
      history.splice(historyIndex + 1);
    }
    history.push(json);
    if (history.length > MAX_HISTORY) {
      history.shift();
    } else {
      historyIndex++;
    }
    btnUndo.disabled = historyIndex <= 0;
    btnRedo.disabled = true;
  }

  function applyHistoryIndex() {
    const json = history[historyIndex];
    if (!json) return;
    canvas.loadFromJSON(json, function () {
      canvas.getObjects().forEach(function (o) {
        if (o.isCurveGroup) {
          rebindCurveGroup(o);
        }
      });
      canvas.requestRenderAll();
      updateMeasures();
    });
    btnUndo.disabled = historyIndex <= 0;
    btnRedo.disabled = historyIndex >= history.length - 1;
  }

  function pushHistory() {
    snapshot();
  }

  btnUndo.addEventListener('click', function () {
    if (historyIndex <= 0) return;
    historyIndex--;
    applyHistoryIndex();
  });

  btnRedo.addEventListener('click', function () {
    if (historyIndex >= history.length - 1) return;
    historyIndex++;
    applyHistoryIndex();
  });

  canvas.on('path:created', function (e) {
    const p = e.path;
    p.set({
      isUserStroke: true,
      strokeUniform: true,
      objectCaching: false,
    });
    pushHistory();
    updateMeasures();
  });

  canvas.on({
    'object:modified': function () {
      pushHistory();
      updateMeasures();
    },
    'object:added': function (e) {
      if (e.target && e.target.isBackground) return;
      if (tool === 'line' && e.target && e.target.type === 'line') return;
    },
    'object:removed': function (e) {
      if (e.target && unfoldRestoreMorphRef === e.target) {
        clearUnfoldBackup();
        updateMeasures();
      }
    },
    'selection:created': updateMeasures,
    'selection:updated': updateMeasures,
    'selection:cleared': updateMeasures,
  });

  function setTool(t) {
    tool = t;
    toolBtns.forEach(function (b) {
      b.classList.toggle('active', b.getAttribute('data-tool') === t);
    });
    linePoints = [];
    lineSegments = [];
    canvas.isDrawingMode = t === 'brush';
    canvas.selection = t === 'select';
    canvas.forEachObject(function (o) {
      if (!o.isBackground) {
        o.selectable = t === 'select';
        o.evented = t === 'select' || o === canvas.getActiveObject();
      }
    });
    if (t === 'select') {
      canvas.getObjects().forEach(function (o) {
        if (!o.isBackground) {
          o.selectable = true;
          o.evented = true;
        }
      });
    } else {
      canvas.discardActiveObject();
      canvas.requestRenderAll();
    }
    if (t === 'brush') {
      setBrushFromUI();
    }
    updateMeasures();
  }

  toolBtns.forEach(function (b) {
    b.addEventListener('click', function () {
      setTool(b.getAttribute('data-tool'));
    });
  });

  function canvasPointer(e) {
    const ptr = canvas.getPointer(e.e);
    return { x: ptr.x, y: ptr.y };
  }

  function finishPolyline() {
    if (lineSegments.length === 0) {
      linePoints = [];
      return;
    }
    if (lineSegments.length === 1) {
      canvas.remove(lineSegments[0]);
      lineSegments = [];
      linePoints = [];
      pushHistory();
      updateMeasures();
      return;
    }
    const grp = new fabric.Group(lineSegments.slice(), {
      isUserStroke: true,
      strokeUniform: true,
    });
    lineSegments.forEach(function (ln) {
      canvas.remove(ln);
    });
    canvas.add(grp);
    lineSegments = [];
    linePoints = [];
    pushHistory();
    updateMeasures();
  }

  canvas.on('mouse:down', function (opt) {
    if (tool !== 'line' || canvas.isDrawingMode) return;
    if (spaceDown) return;
    if (opt.target && !opt.target.isBackground) return;
    const p = canvasPointer(opt);
    linePoints.push(p);
    if (linePoints.length >= 2) {
      const a = linePoints[linePoints.length - 2];
      const b = linePoints[linePoints.length - 1];
      const line = new fabric.Line([a.x, a.y, b.x, b.y], {
        stroke: brushColor.value,
        strokeWidth: parseInt(brushWidth.value, 10),
        strokeLineCap: 'round',
        strokeUniform: true,
        selectable: false,
        evented: false,
        isUserStroke: true,
      });
      canvas.add(line);
      lineSegments.push(line);
      canvas.requestRenderAll();
    }
  });

  canvas.upperCanvasEl.addEventListener(
    'dblclick',
    function (e) {
      if (tool === 'line') {
        e.preventDefault();
        finishPolyline();
      }
    },
    true
  );

  document.addEventListener('keydown', function (e) {
    if (e.code === 'Space') {
      spaceDown = true;
      panHint.classList.add('visible');
      e.preventDefault();
    }
    if (e.key === 'Escape' && tool === 'line') {
      finishPolyline();
    }
    if ((e.ctrlKey || e.metaKey) && e.key === 'z' && !e.shiftKey) {
      e.preventDefault();
      btnUndo.click();
    }
    if ((e.ctrlKey || e.metaKey) && (e.key === 'y' || (e.key === 'z' && e.shiftKey))) {
      e.preventDefault();
      btnRedo.click();
    }
  });

  document.addEventListener('keyup', function (e) {
    if (e.code === 'Space') {
      spaceDown = false;
      isPanning = false;
      panHint.classList.remove('visible');
    }
  });

  canvas.on('mouse:down', function (opt) {
    if (!spaceDown) return;
    isPanning = true;
    panLast = { x: opt.e.clientX, y: opt.e.clientY };
    opt.e.preventDefault();
  });

  canvas.on('mouse:move', function (opt) {
    if (!isPanning || !panLast) return;
    const e = opt.e;
    const dx = e.clientX - panLast.x;
    const dy = e.clientY - panLast.y;
    const vpt = canvas.viewportTransform;
    vpt[4] += dx;
    vpt[5] += dy;
    canvas.requestRenderAll();
    panLast = { x: e.clientX, y: e.clientY };
  });

  canvas.on('mouse:up', function () {
    isPanning = false;
    panLast = null;
  });

  canvas.on('mouse:wheel', function (opt) {
    const delta = opt.e.deltaY;
    let zoom = canvas.getZoom();
    zoom *= 0.999 ** delta;
    if (zoom > 8) zoom = 8;
    if (zoom < 0.2) zoom = 0.2;
    canvas.zoomToPoint({ x: opt.e.offsetX, y: opt.e.offsetY }, zoom);
    opt.e.preventDefault();
    opt.e.stopPropagation();
    updateMeasures();
  });

  let lastTouchDist = null;
  canvas.upperCanvasEl.addEventListener(
    'touchstart',
    function (e) {
      if (e.touches.length === 2) {
        const t0 = e.touches[0];
        const t1 = e.touches[1];
        lastTouchDist = Math.hypot(t1.clientX - t0.clientX, t1.clientY - t0.clientY);
      }
    },
    { passive: true }
  );

  canvas.upperCanvasEl.addEventListener(
    'touchmove',
    function (e) {
      if (e.touches.length === 2 && lastTouchDist != null) {
        e.preventDefault();
        const t0 = e.touches[0];
        const t1 = e.touches[1];
        const d = Math.hypot(t1.clientX - t0.clientX, t1.clientY - t0.clientY);
        const scale = d / lastTouchDist;
        lastTouchDist = d;
        let zoom = canvas.getZoom() * scale;
        if (zoom > 8) zoom = 8;
        if (zoom < 0.2) zoom = 0.2;
        const cx = (t0.clientX + t1.clientX) / 2;
        const cy = (t0.clientY + t1.clientY) / 2;
        const rect = canvas.upperCanvasEl.getBoundingClientRect();
        canvas.zoomToPoint({ x: cx - rect.left, y: cy - rect.top }, zoom);
        canvas.requestRenderAll();
        updateMeasures();
      }
    },
    { passive: false }
  );

  canvas.upperCanvasEl.addEventListener('touchend', function () {
    lastTouchDist = null;
  });

  function preventScrollWhileDrawing(e) {
    if (canvas.isDrawingMode || tool === 'line') {
      if (e.cancelable) e.preventDefault();
    }
  }
  canvas.upperCanvasEl.addEventListener('touchmove', preventScrollWhileDrawing, {
    passive: false,
  });

  fileInput.addEventListener('change', function (ev) {
    const f = ev.target.files && ev.target.files[0];
    if (!f) return;
    const url = URL.createObjectURL(f);
    fabric.Image.fromURL(url, function (img) {
      URL.revokeObjectURL(url);
      canvas.getObjects().forEach(function (o) {
        if (o.isBackground) canvas.remove(o);
      });
      const cw = canvas.getWidth();
      const ch = canvas.getHeight();
      const scale = Math.min(cw / img.width, ch / img.height, 1);
      img.scale(scale);
      img.set({
        left: cw / 2,
        top: ch / 2,
        originX: 'center',
        originY: 'center',
        selectable: false,
        evented: false,
        isBackground: true,
      });
      canvas.add(img);
      img.sendToBack();
      pushHistory();
      canvas.requestRenderAll();
    });
    ev.target.value = '';
  });

  btnGrid.addEventListener('click', function () {
    wrap.classList.toggle('grid-bg');
  });

  btnClear.addEventListener('click', function () {
    canvas.getObjects().slice().forEach(function (o) {
      if (!o.isBackground) canvas.remove(o);
    });
    linePoints = [];
    lineSegments = [];
    pushHistory();
    updateMeasures();
  });

  btnCalibrate.addEventListener('click', function () {
    const active = canvas.getActiveObject();
    if (!active || active.isBackground) {
      alert('请先选中一条线段（或折线组），作为已知长度的参照。');
      return;
    }
    const pxLen = objectPixelLength(active);
    if (pxLen <= 0) {
      alert('无法从当前选中对象计算长度。');
      return;
    }
    const input = prompt(
      '这条选中路径在真实世界中的长度（只填数字，例如 1 或 10）？',
      '1'
    );
    if (input == null) return;
    const num = parseFloat(String(input).replace(/,/g, '.'), 10);
    if (!isFinite(num) || num <= 0) {
      alert('请输入大于 0 的数字。');
      return;
    }
    const unitIn = prompt(
      '该长度对应的单位？可输入：m / dm / cm / mm，或 米 / 分米 / 厘米 / 毫米',
      'cm'
    );
    if (unitIn == null) return;
    const cmReal = realValueToCm(num, unitIn);
    if (cmReal == null || cmReal <= 0) {
      alert('无法识别单位，请使用 m、dm、cm、mm 或 米、分米、厘米、毫米。');
      return;
    }
    pxPerCm = pxLen / cmReal;
    calibrationZoom = canvas.getZoom();
    updateMeasures();
  });

  function pathEndpointsCanvas(pathObj, parentMat) {
    const segs = pathObj.path;
    const m = parentMat
      ? fabric.util.multiplyTransformMatrices(parentMat, pathObj.calcTransformMatrix())
      : pathObj.calcTransformMatrix();
    let cx = 0;
    let cy = 0;
    let first = null;
    for (let i = 0; i < segs.length; i++) {
      const sub = segs[i];
      const cmd = sub[0];
      if (cmd === 'M') {
        cx = sub[1];
        cy = sub[2];
        if (!first) {
          first = fabric.util.transformPoint(new fabric.Point(cx, cy), m);
        }
      } else if (cmd === 'L') {
        cx = sub[1];
        cy = sub[2];
      } else if (cmd === 'Q') {
        cx = sub[3];
        cy = sub[4];
      } else if (cmd === 'C') {
        cx = sub[5];
        cy = sub[6];
      }
    }
    const last = fabric.util.transformPoint(new fabric.Point(cx, cy), m);
    return { a: first, b: last };
  }

  function polylineGroupEndpoints(grp) {
    const lines = grp.getObjects().filter(function (x) {
      return x.type === 'line';
    });
    if (!lines.length) return null;
    const gMat = grp.calcTransformMatrix();
    const firstLine = lines[0];
    const lastLine = lines[lines.length - 1];
    const fMat = fabric.util.multiplyTransformMatrices(gMat, firstLine.calcTransformMatrix());
    const lMat = fabric.util.multiplyTransformMatrices(gMat, lastLine.calcTransformMatrix());
    const a = fabric.util.transformPoint(new fabric.Point(firstLine.x1, firstLine.y1), fMat);
    const b = fabric.util.transformPoint(new fabric.Point(lastLine.x2, lastLine.y2), lMat);
    return { a, b };
  }

  function curveGroupEndpoints(grp) {
    if (!grp || !grp.isCurveGroup) return null;
    const items = grp.getObjects();
    const pathObj = items[0];
    if (!pathObj || pathObj.type !== 'path') return null;
    return pathEndpointsCanvas(pathObj, grp.calcTransformMatrix());
  }

  btnToLine.addEventListener('click', function () {
    const active = canvas.getActiveObject();
    if (!active) return;
    let a;
    let b;
    let stroke = active.stroke || brushColor.value;
    let strokeWidth = active.strokeWidth || parseInt(brushWidth.value, 10);

    if (isFreehandPath(active)) {
      const ep = pathEndpointsCanvas(active);
      if (!ep || !ep.a) return;
      a = ep.a;
      b = ep.b;
      stroke = active.stroke;
      strokeWidth = active.strokeWidth;
    } else if (isPolylineGroup(active)) {
      const ep = polylineGroupEndpoints(active);
      if (!ep) return;
      a = ep.a;
      b = ep.b;
    } else if (isCurveGroup(active)) {
      const ep = curveGroupEndpoints(active);
      if (!ep || !ep.a) return;
      a = ep.a;
      b = ep.b;
      stroke = active.getObjects()[0].stroke || stroke;
      strokeWidth = active.getObjects()[0].strokeWidth || strokeWidth;
    } else {
      return;
    }

    const arcLenPx = objectPixelLength(active);
    if (!(arcLenPx > 0)) return;

    const chordLine = new fabric.Line([a.x, a.y, b.x, b.y], {
      stroke: '#1565c0',
      strokeWidth: Math.max(3, strokeWidth),
      strokeLineCap: 'round',
      strokeDashArray: [14, 10],
      strokeUniform: true,
      isUserStroke: true,
      isChordCompareLine: true,
    });

    const midX = (a.x + b.x) / 2;
    const midY = (a.y + b.y) / 2;
    const unfoldDy = Math.max(40, strokeWidth * 6);
    const half = arcLenPx / 2;
    const unfoldLine = new fabric.Line(
      [midX - half, midY + unfoldDy, midX + half, midY + unfoldDy],
      {
        stroke: '#2e7d32',
        strokeWidth: Math.max(3, strokeWidth),
        strokeLineCap: 'round',
        strokeDashArray: [12, 8],
        strokeUniform: true,
        isUserStroke: true,
        isArcUnfoldLine: true,
      }
    );

    canvas.add(chordLine);
    canvas.add(unfoldLine);
    if (typeof canvas.bringToFront === 'function') {
      canvas.bringToFront(chordLine);
      canvas.bringToFront(unfoldLine);
    }

    unfoldLine.set({ opacity: 0 });
    chordLine.set({ opacity: 0 });
    canvas.setActiveObject(unfoldLine);
    canvas.requestRenderAll();

    const start = performance.now();
    const dur = 280;
    function fadeIn(now) {
      const t = Math.min(1, (now - start) / dur);
      const ease = t * (2 - t);
      chordLine.set({ opacity: ease });
      unfoldLine.set({ opacity: ease });
      canvas.requestRenderAll();
      if (t < 1) {
        requestAnimationFrame(fadeIn);
      } else {
        chordLine.set({ opacity: 1 });
        unfoldLine.set({ opacity: 1 });
        pushHistory();
        updateMeasures();
      }
    }
    requestAnimationFrame(fadeIn);
  });

  function rebindCurveGroup(grp) {
    const items = grp.getObjects();
    const pathObj = items[0];
    const ctrl = items[1];
    if (!pathObj || pathObj.type !== 'path' || !ctrl || !ctrl.curveHandle) return;
    const segs = pathObj.path;
    if (!segs || !segs.length) return;
    let M = null;
    let Q = null;
    for (let i = 0; i < segs.length; i++) {
      if (segs[i][0] === 'M' && !M) M = segs[i];
      if (segs[i][0] === 'Q') {
        Q = segs[i];
        break;
      }
    }
    if (!M || !Q || M[0] !== 'M' || Q[0] !== 'Q') return;
    const Al = M[1];
    const At = M[2];
    const Bl = Q[3];
    const Bt = Q[4];

    ctrl.off('moving');
    ctrl.off('mouseup');
    ctrl.on('moving', function () {
      const cx = ctrl.left;
      const cy = ctrl.top;
      pathObj.path = [['M', Al, At], ['Q', cx, cy, Bl, Bt]];
      pathObj.set({ dirty: true });
      pathObj.setCoords();
      grp.set({ dirty: true });
      grp.setCoords();
      canvas.requestRenderAll();
      updateMeasures();
    });
    ctrl.on('mouseup', function () {
      pushHistory();
    });
  }

  btnToCurve.addEventListener('click', function () {
    const active = canvas.getActiveObject();
    if (!isStraightLine(active)) return;

    const { a, b } = lineAbsEndpoints(active);
    const mx = (a.x + b.x) / 2;
    const my = (a.y + b.y) / 2;

    const pathD =
      'M ' +
      a.x +
      ' ' +
      a.y +
      ' Q ' +
      mx +
      ' ' +
      my +
      ' ' +
      b.x +
      ' ' +
      b.y;

    const path = new fabric.Path(pathD, {
      fill: '',
      stroke: active.stroke || '#e53935',
      strokeWidth: active.strokeWidth || 4,
      strokeLineCap: 'round',
      strokeUniform: true,
      objectCaching: false,
    });

    const ctrl = new fabric.Circle({
      left: mx,
      top: my,
      radius: 14,
      originX: 'center',
      originY: 'center',
      fill: 'rgba(33, 150, 243, 0.9)',
      stroke: '#fff',
      strokeWidth: 2,
      curveHandle: true,
      hasBorders: true,
    });

    const grp = new fabric.Group([path, ctrl], {
      subTargetCheck: true,
      isUserStroke: true,
      isCurveGroup: true,
    });

    canvas.remove(active);
    canvas.add(grp);
    grp.setCoords();
    canvas.setActiveObject(grp);
    rebindCurveGroup(grp);
    canvas.requestRenderAll();
    pushHistory();
    updateMeasures();
  });

  function pathDenseSamplesCanvas(pathObj, parentMat, quadSteps, cubicSteps) {
    const segs = pathObj.path;
    if (!segs || !segs.length) return [];
    const m = parentMat
      ? fabric.util.multiplyTransformMatrices(parentMat, pathObj.calcTransformMatrix())
      : pathObj.calcTransformMatrix();
    const qS = quadSteps || 14;
    const cS = cubicSteps || 18;
    const localPts = [];
    let cx = 0;
    let cy = 0;
    let sx = 0;
    let sy = 0;

    function addLocal(x, y) {
      localPts.push({ x: x, y: y });
    }

    for (let i = 0; i < segs.length; i++) {
      const sub = segs[i];
      const cmd = sub[0];
      if (cmd === 'M') {
        cx = sub[1];
        cy = sub[2];
        sx = cx;
        sy = cy;
        addLocal(cx, cy);
      } else if (cmd === 'L') {
        cx = sub[1];
        cy = sub[2];
        addLocal(cx, cy);
      } else if (cmd === 'Q') {
        const c1x = sub[1];
        const c1y = sub[2];
        const x2 = sub[3];
        const y2 = sub[4];
        for (let s = 1; s <= qS; s++) {
          const t = s / qS;
          const ox = (1 - t) * (1 - t) * cx + 2 * (1 - t) * t * c1x + t * t * x2;
          const oy = (1 - t) * (1 - t) * cy + 2 * (1 - t) * t * c1y + t * t * y2;
          addLocal(ox, oy);
        }
        cx = x2;
        cy = y2;
      } else if (cmd === 'C') {
        const x1 = sub[1];
        const y1 = sub[2];
        const x2 = sub[3];
        const y2 = sub[4];
        const x3 = sub[5];
        const y3 = sub[6];
        for (let s = 1; s <= cS; s++) {
          const tt = s / cS;
          const t1 = 1 - tt;
          const ox =
            t1 * t1 * t1 * cx +
            3 * t1 * t1 * tt * x1 +
            3 * t1 * tt * tt * x2 +
            tt * tt * tt * x3;
          const oy =
            t1 * t1 * t1 * cy +
            3 * t1 * t1 * tt * y1 +
            3 * t1 * tt * tt * y2 +
            tt * tt * tt * y3;
          addLocal(ox, oy);
        }
        cx = x3;
        cy = y3;
      } else if (cmd === 'Z' || cmd === 'z') {
        for (let s = 1; s <= 10; s++) {
          const t = s / 10;
          addLocal(cx + t * (sx - cx), cy + t * (sy - cy));
        }
        cx = sx;
        cy = sy;
      }
    }

    return localPts.map(function (p) {
      return fabric.util.transformPoint(new fabric.Point(p.x, p.y), m);
    });
  }

  function polylineGroupDenseCanvas(grp) {
    const lines = grp.getObjects().filter(function (x) {
      return x.type === 'line';
    });
    const out = [];
    const gMat = grp.calcTransformMatrix();
    lines.forEach(function (line) {
      const m = fabric.util.multiplyTransformMatrices(gMat, line.calcTransformMatrix());
      const a = fabric.util.transformPoint(new fabric.Point(line.x1, line.y1), m);
      const b = fabric.util.transformPoint(new fabric.Point(line.x2, line.y2), m);
      if (
        out.length === 0 ||
        Math.hypot(a.x - out[out.length - 1].x, a.y - out[out.length - 1].y) > 0.5
      ) {
        out.push({ x: a.x, y: a.y });
      }
      out.push({ x: b.x, y: b.y });
    });
    return out;
  }

  function trimClosingDuplicateVerts(verts) {
    const out = verts.slice();
    while (out.length > 2) {
      const a = out[out.length - 1];
      const b = out[0];
      if (Math.hypot(a.x - b.x, a.y - b.y) < 2) {
        out.pop();
      } else {
        break;
      }
    }
    return out;
  }

  function closedLoopPerimeter(vertices) {
    const n = vertices.length;
    if (n < 2) return 0;
    let total = 0;
    for (let i = 0; i < n - 1; i++) {
      total += Math.hypot(vertices[i + 1].x - vertices[i].x, vertices[i + 1].y - vertices[i].y);
    }
    total += Math.hypot(vertices[n - 1].x - vertices[0].x, vertices[n - 1].y - vertices[0].y);
    return total;
  }

  function pointAtDistanceOnClosedLoop(vertices, dAbs) {
    const n = vertices.length;
    if (n < 2) return vertices[0] || { x: 0, y: 0 };
    const edges = [];
    let total = 0;
    for (let i = 0; i < n - 1; i++) {
      const d = Math.hypot(vertices[i + 1].x - vertices[i].x, vertices[i + 1].y - vertices[i].y);
      edges.push({ from: vertices[i], to: vertices[i + 1], d: d });
      total += d;
    }
    const dc = Math.hypot(vertices[n - 1].x - vertices[0].x, vertices[n - 1].y - vertices[0].y);
    edges.push({ from: vertices[n - 1], to: vertices[0], d: dc });
    total += dc;
    if (total < 1e-6) return { x: vertices[0].x, y: vertices[0].y };
    let d = dAbs % total;
    if (d < 0) d += total;
    let acc = 0;
    for (let e = 0; e < edges.length; e++) {
      const ed = edges[e];
      if (acc + ed.d >= d - 1e-9) {
        const t = ed.d < 1e-9 ? 0 : (d - acc) / ed.d;
        return {
          x: ed.from.x + t * (ed.to.x - ed.from.x),
          y: ed.from.y + t * (ed.to.y - ed.from.y),
        };
      }
      acc += ed.d;
    }
    return { x: vertices[0].x, y: vertices[0].y };
  }

  function sampleClosedLoopByFraction(vertices, n, perimeter) {
    const out = [];
    for (let k = 0; k < n; k++) {
      const frac = n <= 1 ? 0 : k / (n - 1);
      out.push(pointAtDistanceOnClosedLoop(vertices, frac * perimeter));
    }
    return out;
  }

  function sampleStraightHorizontal(A, L, n) {
    const out = [];
    for (let k = 0; k < n; k++) {
      const t = n <= 1 ? 0 : k / (n - 1);
      out.push({ x: A.x + t * L, y: A.y });
    }
    return out;
  }

  function lerpPointArrays(ptsA, ptsB, t) {
    const out = [];
    for (let i = 0; i < ptsA.length; i++) {
      out.push({
        x: ptsA[i].x * (1 - t) + ptsB[i].x * t,
        y: ptsA[i].y * (1 - t) + ptsB[i].y * t,
      });
    }
    return out;
  }

  function canvasPointsToPolyline(pts, strokeOpts) {
    if (!pts.length) return null;
    let minX = Infinity;
    let minY = Infinity;
    pts.forEach(function (p) {
      minX = Math.min(minX, p.x);
      minY = Math.min(minY, p.y);
    });
    const rel = pts.map(function (p) {
      return { x: p.x - minX, y: p.y - minY };
    });
    return new fabric.Polyline(rel, Object.assign({
      left: minX,
      top: minY,
      fill: '',
      strokeUniform: true,
      strokeLineCap: 'round',
      strokeLineJoin: 'round',
      objectCaching: false,
      isUserStroke: true,
      isUnfoldDemoLine: true,
    }, strokeOpts));
  }

  function updatePolylineCanvasPts(poly, pts) {
    if (!pts.length) return;
    let minX = Infinity;
    let minY = Infinity;
    pts.forEach(function (p) {
      minX = Math.min(minX, p.x);
      minY = Math.min(minY, p.y);
    });
    const rel = pts.map(function (p) {
      return { x: p.x - minX, y: p.y - minY };
    });
    poly.set({ points: rel, left: minX, top: minY });
    poly.setCoords();
  }

  function buildUnfoldSamples(active, L) {
    let dense;
    let stroke;
    if (isFreehandPath(active)) {
      dense = pathDenseSamplesCanvas(active, null, 14, 18);
      stroke = active.stroke || '#e53935';
    } else if (isPolylineGroup(active)) {
      dense = polylineGroupDenseCanvas(active);
      stroke = active.getObjects()[0].stroke || '#e53935';
    } else {
      return null;
    }
    dense = trimClosingDuplicateVerts(dense);
    if (dense.length < 3) return null;

    const pActual = closedLoopPerimeter(dense);
    if (!(pActual > 4)) return null;

    const n = Math.min(160, Math.max(28, Math.floor(L / 5)));
    const sourcePts = sampleClosedLoopByFraction(dense, n, pActual);
    const br = active.getBoundingRect(true);
    const sw = strokeWidthOf(active);
    const margin = Math.max(48, sw * 10);
    const A = {
      x: br.left + br.width / 2 - L / 2,
      y: br.top + br.height + margin,
    };
    const targetPts = sampleStraightHorizontal(A, L, n);
    return { sourcePts: sourcePts, targetPts: targetPts, stroke: stroke, sw: sw };
  }

  btnUnfoldStraight.addEventListener('click', function () {
    if (unfoldAnimating) return;
    if (hasUnfoldRestore()) return;

    const active = canvas.getActiveObject();
    if (!canUnfoldStraightDemo(active)) {
      alert(
        '请先选中一条「围着图画的封闭线」：手绘时让首尾靠近闭合，或直线多点连线时让最后一点回到起点附近。'
      );
      return;
    }
    const L = objectPixelLength(active);
    if (!(L > 8)) {
      alert('这条线太短，无法演示。');
      return;
    }

    const pack = buildUnfoldSamples(active, L);
    if (!pack || !pack.sourcePts.length) {
      alert('无法从当前图形采样轮廓，请换一条线重试。');
      return;
    }

    unfoldAnimating = true;
    btnUnfoldStraight.disabled = true;
    btnRestoreUnfold.disabled = true;

    const insertIdx = canvas.getObjects().indexOf(active);
    const sw = Math.max(3, pack.sw || 4);

    function startMorphWithBackup(cloned) {
      clearUnfoldBackup();
      unfoldRestoreClone = cloned;
      cloned.set({
        evented: true,
        selectable: true,
        isUserStroke: true,
      });

      const morphPoly = canvasPointsToPolyline(pack.sourcePts, {
        stroke: pack.stroke,
        strokeWidth: sw,
      });

      canvas.remove(active);
      canvas.add(morphPoly);
      if (insertIdx >= 0 && typeof canvas.moveTo === 'function') {
        canvas.moveTo(morphPoly, insertIdx);
      }
      unfoldRestoreMorphRef = morphPoly;
      canvas.setActiveObject(morphPoly);
      canvas.requestRenderAll();

      const dur = 1600;
      const start = performance.now();

      function easeOutCubic(t) {
        return 1 - Math.pow(1 - t, 3);
      }

      function tick(now) {
        const u = Math.min(1, (now - start) / dur);
        const p = easeOutCubic(u);
        const cur = lerpPointArrays(pack.sourcePts, pack.targetPts, p);
        updatePolylineCanvasPts(morphPoly, cur);
        canvas.requestRenderAll();
        if (u < 1) {
          requestAnimationFrame(tick);
        } else {
          updatePolylineCanvasPts(morphPoly, pack.targetPts);
          unfoldAnimating = false;
          pushHistory();
          updateMeasures();
          canvas.requestRenderAll();
        }
      }
      requestAnimationFrame(tick);
    }

    if (typeof active.clone === 'function') {
      active.clone(function (cloned) {
        if (!cloned) {
          unfoldAnimating = false;
          updateMeasures();
          alert('无法复制图形，请重试。');
          return;
        }
        startMorphWithBackup(cloned);
      }, EXTRA_PROPS);
    } else {
      unfoldAnimating = false;
      updateMeasures();
      alert('当前环境不支持图形克隆，无法提供还原。');
    }
  });

  btnRestoreUnfold.addEventListener('click', function () {
    if (!hasUnfoldRestore() || unfoldAnimating) return;
    const morph = unfoldRestoreMorphRef;
    const restored = unfoldRestoreClone;
    const idx = canvas.getObjects().indexOf(morph);
    canvas.remove(morph);
    canvas.add(restored);
    if (idx >= 0 && typeof canvas.moveTo === 'function') {
      canvas.moveTo(restored, idx);
    }
    restored.setCoords();
    if (restored.type === 'group' && restored.isCurveGroup) {
      rebindCurveGroup(restored);
    }
    canvas.setActiveObject(restored);
    clearUnfoldBackup();
    pushHistory();
    updateMeasures();
    canvas.requestRenderAll();
  });

  btnDeleteSel.addEventListener('click', function () {
    const active = canvas.getActiveObject();
    if (!active || active.isBackground) return;
    canvas.remove(active);
    canvas.discardActiveObject();
    pushHistory();
    updateMeasures();
  });

  btnExport.addEventListener('click', function () {
    const data = canvas.toDataURL({
      format: 'png',
      multiplier: 2,
    });
    const a = document.createElement('a');
    a.href = data;
    a.download = '课堂描边-' + new Date().toISOString().slice(0, 19).replace(/:/g, '-') + '.png';
    a.click();
  });

  snapshot();
  btnUndo.disabled = true;
  btnRedo.disabled = true;

  wrap.addEventListener('dragover', function (e) {
    e.preventDefault();
    e.dataTransfer.dropEffect = 'copy';
  });
  wrap.addEventListener('drop', function (e) {
    e.preventDefault();
    const f = e.dataTransfer.files && e.dataTransfer.files[0];
    if (!f || !/^image\/(jpeg|png|webp)$/i.test(f.type)) return;
    const url = URL.createObjectURL(f);
    fabric.Image.fromURL(url, function (img) {
      URL.revokeObjectURL(url);
      canvas.getObjects().forEach(function (o) {
        if (o.isBackground) canvas.remove(o);
      });
      const cw = canvas.getWidth();
      const ch = canvas.getHeight();
      const scale = Math.min(cw / img.width, ch / img.height, 1);
      img.scale(scale);
      img.set({
        left: cw / 2,
        top: ch / 2,
        originX: 'center',
        originY: 'center',
        selectable: false,
        evented: false,
        isBackground: true,
      });
      canvas.add(img);
      img.sendToBack();
      pushHistory();
      canvas.requestRenderAll();
    });
  });

  updateMeasures();
})();
