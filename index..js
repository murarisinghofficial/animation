"use strict";

let canv, ctx; // canvas and context
let maxx, maxy; // canvas dimensions

let radius; // hexagons radius (and side length)
let grid; // array of hexagons
let nbx, nby; // grid size (in elements, not pixels)
let midx, midy;
let loops, colorful, hue, sat, withStroke;
let angle;
let firstRun = true;

// for animation
let messages;

// shortcuts for Math.
const mrandom = Math.random;
const mfloor = Math.floor;
const mround = Math.round;
const mceil = Math.ceil;
const mabs = Math.abs;
const mmin = Math.min;
const mmax = Math.max;

const mPI = Math.PI;
const mPIS2 = Math.PI / 2;
const mPIS3 = Math.PI / 3;
const m2PI = Math.PI * 2;
const m2PIS3 = (Math.PI * 2) / 3;
const msin = Math.sin;
const mcos = Math.cos;
const matan2 = Math.atan2;

const mhypot = Math.hypot;
const msqrt = Math.sqrt;

const rac3 = msqrt(3);
const rac3s2 = rac3 / 2;

//------------------------------------------------------------------------

function alea(mini, maxi) {
    // random number in given range

    if (typeof maxi == "undefined") return mini * mrandom(); // range 0..mini

    return mini + mrandom() * (maxi - mini); // range mini..maxi
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
function intAlea(mini, maxi) {
    // random integer in given range (mini..maxi - 1 or 0..mini - 1)
    //
    if (typeof maxi == "undefined") return mfloor(mini * mrandom()); // range 0..mini - 1
    return mini + mfloor(mrandom() * (maxi - mini)); // range mini .. maxi - 1
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

function lerp(p0, p1, alpha) {
    return {
        x: p0.x * (1 - alpha) + p1.x * alpha,
        y: p0.y * (1 - alpha) + p1.y * alpha
    };
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
function cutC(cubic, alpha) {
    /* cubic is an array of 4 points
         returns 2 cubics
         CAUTION ! some of the points in the returned cubics actually are the same points or points of the input cubic, not copies
         */
    const pa = lerp(cubic[0], cubic[1], alpha);
    const pb = lerp(cubic[1], cubic[2], alpha);
    const pc = lerp(cubic[2], cubic[3], alpha);
    const pd = lerp(pa, pb, alpha);
    const pe = lerp(pb, pc, alpha);
    const pf = lerp(pd, pe, alpha);
    return [
        [cubic[0], pa, pd, pf],
        [pf, pe, pc, cubic[3]]
    ];
}

//-----------------------------------------------------------------------------

class SuperArray {
    constructor() {
        /* kmin and kmax are only updated by the setItem method.
            Direct adding or removing of elements are not stricly prohibited, but may lead to strange behaviors - especially for isEmpty and forEach
            */
        this.kmin = Infinity;
        this.kmax = -Infinity; // kmax < kmin => empty ; kmax == kmin means 1 element
    } // constructor

    isEmpty() {
        return this.kmax < this.kmin;
    } // isEmpty

    setItem(value, ky, kx) {
        /* kx optional
               kx (if present) and ky must be signed integers */

        this.kmin = mmin(this.kmin, ky);
        this.kmax = mmax(this.kmax, ky);
        if (kx === undefined) {
            // 2D access
            this[ky] = value;
            return;
        }
        if (this[ky] === undefined) {
            this[ky] = new SuperArray();
        }
        this[ky].setItem(value, kx);
    } // setItem

    getItem(ky, kx) {
        /* kx optional */
        /* if you are sure that this[ky][kx] exists, just use this syntax !
         */
        let p = this[ky];
        if (kx === undefined) return p;
        if (!(p instanceof SuperArray)) return undefined;
        return p[kx];
    } // getItem

    forEach(func) {
        /* iterates from this.kmin to this.kmax inclusive
            if given element exists and IS NOT a SuperArray, calls func on it
            if given element exists and IS a superArray, calls forEach on it
    
            func must be of the form f(value, ky) or f(value, ky, kx)
            */
        let ar, arr;
        for (let ky = this.kmin; ky < this.kmax + 1; ++ky) {
            ar = this[ky];
            if (ar === undefined) continue;
            if (!(ar instanceof SuperArray)) {
                func(ar, ky); // 1D array
            } else {
                for (let kx = ar.kmin; kx < ar.kmax + 1; ++kx) {
                    arr = ar[kx];
                    if (arr === undefined) continue;
                    func(arr, ky, kx);
                } // for kx
            }
        } // for ky
    } // forEach
} // class SuperArray

//-----------------------------------------------------------------------------
const tc = [1, 0.5, -0.5, -1, -0.5, 0.5]; // cos 0, pi/6, 2pi/6 ...
const ts = [0, rac3s2, rac3s2, 0, -rac3s2, -rac3s2]; // sin 0, pi/6, 2pi/6 ...

const tnx = [0, 1, 1, 0, -1, -1]; // relative kx index of neighbors
const tny = [-1, -1, 0, 1, 1, 0];

class Hexagon {
    constructor(ky, kx) {
        this.kx = kx;
        this.ky = ky;
        this.xc = midx + (kx * 3 * radius) / 2;
        this.yc = midy + (ky + kx / 2) * radius * rac3;
        this.vertices = new Array(6).fill(0).map((v, k) => ({
            x: this.xc + radius * tc[(k + 4) % 6],
            y: this.yc + radius * ts[(k + 4) % 6]
        }));
        this.neighbors = []; // will be defined later, when all hexagons have been created
    } // constructor

    isInside() {
        /* returns true if 6 vertices all are inside view area */
        let p;
        for (let k = 0; k < 6; ++k) {
            p = this.vertices[k];
            if (p.x < 0 || p.x >= maxx || p.y < 0 || p.y >= maxy) return false;
        }
        return true;
    }
    isOutside() {
        /* returns true if 6 vertices all are outside view area */
        /* don't care about hexagons bigger than display */
        let p;
        for (let k = 0; k < 6; ++k) {
            p = this.vertices[k];
            if (p.x >= 0 && p.x < maxx && p.y >= 0 && p.y < maxy) return false;
        }
        return true;
    }

    getNeighborIndices(edge) {
        return { kx: this.kx + tnx[edge], ky: this.ky + tny[edge] }; // does not imply such neighbor actually exists
    }

    setNeighbors() {
        for (let edge = 0; edge < 6; ++edge) {
            let idx = this.getNeighborIndices(edge);
            this.neighbors[edge] = grid.getItem(idx.ky, idx.kx);
        }
    }

    drawHexagon() {
        ctx.strokeStyle = "#888";
        ctx.lineWidth = 1.5;
        ctx.beginPath();
        this.vertices.forEach((v, k) => {
            if (k == 0) ctx.moveTo(v.x, v.y);
            else ctx.lineTo(v.x, v.y);
        });
        ctx.closePath();
        ctx.stroke();
    } // drawHexagon

    //-----------------------------------------------------------------------------

    defineArcs() {
        const karc = 0.28; // 0 ..0.5
        const l0b0 = 0.4; // for little bezier, free end - should depend of karc
        const l1b0 = 0.5; // for little bezier, common end - should depend of karc
        const l0b1 = 0.6; // for big bezier, free end - should depend of karc
        const l1b1 = 0.6; // for big bezier, common end - should depend of karc

        this.rot = intAlea(6);
        this.o0 = intAlea(3);
        this.o1 = intAlea(3);
        this.points = [];
        for (let k = 0; k < 6; ++k) {
            this.points[3 * k] = lerp(
                this.vertices[k],
                this.vertices[(k + 1) % 6],
                karc
            );
            this.points[3 * k + 1] = lerp(
                this.vertices[k],
                this.vertices[(k + 1) % 6],
                0.5
            );
            this.points[3 * k + 2] = lerp(
                this.vertices[k],
                this.vertices[(k + 1) % 6],
                1 - karc
            );
        }

        this.segs = []; // will contain description of loops entering hexa at point kin = 0..17 (3 entry points on each side)

        // initially define routes for rot = 0. "routes" means exit point for every entry point
        let routes = this.o0
            ? [17, 0, 3, 2, 1, 6, 5, 15, 14, 4, 16]
            : [17, 16, 1, 2, 3, 6, 5, 15, 14, 4, 0];
        routes.splice(
            7,
            0,
            ...(this.o1 ? [13, 7, 8, 9, 12, 11, 10] : [13, 9, 8, 7, 10, 11, 12])
        );
        // now apply rotation to routes
        this.routes = [];

        routes.forEach(
            (exit, entry) =>
                (this.routes[(entry + this.rot * 3) % 18] = (exit + this.rot * 3) % 18)
        );

        // building blocks
        const vlarc = {
            kind: "arc",
            radius: karc,
            center: { x: -0.5, y: -rac3s2 },
            a0: 0,
            a1: 2,
            ccw: false
        }; // very little arc
        const larc = {
            kind: "arc",
            radius: 0.5,
            center: { x: -0.5, y: -rac3s2 },
            a0: 0,
            a1: 2,
            ccw: false
        }; // little arc
        const barc = {
            kind: "arc",
            radius: 1.5,
            center: { x: 0, y: -rac3 },
            a0: 1,
            a1: 2,
            ccw: false
        }; // big arc

        const b0 = {
            kind: "bezier",
            p0: { x: 0.5 - karc, y: -rac3s2 },
            p1: { x: 0.5 - karc, y: -rac3s2 + l0b0 },
            p2: rotP({ x: 0, y: -rac3s2 + l1b0 }, 5),
            p3: { x: -0.75, y: -rac3s2 / 2 }
        }; // little bezier

        const b1 = {
            kind: "bezier",
            p0: rotP({ x: -0.5 + karc, y: -rac3s2 }, 1),
            p1: rotP({ x: -0.5 + karc, y: -rac3s2 + l1b0 }, 1),
            p2: rotP({ x: 0, y: -rac3s2 + l1b1 }, 5),
            p3: { x: -0.75, y: -rac3s2 / 2 }
        }; // big bezier

        const symb0 = {
            kind: "bezier",
            p0: { x: -b0.p0.x, y: b0.p0.y },
            p1: { x: -b0.p1.x, y: b0.p1.y },
            p2: { x: -b0.p2.x, y: b0.p2.y },
            p3: { x: -b0.p3.x, y: b0.p3.y }
        };
        const symb1 = {
            kind: "bezier",
            p0: { x: -b1.p0.x, y: b1.p0.y },
            p1: { x: -b1.p1.x, y: b1.p1.y },
            p2: { x: -b1.p2.x, y: b1.p2.y },
            p3: { x: -b1.p3.x, y: b1.p3.y }
        };

        // calculate graphic elements for radius = 1 and center of hexagon = (0,0)
        this.carcs = []; // each compound arc can be an arc of circle, or a bezier cubic curve, or 2 arcs
        this.carcs[(6 + 3 * this.rot) % 18] = [rotateArc(vlarc, this.rot + 2)];
        this.carcs[(5 + 3 * this.rot) % 18] = reverseCArc(
            this.carcs[(6 + 3 * this.rot) % 18]
        );
        this.carcs[(15 + 3 * this.rot) % 18] = [rotateArc(vlarc, this.rot + 5)];
        this.carcs[(14 + 3 * this.rot) % 18] = reverseCArc(
            this.carcs[(15 + 3 * this.rot) % 18]
        );
        if (this.o0 == 0) {
            this.carcs[(0 + 3 * this.rot) % 18] = [rotateArc(vlarc, this.rot)];
            this.carcs[(17 + 3 * this.rot) % 18] = reverseCArc(
                this.carcs[(0 + 3 * this.rot) % 18]
            );
            this.carcs[(1 + 3 * this.rot) % 18] = [rotateArc(larc, this.rot)];
            this.carcs[(2 + 3 * this.rot) % 18] = rotateCArc(
                [b0, reverseArc(larc)],
                this.rot
            );
            this.carcs[(3 + 3 * this.rot) % 18] = rotateCArc(
                [b1, reverseArc(b0)],
                this.rot
            );
            this.carcs[(4 + 3 * this.rot) % 18] = rotateCArc(
                [barc, reverseArc(b1)],
                this.rot
            );
            this.carcs[(16 + 3 * this.rot) % 18] = [
                rotateArc(reverseArc(barc), this.rot)
            ];
        } else {
            this.carcs[(3 + 3 * this.rot) % 18] = [rotateArc(vlarc, this.rot + 1)];
            this.carcs[(2 + 3 * this.rot) % 18] = reverseCArc(
                this.carcs[(3 + 3 * this.rot) % 18]
            );
            this.carcs[(4 + 3 * this.rot) % 18] = [rotateArc(larc, this.rot + 1)];
            this.carcs[(1 + 3 * this.rot) % 18] = rotateCArc(
                reverseCArc([symb0, rotateArc(larc, 1)]),
                this.rot
            );
            this.carcs[(0 + 3 * this.rot) % 18] = rotateCArc(
                [symb0, reverseArc(symb1)],
                this.rot
            );
            this.carcs[(17 + 3 * this.rot) % 18] = rotateCArc(
                [symb1, barc],
                this.rot
            );
            this.carcs[(16 + 3 * this.rot) % 18] = [
                rotateArc(reverseArc(barc), this.rot)
            ];
        }
        if (this.o1 == 0) {
            this.carcs[(9 + 0 + 3 * this.rot) % 18] = [
                rotateArc(vlarc, this.rot + 3)
            ];
            this.carcs[(17 - 9 + 3 * this.rot) % 18] = reverseCArc(
                this.carcs[(9 + 0 + 3 * this.rot) % 18]
            );
            this.carcs[(9 + 1 + 3 * this.rot) % 18] = [rotateArc(larc, this.rot + 3)];
            this.carcs[(9 + 2 + 3 * this.rot) % 18] = rotateCArc(
                [b0, reverseArc(larc)],
                this.rot + 3
            );
            this.carcs[(9 + 3 + 3 * this.rot) % 18] = rotateCArc(
                [b1, reverseArc(b0)],
                this.rot + 3
            );
            this.carcs[(9 + 4 + 3 * this.rot) % 18] = rotateCArc(
                [barc, reverseArc(b1)],
                this.rot + 3
            );
            this.carcs[(16 - 9 + 3 * this.rot) % 18] = [
                rotateArc(reverseArc(barc), this.rot + 3)
            ];
        } else {
            this.carcs[(9 + 3 + 3 * this.rot) % 18] = [
                rotateArc(vlarc, this.rot + 1 + 3)
            ];
            this.carcs[(9 + 2 + 3 * this.rot) % 18] = reverseCArc(
                this.carcs[(9 + 3 + 3 * this.rot) % 18]
            );
            this.carcs[(9 + 4 + 3 * this.rot) % 18] = [
                rotateArc(larc, this.rot + 1 + 3)
            ];
            this.carcs[(9 + 1 + 3 * this.rot) % 18] = rotateCArc(
                reverseCArc([symb0, rotateArc(larc, 1)]),
                this.rot + 3
            );
            this.carcs[(9 + 0 + 3 * this.rot) % 18] = rotateCArc(
                [symb0, reverseArc(symb1)],
                this.rot + 3
            );
            this.carcs[(17 - 9 + 3 * this.rot) % 18] = rotateCArc(
                [symb1, barc],
                this.rot + 3
            );
            this.carcs[(16 - 9 + 3 * this.rot) % 18] = [
                rotateArc(reverseArc(barc), this.rot + 3)
            ];
        }

        // now turn angles (in 1/6th of turn)

        let turns = this.o0
            ? [2, 3, -2, 2, 2, -2, 2, -2, 2, -1, 3]
            : [2, 2, 3, 2, 3, -2, 2, -2, 2, -1, -2];
        turns.splice(
            7,
            0,
            ...(this.o1 ? [-1, 3, 2, 3, -2, 2, 2] : [-1, -2, 2, 2, 3, 2, 3])
        );
        // now apply rotation to routes
        this.turns = [];

        turns.forEach(
            (turn, entry) => (this.turns[(entry + this.rot * 3) % 18] = turn)
        );

        function reverseArc(arc) {
            /* returns arc running the opposite way of input arc */

            switch (arc.kind) {
                case "arc":
                    return {
                        kind: arc.kind,
                        radius: arc.radius,
                        center: Object.assign({}, arc.center),
                        a0: arc.a1,
                        a1: arc.a0,
                        ccw: !arc.ccw
                    };
                case "bezier":
                    return {
                        kind: arc.kind,
                        p0: Object.assign({}, arc.p3),
                        p1: Object.assign({}, arc.p2),
                        p2: Object.assign({}, arc.p1),
                        p3: Object.assign({}, arc.p0)
                    };
            }
        }

        function reverseCArc(carc) {
            /* returns arc running the opposite way of input compound arc */
            return carc.map((arc) => reverseArc(arc)).reverse();
        }

        function rotateArc(arc, angle) {
            // angle is given in 1/6th of turn (PI/3)
            switch (arc.kind) {
                case "arc":
                    return {
                        kind: arc.kind,
                        radius: arc.radius,
                        center: rotP(arc.center, angle),
                        a0: arc.a0 + angle,
                        a1: arc.a1 + angle,
                        ccw: arc.ccw
                    };
                case "bezier":
                    return {
                        kind: arc.kind,
                        p0: rotP(arc.p0, angle),
                        p1: rotP(arc.p1, angle),
                        p2: rotP(arc.p2, angle),
                        p3: rotP(arc.p3, angle)
                    };
            }
        } // rotateArc

        function rotateCArc(carc, angle) {
            return carc.map((arc) => rotateArc(arc, angle));
        } // rotatecArc

        function rotP(p, angle) {
            /* angle in 1/6th of turn */
            while (angle < 0) angle += 6;
            angle %= 6; // now sure angle is 0..5 (if it was an integer...)
            const c = tc[angle];
            const s = ts[angle];
            return { x: p.x * c - p.y * s, y: p.x * s + p.y * c };
        }
    } // constructor

    gotoNeighbor(point) {
        /* returns neighbor at given point, entry point for this neighbor
            neighbor may be undefined */

        const side = mfloor(point / 3);
        const konside = point % 3;
        const otherside = (side + 3) % 6;
        const otherpoint = 3 * otherside + 2 - konside;
        return {
            hexa: this.neighbors[side],
            point: otherpoint,
            fromHexa: this,
            fromPoint: point
        };
    }

    gotoExtNeighbor(point) {
        let edge, hexa;
        /* when going out of the grid, picks next point on the right */
        if (point % 3 != 2) return { hexa: this, point: point + 1, extTurn: 3 }; // on same edge - easy
        edge = (mfloor(point / 3) + 1) % 6; // next edge
        hexa = this.neighbors[edge];
        if (!hexa) return { hexa: this, point: (point + 1) % 18, extTurn: 4 }; // no neighbor on next edge
        return { hexa, point: (point + 13) % 18, extTurn: 2 };
    }
} // class Hexagon

//-----------------------------------------------------------------------------
function addPath(path, seg, minimax, first) {
    let hexa, point, ext;

    ({ hexa, point, ext } = seg);

    if (ext) hexa = ext.hexa;

    const xc = midx + (hexa.kx * 3 * radius) / 2;
    const yc = midy + (hexa.ky + hexa.kx / 2) * radius * rac3;

    if (ext) {
        let p = hexa.points[ext.point];
        path.lineTo(p.x, p.y);
        return;
    }

    // initial "moveTo" only required for bezier

    if (first && hexa.carcs[point][0].kind == "bezier") {
        let p = transf(hexa.carcs[point][0].p0);
        path.moveTo(p.x, p.y);
    }

    hexa.carcs[point].forEach((arc) => drawArc(transfArc(arc)));

    function drawArc(arc) {
        switch (arc.kind) {
            case "arc":
                let a0 = (arc.a0 * mPI) / 3;
                let a1 = (arc.a1 * mPI) / 3;
                path.arc(arc.center.x, arc.center.y, arc.radius, a0, a1, arc.ccw);
                minimax.checkArc(
                    arc.center.x,
                    arc.center.y,
                    arc.radius,
                    a0,
                    a1,
                    arc.ccw
                );
                break;
            case "bezier":
                //            path.moveTo(arc.p0.x, arc.p0.y);
                path.bezierCurveTo(
                    arc.p1.x,
                    arc.p1.y,
                    arc.p2.x,
                    arc.p2.y,
                    arc.p3.x,
                    arc.p3.y
                );
                minimax.checkCubic([arc.p0, arc.p1, arc.p2, arc.p3]);
                break;
        }
    }

    function transfArc(arc) {
        switch (arc.kind) {
            case "arc":
                return {
                    kind: arc.kind,
                    radius: arc.radius * radius,
                    center: transf(arc.center),
                    a0: arc.a0,
                    a1: arc.a1,
                    ccw: arc.ccw
                };
            case "bezier":
                return {
                    kind: arc.kind,
                    p0: transf(arc.p0),
                    p1: transf(arc.p1),
                    p2: transf(arc.p2),
                    p3: transf(arc.p3)
                };
        }
    } // transfArc
    function transf(p) {
        return { x: xc + radius * p.x, y: yc + radius * p.y };
    }
} // addPath

//-----------------------------------------------------------------------------
function makePath(loop) {
    const path = new Path2D();

    loop.minimax = new GradientControler();
    loop.segs.forEach((seg, k) => {
        addPath(path, seg, loop.minimax, k == 0);
    });
    path.closePath();
    loop.hue = colorful ? hue : intAlea(360);
    loop.sat = intAlea(50, 100);
    loop.invGrad = intAlea(2); // randomly inverse gradient
    loop.path = path;
    return path;
}

//-----------------------------------------------------------------------------

function makeTile() {
    /* called "makeTile" for historical reasons. Do not look for any tile here */

    let loop;

    loops = [];
    grid.forEach((hexa) => hexa.defineArcs());

    grid.forEach((hexa) => {
        for (let kin = 0; kin < 18; ++kin) {
            loop = makeLoop(hexa, kin);
            if (!loop) continue;
            loops.push(loop);
        } // for kin
    });
    //      console.log(loops);
    //-----------------------------------------------------------------------------

    function makeLoop(hexa, point) {
        let fromHexa, fromPoint, seg, extTurn;

        if (hexa.segs[point]) return false; // already exists, no new loop here
        let ihexa = hexa,
            ipoint = point;
        const segs = [];
        const loop = { segs }; // .segs,.turn,.closed, .path
        let turn = 0;

        do {
            seg = { hexa, point };
            segs.push(seg);

            if (!hexa) {
                // out of the grid
                ({ hexa, point, extTurn } = fromHexa.gotoExtNeighbor(fromPoint));
                seg.ext = { hexa, point }; // "ext" field in seg means "lineTo"
                turn += extTurn;
            } else {
                turn += hexa.turns[point];
                hexa.segs[point] = loop;
                ({ hexa, point, fromHexa, fromPoint } = hexa.gotoNeighbor(
                    hexa.routes[point]
                ));
            }
        } while (hexa != ihexa || point != ipoint);
        loop.turn = turn;

        if (loop.turn == 6) {
            // simplfied test for nested loops : only care about small circles
            if (loop.segs.length == 3) {
                let mayBeCircle = true;
                for (let k = 0; k < 3; ++k) {
                    if (!loop.segs[k].hexa) {
                        mayBeCircle = false;
                        break;
                    }
                    if (loop.segs[k].hexa.carcs[loop.segs[k].point].length != 1) {
                        mayBeCircle = false;
                        break;
                    }
                    if (loop.segs[k].point % 3) {
                        mayBeCircle = false;
                        break;
                    }
                } // for k
                if (mayBeCircle) loop.isSmallCircle = true;
            }
        }

        return loop;
    } // makeloop
} // makeTile

//-----------------------------------------------------------------------------
class GradientControler {
    /* to create linear gradients */
    /* creates a collection of points, then uses them to create a gradient */

    constructor() {
        this.points = [];
    } // constructor

    addPoint(p) {
        this.points.push(p);
    }

    checkCubic(cubic) {
        // cubic is an array of 4 points
        // only checks 5 points along the cubic, by splitting it into 4 parts

        let cub1, cub2, cub3, cub4;
        [cub1, cub2] = cutC(cubic, 0.5);
        cub3 = cutC(cub1, 0.5)[0];
        cub4 = cutC(cub2, 0.5)[0];
        this.addPoint(cubic[0]); // start (0)
        this.addPoint(cubic[3]); // end (1)
        this.addPoint(cub2[0]); // 0.5
        this.addPoint(cub3[3]); // 0.25
        this.addPoint(cub4[3]); // 0.75
    }

    checkArc(x, y, radius, a0, a1, ccw) {
        /* same parameters as CanvasRenderingContext2D.arc
             though accurate calculation could theoritecally be done,
             I divide arc into parts <= 30 degrees and only check their ends
             */
        if (ccw) [a0, a1] = [a1, a0];
        while (a1 >= a0 + m2PI) a1 -= m2PI;
        while (a1 < a0) a1 += m2PI;
        let nb = mceil(((a1 - a0) / mPI) * 6);
        let delta = (a1 - a0) / nb;
        for (let k = 0; k <= nb; ++k) {
            let ang = a0 + k * delta;
            this.addPoint({ x: x + radius * mcos(ang), y: y + radius * msin(ang) });
        }
    } // checkArc

    getGradient(ctx, angle) {
        let c = mcos(angle);
        let s = msin(angle);
        let mini = Infinity;
        let maxi = -Infinity;
        let p = { x: 0, y: 0 };

        this.points.forEach((np) => {
            const v = np.x * c + np.y * s;
            if (v < mini) {
                p = np;
                mini = v;
            }
            if (v > maxi) maxi = v;
        });

        /* returned gradient has no colorStop set */
        let delta;
        if (!isFinite(mini)) delta = 1;
        // no data, pick arbitrary difference
        else delta = maxi - mini;
        if (delta == 0) delta = 1; // only 1 point, or all at same position on gradient axis : pick arbitrary difference
        return ctx.createLinearGradient(p.x, p.y, p.x + delta * c, p.y + delta * s);
    } // getGradient
} // class GradientControler
//-----------------------------------------------------------------------------

function createGrid() {
    let cover = true; // true: hexagons will fully cover screen; false: hexagons do not overpass screen limits

    midx = maxx / 2; // will be used for center of Hexagon (0,0)
    midy = maxy / 2;
    // by making the center of the display be the center of an hexagon, we impose odd numbers of rows and columns.
    // midx and midy could be adjusted to have even numbers

    grid = new SuperArray();
    // create central hexagon, then grow...
    let toBeExamined = [];
    let hex = new Hexagon(0, 0);
    toBeExamined.push(hex);
    while (toBeExamined.length) {
        let cell = toBeExamined.shift();
        for (let k = 0; k < 6; ++k) {
            let nk = cell.getNeighborIndices(k);
            let ncell = grid.getItem(nk.ky, nk.kx);
            if (ncell) continue; // already exists
            ncell = new Hexagon(nk.ky, nk.kx);
            if (!cover && !ncell.isInside()) continue; // do not overpass limits
            grid.setItem(ncell, nk.ky, nk.kx);
            if (ncell.isOutside()) continue;
            toBeExamined.push(ncell);
        }
    }

    colorful = intAlea(2) || firstRun;

    let gr = ctx.createLinearGradient(0, maxy, maxx, 0);
    hue = intAlea(360);
    sat = intAlea(30, 50);
    withStroke = intAlea(2);
    gr.addColorStop(0, `hsl(${hue} ${sat}% 20%)`);
    gr.addColorStop(1, `hsl(${hue} ${sat}% 40%)`);
    ctx.fillStyle = gr;
    ctx.fillRect(0, 0, maxx, maxy);
    grid.forEach((cell) => cell.setNeighbors());

    makeTile();
    loops.forEach((loop) => makePath(loop));

    //      grid.forEach(hx => hx.drawHexagon());
} // createGrid

//-----------------------------------------------------------------------------

let animate;

{
    // scope for animate

    let animState = 0;

    animate = function (tStamp) {
        let message, gr;

        message = messages.shift();
        if (message && message.message == "reset") animState = 0;
        if (message && message.message == "click") animState = 0;
        window.requestAnimationFrame(animate);

        switch (animState) {
            case 0:
                if (!startOver()) break;
                ++animState;

            case 1:
                for (let pass = 0; pass < 2; ++pass) {
                    loops.forEach((loop) => {
                        if (loop.turn != 6) return; // do not draw open / reverse loops
                        if (loop.isSmallCircle && pass == 0) return;
                        if (!loop.isSmallCircle && pass != 0) return;
                        if (colorful) hue = intAlea(360);
                        gr = loop.minimax.getGradient(
                            ctx,
                            loop.invGrad ? angle : angle + mPI
                        );
                        gr.addColorStop(0, `hsl(${loop.hue} ${loop.sat}% 20%)`);
                        gr.addColorStop(0.4, `hsl(${loop.hue} ${loop.sat}% 40%)`);
                        gr.addColorStop(0.6, `hsl(${loop.hue} ${loop.sat}% 60%)`);
                        gr.addColorStop(1, `hsl(${loop.hue} ${loop.sat}% 80%)`);
                        ctx.fillStyle = gr;
                        ctx.fill(loop.path);
                    });
                }
                if (withStroke || firstRun) {
                    ctx.lineWidth = 0.5;
                    ctx.strokeStyle = "#000";
                    loops.forEach((loop) => {
                        ctx.stroke(loop.path);
                    });
                }

                ++animState;
                break;

            case 2:
                if (message && message.message == "move") {
                    angle = message.angle;
                    --animState;
                }
                break;
        } // switch
    }; // animate
} // scope for animate

//------------------------------------------------------------------------
//------------------------------------------------------------------------

function startOver() {
    // canvas dimensions

    maxx = window.innerWidth;
    maxy = window.innerHeight;

    canv.width = maxx;
    canv.height = maxy;
    ctx.lineJoin = "round";
    ctx.lineCap = "round";

    ctx.fillStyle = "#000";
    ctx.fillRect(0, 0, maxx, maxy);

    radius = msqrt(maxx * maxy) / intAlea(5, firstRun ? 8 : 20);

    createGrid();
    firstRun = false;
    return true;
} // startOver

//------------------------------------------------------------------------

function mouseClick(event) {
    messages.push({ message: "click" });
} // mouseClick
//------------------------------------------------------------------------

function mouseMove(event) {
    if (messages.length && messages[messages.length - 1].message == "move")
        messages.pop(); // no need cumulating move messages
    messages.push({
        message: "move",
        angle: matan2(event.clientY - maxy / 2, event.clientX - maxx / 2)
    });
} // mouseMove

//------------------------------------------------------------------------
//------------------------------------------------------------------------
// beginning of execution

{
    canv = document.createElement("canvas");
    canv.style.position = "absolute";
    document.body.appendChild(canv);
    ctx = canv.getContext("2d");
    //      canv.setAttribute('title', 'click me');
} // création CANVAS

angle = -mPI / 4;
canv.addEventListener("click", mouseClick);
canv.addEventListener("mousemove", mouseMove);

messages = [{ message: "reset" }];
requestAnimationFrame(animate);
