/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import MathlibExt.Computability.TuringMachine.BitOps
public import Mathlib.Tactic.Linarith

/-!
# The NP verifier for 3-COLOR

A witness gives vertex `i` the bits `w[2 i], w[2 i + 1]` (`col`): `00`, `01`, `10` are the colors
`0`, `1`, `2` and `11` is invalid (`okCol`). `colCheck x w` accepts iff `x` decodes to `(n, es)`
(`decodeE`, the inverse of `encodeE`), every edge endpoint is below `n`, `w` has at least `2 n`
bits, every vertex `i < n` has a valid color, and the ends of every edge `(u, v)` with `u ≠ v`
have different colors.

* Pure part: `col3Dec_iff` characterizes 3-COLOR by `colCheck` with witnesses at most twice as
  long as the input, through `colorable_iff` (a coloring `Fin n → Fin 3` of `edgeGraph n es` is
  a witness of `2 n` bits, by `code` and `uncode`).
* Machine: `prog`, a `TM2` component on seven stacks over the alphabet `Sym` (bits as
  `Sym.bit`). It reads `n` onto a counter, moves the first `n` color codes of `W` onto `P`
  (vertex `0` on top), rejecting a short witness or a code `11` (`loadS`), and then checks the
  edges one by one: it reads `u` and `v` onto counters (`readU`) and walks the colors of `P`
  towards both endpoints at once, parking the passed colors on `T` (`walkS`, `walk1S`, `mvP`).
  Running out of colors rejects an endpoint `≥ n`; the two endpoint colors are compared unless
  both counters run out together (a loop); `back` puts the colors back. `run`: it reaches `yes`
  iff `colCheck x w`, within `8 (|x| + |w| + 1)³` steps (linearly many, in fact).
* The bridge between the two is `colCheck_eq`: the check as the machine runs it, reading `n`,
  then the witness, then the edges one at a time (`edgeOk`, `edgesOk`).
-/

@[expose] public section

namespace Cslib.Complexity.Karp.ColVerify

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin
open Cslib.Complexity.SatVerifier (Sym)

/-! ### The verifier as a pure function -/

/-- The color code of vertex `i`: witness bits `2 i` and `2 i + 1` (`00`, `01`, `10` are the
colors `0`, `1`, `2`; `11` is invalid). -/
def col (w : List Bool) (i : ℕ) : Bool × Bool := (w.getD (2 * i) false, w.getD (2 * i + 1) false)

/-- A color code is valid: not `11`. -/
def okCol (c : Bool × Bool) : Bool := !(c.1 && c.2)

/-- The verifier: `x` decodes to `(n, es)`, every edge endpoint is below `n`, `w` has at least
`2 n` bits, every vertex `i < n` has a valid color, and the two ends of every edge `(u, v)` with
`u ≠ v` have different colors. -/
def colCheck (x w : List Bool) : Bool :=
  match decodeE x with
  | none => false
  | some (n, es) => es.all (fun e => decide (e.1 < n) && decide (e.2 < n)) &&
      decide (2 * n ≤ w.length) && (List.range n).all (fun i => okCol (col w i)) &&
      es.all fun e => e.1 == e.2 || col w e.1 != col w e.2

/-- The verifier's conditions, spelled out. -/
theorem colCheck_iff (x w : List Bool) : colCheck x w = true ↔
    ∃ n es, encodeE n es = x ∧ (∀ e ∈ es, e.1 < n ∧ e.2 < n) ∧ 2 * n ≤ w.length ∧
      (∀ i < n, okCol (col w i) = true) ∧ ∀ e ∈ es, e.1 ≠ e.2 → col w e.1 ≠ col w e.2 := by
  constructor
  · intro h
    unfold colCheck at h
    split at h
    · simp at h
    · rename_i n es hx
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
        Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨hb, hl⟩, hv⟩, hp⟩ := h
      exact ⟨n, es, encodeE_of_decodeE hx, hb, hl, hv, fun e he hne => (hp e he).resolve_left hne⟩
  · rintro ⟨n, es, rfl, hb, hl, hv, hp⟩
    rw [colCheck, decodeE_encodeE]
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
      Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    exact ⟨⟨⟨hb, hl⟩, hv⟩, fun e he => or_iff_not_imp_left.2 (hp e he)⟩

/-! ### Bridge to `SimpleGraph.Colorable` -/

/-- The code of a color: `0 ↦ 00`, `1 ↦ 01`, `2 ↦ 10`. -/
def code (c : Fin 3) : Bool × Bool := (decide (c = 2), decide (c = 1))

/-- The color of a code; the invalid code `11` reads as `0`. -/
def uncode : Bool × Bool → Fin 3
  | (false, true) => 1
  | (true, false) => 2
  | _ => 0

/-- `uncode` inverts `code`. -/
theorem uncode_code (c : Fin 3) : uncode (code c) = c := by
  fin_cases c <;> rfl

/-- Codes of colors are valid. -/
theorem okCol_code (c : Fin 3) : okCol (code c) = true := by
  fin_cases c <;> rfl

/-- `code` inverts `uncode` on valid codes. -/
theorem code_uncode {c : Bool × Bool} (h : okCol c = true) : code (uncode c) = c := by
  obtain ⟨a, b⟩ := c
  cases a <;> cases b <;> first | rfl | simp [okCol] at h

/-- Pairs of bits, flattened. -/
def flat (cs : List (Bool × Bool)) : List Bool := cs.flatMap fun c => [c.1, c.2]

/-- No pairs, no bits. -/
@[simp] theorem flat_nil : flat [] = [] := rfl

/-- The first pair comes first. -/
@[simp] theorem flat_cons (c : Bool × Bool) (cs : List (Bool × Bool)) :
    flat (c :: cs) = c.1 :: c.2 :: flat cs := rfl

/-- Flattening distributes over `++`. -/
theorem flat_append (cs ds : List (Bool × Bool)) : flat (cs ++ ds) = flat cs ++ flat ds :=
  List.flatMap_append

/-- Two bits per pair. -/
@[simp] theorem length_flat (cs : List (Bool × Bool)) : (flat cs).length = 2 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]; omega

/-- The color code of vertex `i` in flattened pairs is pair `i`. -/
theorem col_flat : ∀ (cs : List (Bool × Bool)) (i : ℕ), col (flat cs) i = cs.getD i (false, false)
  | [], i => by simp [col]
  | c :: cs, 0 => by simp [col]
  | c :: cs, i + 1 => by
      rw [List.getD_cons_succ, ← col_flat cs i, col, col, flat_cons,
        show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
      simp only [List.getD_cons_succ]

/-- The color code of vertex `i` in the flattened codes `f`. -/
theorem col_flat_ofFn {n : ℕ} (f : Fin n → Bool × Bool) (i : Fin n) :
    col (flat (List.ofFn f)) i = f i := by
  rw [col_flat, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

/-- **3-colorability by witness bits.** `edgeGraph n es` is 3-colorable iff some witness of
`2 n` bits gives each vertex a valid color, the two ends of every edge `(u, v)` with `u ≠ v`
getting different colors. -/
theorem colorable_iff (n : ℕ) (es : List (ℕ × ℕ)) (hb : ∀ e ∈ es, e.1 < n ∧ e.2 < n) :
    (edgeGraph n es).Colorable 3 ↔ ∃ w : List Bool, w.length = 2 * n ∧
      (∀ i < n, okCol (col w i) = true) ∧ ∀ e ∈ es, e.1 ≠ e.2 → col w e.1 ≠ col w e.2 := by
  constructor
  · rintro ⟨C⟩
    refine ⟨flat (List.ofFn fun i => code (C i)), by simp, fun i hi => ?_, fun e he hne => ?_⟩
    · rw [col_flat_ofFn _ ⟨i, hi⟩]
      exact okCol_code _
    · obtain ⟨h1, h2⟩ := hb e he
      rw [col_flat_ofFn _ ⟨e.1, h1⟩, col_flat_ofFn _ ⟨e.2, h2⟩]
      intro hc
      have hadj : (edgeGraph n es).Adj ⟨e.1, h1⟩ ⟨e.2, h2⟩ := by
        rw [edgeGraph, SimpleGraph.fromRel_adj]
        exact ⟨fun h => hne (Fin.mk.inj_iff.1 h), Or.inl he⟩
      exact C.valid hadj (by simpa [uncode_code] using congrArg uncode hc)
  · rintro ⟨w, -, hv, hp⟩
    refine ⟨SimpleGraph.Coloring.mk (fun i => uncode (col w i)) fun {i j} hadj hc => ?_⟩
    rw [edgeGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨hne, hij⟩ := hadj
    have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
    have hc' : col w i = col w j := by
      rw [← code_uncode (hv i i.isLt), ← code_uncode (hv j j.isLt), hc]
    rcases hij with h | h
    · exact hp _ h hne' hc'
    · exact hp _ h hne'.symm hc'.symm

/-- **3-COLOR is verified by `colCheck`**, with witnesses at most twice as long as the input. -/
theorem col3Dec_iff (x : List Bool) :
    col3Dec x = true ↔ ∃ w, w.length ≤ 2 * x.length ∧ colCheck x w = true := by
  simp only [col3Dec, decide_eq_true_eq, colCheck_iff]
  constructor
  · rintro ⟨n, es, rfl, hb, hc⟩
    obtain ⟨w, hl, hv, hp⟩ := (colorable_iff n es hb).1 hc
    refine ⟨w, ?_, n, es, rfl, hb, hl.ge, hv, hp⟩
    rw [hl, encodeE_eq]
    simp
  · rintro ⟨w, -, n, es, rfl, hb, hl, hv, hp⟩
    refine ⟨n, es, rfl, hb, (colorable_iff n es hb).2 ⟨flat ((List.range n).map (col w)),
      by simp, fun i hi => ?_, fun e he hne => ?_⟩⟩
    · rw [col_flat]
      simpa [List.getD_eq_getElem?_getD, hi] using hv i hi
    · obtain ⟨h1, h2⟩ := hb e he
      rw [col_flat, col_flat]
      simpa [List.getD_eq_getElem?_getD, h1, h2] using hp e he hne

/-! ### The machine's view of the check -/

/-- The witness colors of the vertices `0, …, n - 1`. -/
def cols (w : List Bool) (n : ℕ) : List (Bool × Bool) := (List.range n).map (col w)

/-- The verdict on one edge `(u, v)` with vertex colors `cs`: both ends are vertices, and a
non-loop's ends have different colors. -/
def edgeOk (cs : List (Bool × Bool)) (u v : ℕ) : Bool :=
  decide (u < cs.length) && decide (v < cs.length) &&
    (u == v || cs.getD u (false, false) != cs.getD v (false, false))

/-- The verdict of the edge loop on the rest `r` of the input: it parses, and every edge passes
`edgeOk`. -/
def edgesOk (cs : List (Bool × Bool)) (r : List Bool) : Bool :=
  match decodeEs r with
  | none => false
  | some es => es.all fun e => edgeOk cs e.1 e.2

/-- There are `n` witness colors. -/
@[simp] theorem length_cols (w : List Bool) (n : ℕ) : (cols w n).length = n := by
  simp [cols]

/-- Reading the color of a vertex `i < n`. -/
theorem getD_cols {w : List Bool} {n i : ℕ} (hi : i < n) :
    (cols w n).getD i (false, false) = col w i := by
  simp [cols, List.getD_eq_getElem?_getD, hi]

/-- Peeling the first two witness bits off. -/
theorem cols_cons_cons (a b : Bool) (w : List Bool) (n : ℕ) :
    cols (a :: b :: w) (n + 1) = (a, b) :: cols w n := by
  rw [cols, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1

/-- The verifier as the machine runs it: read `n`, check the witness, then the edge loop. -/
theorem colCheck_eq (x w : List Bool) : colCheck x w = match readUnaryLength x with
    | none => false
    | some (n, r) => decide (2 * n ≤ w.length) && (cols w n).all okCol && edgesOk (cols w n) r := by
  unfold colCheck decodeE
  cases hx : readUnaryLength x with
  | none => rfl
  | some p =>
      obtain ⟨n, r⟩ := p
      simp only [edgesOk]
      cases hr : decodeEs r with
      | none => simp
      | some es =>
          simp only [Option.map_some]
          rw [Bool.eq_iff_iff]
          simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
            cols, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, edgeOk,
            List.length_map, List.length_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
          constructor
          · rintro ⟨⟨⟨hb, hl⟩, hv⟩, hp⟩
            refine ⟨⟨hl, hv⟩, fun e he => ⟨hb e he, ?_⟩⟩
            rw [← cols, getD_cols (hb e he).1, getD_cols (hb e he).2]
            exact hp e he
          · rintro ⟨⟨hl, hv⟩, h⟩
            refine ⟨⟨⟨fun e he => (h e he).1, hl⟩, hv⟩, fun e he => ?_⟩
            have := (h e he).2
            rwa [← cols, getD_cols (h e he).1.1, getD_cols (h e he).1.2] at this

/-- An edge whose ends are both past the first color, seen from the second one. -/
theorem edgeOk_cons_succ (c : Bool × Bool) (cs : List (Bool × Bool)) (u v : ℕ) :
    edgeOk (c :: cs) (u + 1) (v + 1) = edgeOk cs u v := by
  simp [edgeOk]

/-! ### The machine -/

/-- Stacks: the input `X` and the witness `W`; the counter `N` (for `n`); the color stack `P`
(the `n` color codes, vertex `0` on top) and its scratch stack `T`; the endpoint counters `U`
and `V`. -/
inductive K | X | W | N | P | T | U | V
  deriving DecidableEq

/-- `K` is finite. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .W, .N, .P, .T, .U, .V], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Labels: read `n`; load the witness colors onto `T`; move them onto `P`; start an edge; read
its endpoints; walk the colors towards both endpoints; walk on towards the farther endpoint,
holding the nearer one's color `(a, b)` (counter `U` or `V`); restore `P`; accept; reject. -/
inductive Lab | rdN | load | mkP | edge | rdU | rdV | walk | walkU (a b : Bool)
  | walkV (a b : Bool) | back | yes | no
  deriving DecidableEq

/-- `Lab` is finite. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.rdN, .load, .mkP, .edge, .rdU, .rdV, .walk,
    .walkU false false, .walkU false true, .walkU true false, .walkU true true,
    .walkV false false, .walkV false true, .walkV true false, .walkV true true,
    .back, .yes, .no], by decide⟩
  complete := by
    rintro (_ | _ | _ | _ | _ | _ | _ | ⟨_ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ | _ | _ | _) <;> decide

/-- Statements of the verifier. -/
abbrev Stmt := TM2.Stmt (fun _ : K => Sym) Lab Bool

/-- Read a unary number off `X` onto the counter `c`: a `true` adds a unit, the `false`
terminator moves on to `next`, an exhausted `X` rejects. -/
def readU (c : K) (self next : Lab) : Stmt :=
  .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
    .pop .X (fun _ o => bitOf Sym.bit? o) <| .branch id
      (.push c (fun _ => .bit true) (.goto fun _ => self)) (.goto fun _ => next)

/-- Load one color per unit of `N`: pop two bits of `W` onto `T` (so the codes end up reversed
on `T`). Rejects if `W` runs out or a code is `11`. -/
def loadS : Stmt :=
  .pop .N (fun _ o => o.isSome) <| .branch id
    (.peek .W (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
      .pop .W (fun _ o => bitOf Sym.bit? o) <| .push .T (fun a => .bit a) <| .branch id
        (.peek .W (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
          .pop .W (fun _ o => bitOf Sym.bit? o) <| .push .T (fun b => .bit b) <|
            .goto fun b => if b then .no else .load)
        (.peek .W (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
          .pop .W (fun _ o => bitOf Sym.bit? o) <| .push .T (fun b => .bit b) <|
            .goto fun _ => .load))
    (.goto fun _ => .mkP)

/-- Start an edge: accept if `X` is exhausted, else read the endpoints. -/
def edgeS : Stmt :=
  .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .yes) (.goto fun _ => .rdU)

/-- Move the next color code `(a, b)` from `P` to `T` and go to `f a b`; reject if `P` is
empty (an endpoint past the last vertex). -/
def mvP (f : Bool → Bool → Lab) : Stmt :=
  .peek .P (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
    .pop .P (fun _ o => bitOf Sym.bit? o) <| .push .T (fun a => .bit a) <| .branch id
      (.pop .P (fun _ o => bitOf Sym.bit? o) <| .push .T (fun b => .bit b) <| .goto (f true))
      (.pop .P (fun _ o => bitOf Sym.bit? o) <| .push .T (fun b => .bit b) <| .goto (f false))

/-- A step of the joint walk: take a unit off both `U` and `V` and pass a color. When one
counter runs out first, its endpoint's color is the one passed, and the walk goes on towards
the other endpoint; when both run out together the edge is a loop, which passes once its
endpoint's color exists. -/
def walkS : Stmt :=
  .pop .U (fun _ o => o.isSome) <| .branch id
    (.pop .V (fun _ o => o.isSome) <| .branch id (mvP fun _ _ => .walk) (mvP .walkU))
    (.pop .V (fun _ o => o.isSome) <| .branch id (mvP .walkV) (mvP fun _ _ => .back))

/-- A step of the walk towards the farther endpoint (counter `k`), holding the nearer one's
color `(a, b)`: pass a color per unit of `k`; at the end the color passed is the farther
endpoint's, and the edge passes iff it differs from `(a, b)`. -/
def walk1S (k : K) (self : Lab) (a b : Bool) : Stmt :=
  .pop k (fun _ o => o.isSome) <| .branch id (mvP fun _ _ => self)
    (mvP fun a' b' => if a' = a ∧ b' = b then .no else .back)

/-- The verifier: read `n`, load the witness colors and check them, then check the edges one by
one, restoring the colors after each. -/
def prog : Lab → TM2.Stmt (fun _ : K => Sym) Lab Bool
  | .rdN => readU .N .rdN .load
  | .load => loadS
  | .mkP => moveB .T .P Sym.bit? Sym.bit .mkP .edge
  | .edge => edgeS
  | .rdU => readU .U .rdU .rdV
  | .rdV => readU .V .rdV .walk
  | .walk => walkS
  | .walkU a b => walk1S .U (.walkU a b) a b
  | .walkV a b => walk1S .V (.walkV a b) a b
  | .back => moveB .T .P Sym.bit? Sym.bit .back .edge
  | .yes => .halt
  | .no => .halt

/-- The start label. -/
def start : Lab := .rdN

/-! ### Runs of the phases -/

/-- A step whose label is known: some state and stacks follow. -/
theorem run_one {l l' : Lab} {v : Bool} {S : ∀ _ : K, List Sym}
    (h : (TM2.stepAux (prog l) v S).l = some l') :
    ∃ v' S', Run prog 1 ⟨some l, v, S⟩ ⟨some l', v', S'⟩ :=
  ⟨_, _, Run.single (by rw [← h])⟩

/-- Two updates of `a` interleaved with two of `b` leave the last of each. -/
theorem update_update_update_update {a b : K} (hab : a ≠ b) (S : ∀ _ : K, List Sym)
    (p p' t t' : List Sym) :
    update (update (update (update S a p) b t) a p') b t' = update (update S a p') b t' := by
  rw [update_comm hab.symm, update_idem, update_idem]

/-- `mvP` on a nonempty color stack: one color code moves to `T`. -/
theorem stepAux_mvP_cons (f : Bool → Bool → Lab) (c : Bool × Bool) (rest : List Sym) (s : Bool)
    (S : ∀ _ : K, List Sym) (hP : S .P = .bit c.1 :: .bit c.2 :: rest) :
    TM2.stepAux (mvP f) s S =
      ⟨some (f c.1 c.2), c.2, update (update S .P rest) .T (.bit c.2 :: .bit c.1 :: S .T)⟩ := by
  obtain ⟨a, b⟩ := c
  cases a <;> cases b <;>
    simp [mvP, TM2.stepAux, hP, bitOf, Sym.bit?, update_update_update_update]

/-- `mvP` on an exhausted color stack rejects. -/
theorem stepAux_mvP_nil (f : Bool → Bool → Lab) (s : Bool) (S : ∀ _ : K, List Sym)
    (hP : S .P = []) : TM2.stepAux (mvP f) s S = ⟨some .no, true, S⟩ := by
  simp [mvP, TM2.stepAux, hP]

/-- The walk-on step with the counter exhausted: the farther endpoint's color is next. -/
theorem stepAux_walk1S_nil (k : K) (self : Lab) (a b s : Bool) (St : ∀ _ : K, List Sym)
    (hk : St k = []) : TM2.stepAux (walk1S k self a b) s St =
      TM2.stepAux (mvP fun a' b' => if a' = a ∧ b' = b then .no else .back) false St := by
  have : update St k [] = St := by rw [← hk, update_eq_self]
  simp [walk1S, TM2.stepAux, hk, this]

/-- The walk-on step with a unit on the counter: pass a color. -/
theorem stepAux_walk1S_cons (k : K) (self : Lab) (a b s : Bool) (St : ∀ _ : K, List Sym)
    (j : ℕ) (hk : St k = cnt (Sym.bit true) (j + 1)) : TM2.stepAux (walk1S k self a b) s St =
      TM2.stepAux (mvP fun _ _ => self) true (update St k (cnt (Sym.bit true) j)) := by
  simp [walk1S, TM2.stepAux, hk, cnt_succ]

/-- The walk towards the farther endpoint: from `self` with `j` units on `k`, the colors `post`
on `P` and the colors `pre` passed so far (reversed) on `T`, it passes `j + 1` colors and
reaches `back` iff color `j` of `post` exists and differs from `(a, b)`. -/
theorem walk1_run {k : K} {self : Lab} {a b : Bool} (hp : prog self = walk1S k self a b)
    (hkP : k ≠ .P) (hkT : k ≠ .T) : ∀ (j : ℕ) (pre post : List (Bool × Bool)) (s : Bool)
    (St : ∀ _ : K, List Sym), St k = cnt (Sym.bit true) j → St .P = (flat post).map Sym.bit →
    St .T = (flat pre).reverse.map Sym.bit →
    ∃ s' S', RunLe prog (j + 1) ⟨some self, s, St⟩
      ⟨some (if j < post.length ∧ post.getD j (false, false) ≠ (a, b) then .back else .no), s',
        S'⟩ ∧
      (j < post.length → S' .P = (flat (post.drop (j + 1))).map Sym.bit ∧
        S' .T = (flat (pre ++ post.take (j + 1))).reverse.map Sym.bit ∧ S' k = [] ∧
        ∀ q, q ≠ k → q ≠ .P → q ≠ .T → S' q = St q)
  | j, pre, [], s, St, hk, hP, hT => by
      obtain ⟨s', S', h⟩ := run_one (l := self) (v := s) (S := St) (l' := .no) (by
        rw [hp]; cases j <;> simp [walk1S, mvP, TM2.stepAux, hk, hP, cnt_succ, hkP.symm])
      exact ⟨s', S', by simpa using h.le (by omega), fun h => by simp at h⟩
  | 0, pre, c :: post, s, St, hk, hP, hT => by
      refine ⟨c.2, update (update St .P ((flat post).map Sym.bit)) .T
        (.bit c.2 :: .bit c.1 :: St .T), (Run.single ?_).le le_rfl, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
      · rw [hp, stepAux_walk1S_nil k self a b s St hk,
          stepAux_mvP_cons _ c _ _ _ (by simpa using hP)]
        obtain ⟨c1, c2⟩ := c
        by_cases h : c1 = a ∧ c2 = b
        · obtain ⟨rfl, rfl⟩ := h
          simp
        · have h' : (c1, c2) ≠ (a, b) := fun e => h (Prod.mk.inj e)
          simp [h, h']
      · simp
      · simp [hT, flat_append]
      · simp [update_of_ne hkP, update_of_ne hkT, hk]
      · intro q h1 h2 h3
        simp [update_of_ne h2, update_of_ne h3]
  | j + 1, pre, c :: post, s, St, hk, hP, hT => by
      set St₁ := update (update (update St k (cnt (Sym.bit true) j)) .P
        ((flat post).map Sym.bit)) .T (.bit c.2 :: .bit c.1 :: St .T) with hSt₁
      have hstep : TM2.step prog ⟨some self, s, St⟩ = some ⟨some self, c.2, St₁⟩ := by
        simp only [TM2.step, Option.some.injEq]
        rw [hp, stepAux_walk1S_cons k self a b s St j hk,
          stepAux_mvP_cons _ c _ _ _ (by simpa [update_of_ne hkP.symm] using hP)]
        simp [hSt₁, update_of_ne hkT.symm]
      obtain ⟨s', S', hrun, hF⟩ := walk1_run hp hkP hkT j (pre ++ [c]) post c.2 St₁
        (by simp [hSt₁, update_of_ne hkP, update_of_ne hkT]) (by simp [hSt₁])
        (by simp [hSt₁, hT, flat_append])
      refine ⟨s', S', ?_, fun h => ?_⟩
      · have := ((Run.head hstep (Run.zero _)).le le_rfl).trans hrun
        simpa [add_comm 1] using this
      · obtain ⟨h1, h2, h3, h4⟩ := hF (by simpa using h)
        refine ⟨by simpa using h1, by simpa using h2, h3, fun q q1 q2 q3 => ?_⟩
        rw [h4 q q1 q2 q3, hSt₁, update_of_ne q3, update_of_ne q2, update_of_ne q1]

/-- A joint-walk step with a unit on both counters. -/
theorem stepAux_walkS_cons_cons (s : Bool) (St : ∀ _ : K, List Sym) (u v : ℕ)
    (hU : St .U = cnt (Sym.bit true) (u + 1)) (hV : St .V = cnt (Sym.bit true) (v + 1)) :
    TM2.stepAux walkS s St = TM2.stepAux (mvP fun _ _ => .walk) true
      (update (update St .U (cnt (Sym.bit true) u)) .V (cnt (Sym.bit true) v)) := by
  simp [walkS, TM2.stepAux, hU, hV, cnt_succ]

/-- A joint-walk step with `V` exhausted first: `v`'s color is next. -/
theorem stepAux_walkS_cons_nil (s : Bool) (St : ∀ _ : K, List Sym) (u : ℕ)
    (hU : St .U = cnt (Sym.bit true) (u + 1)) (hV : St .V = []) :
    TM2.stepAux walkS s St = TM2.stepAux (mvP .walkU) false
      (update St .U (cnt (Sym.bit true) u)) := by
  have : update (update St .U (cnt (Sym.bit true) u)) .V [] =
      update St .U (cnt (Sym.bit true) u) := by
    rw [← hV, ← update_of_ne (show K.V ≠ K.U by decide) (cnt (Sym.bit true) u) St, update_eq_self]
  simp [walkS, TM2.stepAux, hU, hV, cnt_succ, this]

/-- A joint-walk step with `U` exhausted first: `u`'s color is next. -/
theorem stepAux_walkS_nil_cons (s : Bool) (St : ∀ _ : K, List Sym) (v : ℕ)
    (hU : St .U = []) (hV : St .V = cnt (Sym.bit true) (v + 1)) :
    TM2.stepAux walkS s St = TM2.stepAux (mvP .walkV) true
      (update St .V (cnt (Sym.bit true) v)) := by
  have : update St .U [] = St := by rw [← hU, update_eq_self]
  simp [walkS, TM2.stepAux, hU, hV, cnt_succ, this]

/-- A joint-walk step with both counters exhausted: a loop. -/
theorem stepAux_walkS_nil_nil (s : Bool) (St : ∀ _ : K, List Sym) (hU : St .U = [])
    (hV : St .V = []) : TM2.stepAux walkS s St = TM2.stepAux (mvP fun _ _ => .back) false St := by
  have h₁ : update St .U [] = St := by rw [← hU, update_eq_self]
  have h₂ : update St .V [] = St := by rw [← hV, update_eq_self]
  simp [walkS, TM2.stepAux, hU, hV, h₁, h₂]

/-- The walk-on result decides `edgeOk` when one endpoint is the first color. -/
theorem edgeOk_zero_succ (c : Bool × Bool) (cs : List (Bool × Bool)) (v : ℕ) :
    edgeOk (c :: cs) 0 (v + 1) = true ↔ v < cs.length ∧ cs.getD v (false, false) ≠ (c.1, c.2) := by
  simp [edgeOk, ne_comm]

/-- The walk-on result decides `edgeOk` when one endpoint is the first color. -/
theorem edgeOk_succ_zero (c : Bool × Bool) (cs : List (Bool × Bool)) (u : ℕ) :
    edgeOk (c :: cs) (u + 1) 0 = true ↔ u < cs.length ∧ cs.getD u (false, false) ≠ (c.1, c.2) := by
  simp [edgeOk]

/-- The joint walk: from `walk` with `u` units on `U`, `v` on `V`, the colors `post` on `P` and
the colors `pre` passed so far (reversed) on `T`, it passes `max u v + 1` colors and reaches
`back` iff `edgeOk post u v`, with both counters empty. -/
theorem walk_run : ∀ (u v : ℕ) (pre post : List (Bool × Bool)) (s : Bool)
    (St : ∀ _ : K, List Sym), St .U = cnt (Sym.bit true) u → St .V = cnt (Sym.bit true) v →
    St .P = (flat post).map Sym.bit → St .T = (flat pre).reverse.map Sym.bit →
    ∃ s' S', RunLe prog (max u v + 1) ⟨some .walk, s, St⟩
      ⟨some (if edgeOk post u v then .back else .no), s', S'⟩ ∧
      (edgeOk post u v = true → S' .P = (flat (post.drop (max u v + 1))).map Sym.bit ∧
        S' .T = (flat (pre ++ post.take (max u v + 1))).reverse.map Sym.bit ∧
        S' .U = [] ∧ S' .V = [] ∧ ∀ q, q ≠ .U → q ≠ .V → q ≠ .P → q ≠ .T → S' q = St q)
  | u, v, pre, [], s, St, hU, hV, hP, hT => by
      obtain ⟨s', S', h⟩ := run_one (l := .walk) (v := s) (S := St) (l' := .no) (by
        cases u <;> cases v <;> simp [prog, walkS, mvP, TM2.stepAux, hU, hV, hP, cnt_succ])
      exact ⟨s', S', by simpa [edgeOk] using h.le (by omega), fun h => by simp [edgeOk] at h⟩
  | 0, 0, pre, c :: post, s, St, hU, hV, hP, hT => by
      refine ⟨c.2, update (update St .P ((flat post).map Sym.bit)) .T
        (.bit c.2 :: .bit c.1 :: St .T), (Run.single ?_).le le_rfl, fun _ => ⟨?_, ?_, ?_, ?_,
        fun q h1 h2 h3 h4 => by simp [update_of_ne h3, update_of_ne h4]⟩⟩
      · rw [prog, stepAux_walkS_nil_nil s St hU hV, stepAux_mvP_cons _ c _ _ _
          (by simpa using hP)]
        simp [edgeOk]
      · simp
      · simp [hT, flat_append]
      · simpa using hU
      · simpa using hV
  | 0, v + 1, pre, c :: post, s, St, hU, hV, hP, hT => by
      set St₁ := update (update (update St .V (cnt (Sym.bit true) v)) .P
        ((flat post).map Sym.bit)) .T (.bit c.2 :: .bit c.1 :: St .T) with hSt₁
      have hstep : TM2.step prog ⟨some .walk, s, St⟩ =
          some ⟨some (.walkV c.1 c.2), c.2, St₁⟩ := by
        simp only [TM2.step, Option.some.injEq]
        rw [prog, stepAux_walkS_nil_cons s St v hU hV, stepAux_mvP_cons _ c _ _ _
          (by simpa using hP)]
        simp [hSt₁]
      obtain ⟨s', S', hrun, hF⟩ := walk1_run (k := .V) (self := .walkV c.1 c.2) rfl
        (by decide) (by decide) v (pre ++ [c]) post c.2 St₁ (by simp [hSt₁]) (by simp [hSt₁])
        (by simp [hSt₁, hT, flat_append])
      refine ⟨s', S', ?_, fun h => ?_⟩
      · have := ((Run.head hstep (Run.zero _)).le le_rfl).trans hrun
        rw [if_congr (edgeOk_zero_succ c post v) rfl rfl]
        simpa [add_comm 1] using this
      · obtain ⟨h1, h2, h3, h4⟩ := hF ((edgeOk_zero_succ c post v).1 h).1
        refine ⟨by simpa using h1, by simpa using h2, ?_, h3, fun q q1 q2 q3 q4 => ?_⟩
        · rw [h4 .U (by decide) (by decide) (by decide), hSt₁]; simpa using hU
        · rw [h4 q q2 q3 q4, hSt₁, update_of_ne q4, update_of_ne q3, update_of_ne q2]
  | u + 1, 0, pre, c :: post, s, St, hU, hV, hP, hT => by
      set St₁ := update (update (update St .U (cnt (Sym.bit true) u)) .P
        ((flat post).map Sym.bit)) .T (.bit c.2 :: .bit c.1 :: St .T) with hSt₁
      have hstep : TM2.step prog ⟨some .walk, s, St⟩ =
          some ⟨some (.walkU c.1 c.2), c.2, St₁⟩ := by
        simp only [TM2.step, Option.some.injEq]
        rw [prog, stepAux_walkS_cons_nil s St u hU hV, stepAux_mvP_cons _ c _ _ _
          (by simpa using hP)]
        simp [hSt₁]
      obtain ⟨s', S', hrun, hF⟩ := walk1_run (k := .U) (self := .walkU c.1 c.2) rfl
        (by decide) (by decide) u (pre ++ [c]) post c.2 St₁ (by simp [hSt₁]) (by simp [hSt₁])
        (by simp [hSt₁, hT, flat_append])
      refine ⟨s', S', ?_, fun h => ?_⟩
      · have := ((Run.head hstep (Run.zero _)).le le_rfl).trans hrun
        rw [if_congr (edgeOk_succ_zero c post u) rfl rfl]
        simpa [add_comm 1] using this
      · obtain ⟨h1, h2, h3, h4⟩ := hF ((edgeOk_succ_zero c post u).1 h).1
        refine ⟨by simpa using h1, by simpa using h2, h3, ?_, fun q q1 q2 q3 q4 => ?_⟩
        · rw [h4 .V (by decide) (by decide) (by decide), hSt₁]; simpa using hV
        · rw [h4 q q1 q3 q4, hSt₁, update_of_ne q4, update_of_ne q3, update_of_ne q1]
  | u + 1, v + 1, pre, c :: post, s, St, hU, hV, hP, hT => by
      set St₁ := update (update (update (update St .U (cnt (Sym.bit true) u)) .V
        (cnt (Sym.bit true) v)) .P ((flat post).map Sym.bit)) .T
        (.bit c.2 :: .bit c.1 :: St .T) with hSt₁
      have hstep : TM2.step prog ⟨some .walk, s, St⟩ = some ⟨some .walk, c.2, St₁⟩ := by
        simp only [TM2.step, Option.some.injEq]
        rw [prog, stepAux_walkS_cons_cons s St u v hU hV, stepAux_mvP_cons _ c _ _ _
          (by simpa using hP)]
        simp [hSt₁]
      obtain ⟨s', S', hrun, hF⟩ := walk_run u v (pre ++ [c]) post c.2 St₁ (by simp [hSt₁])
        (by simp [hSt₁]) (by simp [hSt₁]) (by simp [hSt₁, hT, flat_append])
      have hm : max (u + 1) (v + 1) = max u v + 1 := Nat.succ_max_succ u v
      rw [edgeOk_cons_succ, hm]
      refine ⟨s', S', ?_, fun h => ?_⟩
      · have := ((Run.head hstep (Run.zero _)).le le_rfl).trans hrun
        simpa [add_comm 1] using this
      · obtain ⟨h1, h2, h3, h4, h5⟩ := hF h
        refine ⟨by simpa using h1, by simpa using h2, h3, h4, fun q q1 q2 q3 q4 => ?_⟩
        rw [h5 q q1 q2 q3 q4, hSt₁, update_of_ne q4, update_of_ne q3, update_of_ne q2,
          update_of_ne q1]

/-- `readU` on `k` in unary: `k + 1` steps to `next`, with `k` more units on the counter and
the rest of `X` left. -/
theorem readU_some {c : K} {self next : Lab} (hp : prog self = readU c self next)
    (hc : c ≠ .X) : ∀ (k j : ℕ) (r : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      St .X = (List.replicate k true ++ false :: r).map Sym.bit → St c = cnt (Sym.bit true) j →
      ∃ v' S', Run prog (k + 1) ⟨some self, v, St⟩ ⟨some next, v', S'⟩ ∧
        S' .X = r.map Sym.bit ∧ S' c = cnt (Sym.bit true) (k + j) ∧
        ∀ q, q ≠ .X → q ≠ c → S' q = St q := by
  intro k
  induction k with
  | zero =>
      intro j r v St hX hC
      simp only [List.replicate_zero, List.nil_append, List.map_cons] at hX
      refine ⟨false, update St .X (r.map Sym.bit), Run.single ?_, by simp, ?_,
        fun q hq _ => by simp [update_of_ne hq]⟩
      · simp [hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?]
      · rw [update_of_ne hc, hC, zero_add]
  | succ k ih =>
      intro j r v St hX hC
      simp only [List.replicate_succ, List.cons_append, List.map_cons] at hX
      set St₁ := update (update St .X ((List.replicate k true ++ false :: r).map Sym.bit)) c
        (Sym.bit true :: St c) with hSt₁
      obtain ⟨v', S', hrun, hX', hC', hF'⟩ := ih (j + 1) r true St₁
        (by simp [hSt₁, update_of_ne hc.symm]) (by simp [hSt₁, hC, cnt_succ])
      refine ⟨v', S', Run.head ?_ hrun, hX', by rw [hC']; congr 1; omega,
        fun q h1 h2 => by rw [hF' q h1 h2, hSt₁, update_of_ne h2, update_of_ne h1]⟩
      simp [TM2.step, hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?, hSt₁, update_of_ne hc]

/-- `readU` on an unterminated unary prefix rejects. -/
theorem readU_none {c : K} {self next : Lab} (hp : prog self = readU c self next)
    (hc : c ≠ .X) : ∀ (l : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      readUnaryLength l = none → St .X = l.map Sym.bit →
      ∃ v' S', RunLe prog (l.length + 1) ⟨some self, v, St⟩ ⟨some .no, v', S'⟩ := by
  intro l
  induction l with
  | nil =>
      intro v St _ hX
      obtain ⟨v', S', h⟩ := run_one (l := self) (v := v) (S := St) (l' := .no)
        (by simp [hp, readU, TM2.stepAux, hX])
      exact ⟨v', S', h.le (by simp)⟩
  | cons b l ih =>
      intro v St hl hX
      cases b with
      | false => simp [readUnaryLength] at hl
      | true =>
          have hl' : readUnaryLength l = none := by simpa [readUnaryLength] using hl
          obtain ⟨v', S', h⟩ := ih true
            (update (update St .X (l.map Sym.bit)) c (Sym.bit true :: St c)) hl'
            (by simp [update_of_ne hc.symm])
          refine ⟨v', S', (((Run.single ?_).le le_rfl).trans h).mono (by simp; omega)⟩
          simp [hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?, update_of_ne hc]

/-- The load phase: from `n` units on `N`, the witness `w` on `W` and `acc` on `T`, it reaches
`mkP` if `w` has at least `2 n` bits and the first `n` color codes are valid, and `no`
otherwise; on success those codes sit on `T`, reversed. -/
theorem load_run : ∀ (n : ℕ) (w acc : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
    St .N = cnt (Sym.bit true) n → St .W = w.map Sym.bit → St .T = acc.map Sym.bit →
    ∃ v' S', RunLe prog (n + 1) ⟨some .load, v, St⟩
      ⟨some (if 2 * n ≤ w.length ∧ (cols w n).all okCol = true then .mkP else .no), v', S'⟩ ∧
      (2 * n ≤ w.length ∧ (cols w n).all okCol = true →
        S' .T = ((flat (cols w n)).reverse ++ acc).map Sym.bit ∧
        ∀ q, q ≠ .N → q ≠ .W → q ≠ .T → S' q = St q) := by
  intro n
  induction n with
  | zero =>
      intro w acc v St hN hW hT
      refine ⟨false, update St .N [], (Run.single ?_).le le_rfl,
        fun _ => ⟨by simp [hT, cols], fun q hq _ _ => by simp [update_of_ne hq]⟩⟩
      simp [prog, loadS, TM2.stepAux, hN, cols]
  | succ n ih =>
      intro w acc v St hN hW hT
      match w with
      | [] =>
          obtain ⟨v', S', h⟩ := run_one (l := .load) (v := v) (S := St) (l' := .no)
            (by simp [prog, loadS, TM2.stepAux, hN, hW, cnt_succ])
          exact ⟨v', S', by simpa using h.le (by omega), fun h => by simp at h⟩
      | [a] =>
          obtain ⟨v', S', h⟩ := run_one (l := .load) (v := v) (S := St) (l' := .no)
            (by cases a <;> simp [prog, loadS, TM2.stepAux, hN, hW, cnt_succ, bitOf, Sym.bit?])
          have hc : ¬(2 * (n + 1) ≤ [a].length ∧ (cols [a] (n + 1)).all okCol = true) := by
            simp only [List.length_singleton]; omega
          exact ⟨v', S', by rw [ite_eq_right hc]; exact h.le (by omega), fun h => absurd h hc⟩
      | a :: b :: w =>
          by_cases hab : a = true ∧ b = true
          · obtain ⟨rfl, rfl⟩ := hab
            obtain ⟨v', S', h⟩ := run_one (l := .load) (v := v) (S := St) (l' := .no)
              (by simp [prog, loadS, TM2.stepAux, hN, hW, cnt_succ, bitOf, Sym.bit?])
            refine ⟨v', S', by simpa [cols_cons_cons, okCol] using h.le (by omega),
              fun h => by simp [cols_cons_cons, okCol] at h⟩
          · set St₁ := update (update (update St .N (cnt (Sym.bit true) n)) .W
              (w.map Sym.bit)) .T (Sym.bit b :: Sym.bit a :: St .T) with hSt₁
            have hstep : TM2.step prog ⟨some .load, v, St⟩ = some ⟨some .load, b, St₁⟩ := by
              simp only [TM2.step, Option.some.injEq]
              cases a <;> cases b
              all_goals first
                | exact absurd ⟨rfl, rfl⟩ hab
                | simp [prog, loadS, TM2.stepAux, hN, hW, cnt_succ, bitOf, Sym.bit?, hSt₁,
                    update_update_update_update]
            obtain ⟨v', S', hrun, hF⟩ := ih w (b :: a :: acc) b St₁ (by simp [hSt₁])
              (by simp [hSt₁]) (by simp [hSt₁, hT])
            have hok : okCol (a, b) = true := by cases a <;> cases b <;> simp_all [okCol]
            have hc : (2 * (n + 1) ≤ (a :: b :: w).length ∧
                (cols (a :: b :: w) (n + 1)).all okCol = true) ↔
                (2 * n ≤ w.length ∧ (cols w n).all okCol = true) := by
              simp [cols_cons_cons, hok]; omega
            refine ⟨v', S', ?_, fun h => ?_⟩
            · have := ((Run.head hstep (Run.zero _)).le le_rfl).trans hrun
              rw [if_congr hc rfl rfl]
              simpa [add_comm 1] using this
            · obtain ⟨h1, h2⟩ := hF (hc.1 h)
              refine ⟨by simp [h1, cols_cons_cons], fun q q1 q2 q3 => ?_⟩
              rw [h2 q q1 q2 q3, hSt₁, update_of_ne q3, update_of_ne q2, update_of_ne q1]

/-- A parsed edge, then the rest: the loop's verdict is the edge's and the rest's. -/
theorem edgesOk_of_some_some (cs : List (Bool × Bool)) {r r₁ r₂ : List Bool} {u v : ℕ}
    (h₁ : readUnaryLength r = some (u, r₁)) (h₂ : readUnaryLength r₁ = some (v, r₂)) :
    edgesOk cs r = (edgeOk cs u v && edgesOk cs r₂) := by
  unfold edgesOk
  rw [decodeEs_of_some_some h₁ h₂]
  cases decodeEs r₂ <;> simp

/-- Putting the passed colors back: `back` moves `T` onto `P`. -/
theorem back_run (pre post : List (Bool × Bool)) (s : Bool) (St : ∀ _ : K, List Sym)
    (hP : St .P = (flat post).map Sym.bit) (hT : St .T = (flat pre).reverse.map Sym.bit) :
    ∃ s' S', Run prog (2 * pre.length + 1) ⟨some .back, s, St⟩ ⟨some .edge, s', S'⟩ ∧
      S' .T = [] ∧ S' .P = (flat (pre ++ post)).map Sym.bit ∧
      ∀ q, q ≠ .T → q ≠ .P → S' q = St q := by
  obtain ⟨s', S', h, hT', hP', hF⟩ := moveB_run (M := prog) (self := .back) (next := .edge) rfl
    (show K.T ≠ K.P by decide) (flat pre).reverse ((flat pre).reverse.map Sym.bit) [] s St
    (by simp [hT]) (by simp [IsBitBlock, Sym.bit?, Function.comp_def]) (by simp [EndsBitBlock])
  exact ⟨s', S', by simpa using h, hT', by simp [hP', hP, flat_append, List.map_reverse], hF⟩

/-- The edge loop: from `edge` with the rest `r` of the input on `X`, the colors `cs` on `P`
and `T`, `U`, `V` empty, it reaches `yes` iff `edgesOk cs r`, within `4 |r| + 1` steps. -/
theorem edges_run (cs : List (Bool × Bool)) (r : List Bool) : ∀ (s : Bool)
    (St : ∀ _ : K, List Sym), St .X = r.map Sym.bit → St .P = (flat cs).map Sym.bit →
    St .T = [] → St .U = [] → St .V = [] →
    ∃ s' S', RunLe prog (4 * r.length + 1) ⟨some .edge, s, St⟩
      ⟨some (if edgesOk cs r then .yes else .no), s', S'⟩ := by
  induction hL : r.length using Nat.strong_induction_on generalizing r with
  | _ L ih =>
  intro s St hX hP hT hU hV
  subst hL
  by_cases hr : r = []
  · subst hr
    obtain ⟨s', S', h⟩ := run_one (l := .edge) (v := s) (S := St)
      (l' := if edgesOk cs [] then .yes else .no)
      (by simp [prog, edgeS, TM2.stepAux, hX, edgesOk, decodeEs_nil])
    exact ⟨s', S', h.le (by simp)⟩
  have hr₀ : Run prog 1 ⟨some .edge, s, St⟩ ⟨some .rdU, false, St⟩ := Run.single (by
    cases r with
    | nil => exact absurd rfl hr
    | cons b r => simp [prog, edgeS, TM2.stepAux, hX])
  have hlen : 1 ≤ r.length := by
    cases r with
    | nil => exact absurd rfl hr
    | cons b r => simp
  cases h₁ : readUnaryLength r with
  | none =>
      obtain ⟨s₁, S₁, r₁⟩ := readU_none (c := .U) (self := .rdU) (next := .rdV) rfl (by decide)
        r false St h₁ hX
      rw [edgesOk, decodeEs_of_none hr h₁]
      exact ⟨s₁, S₁, ((hr₀.le le_rfl).trans r₁).mono (by omega)⟩
  | some p =>
      obtain ⟨u, r₁⟩ := p
      have hx₁ := (readUnaryLength_eq_some_iff _ _ _).1 h₁
      obtain ⟨s₁, S₁, run₁, hX₁, hU₁, hF₁⟩ := readU_some (c := .U) (self := .rdU) (next := .rdV)
        rfl (by decide) u 0 r₁ false St (by rw [hX, hx₁]) (by simp [hU])
      have hl₁ : r.length = u + 1 + r₁.length := by rw [hx₁]; simp; omega
      cases h₂ : readUnaryLength r₁ with
      | none =>
          obtain ⟨s₂, S₂, run₂⟩ := readU_none (c := .V) (self := .rdV) (next := .walk) rfl
            (by decide) r₁ s₁ S₁ h₂ hX₁
          rw [edgesOk, decodeEs_of_some_none h₁ h₂]
          exact ⟨s₂, S₂, (((hr₀.le le_rfl).trans (run₁.le le_rfl)).trans run₂).mono (by omega)⟩
      | some q =>
          obtain ⟨v, r₂⟩ := q
          have hx₂ := (readUnaryLength_eq_some_iff _ _ _).1 h₂
          obtain ⟨s₂, S₂, run₂, hX₂, hV₂, hF₂⟩ := readU_some (c := .V) (self := .rdV)
            (next := .walk) rfl (by decide) v 0 r₂ s₁ S₁ (by rw [hX₁, hx₂])
            (by rw [hF₁ .V (by decide) (by decide), hV]; rfl)
          have hl₂ : r₁.length = v + 1 + r₂.length := by rw [hx₂]; simp; omega
          have hS₂ : ∀ q, q ≠ .X → q ≠ .U → q ≠ .V → S₂ q = St q := fun q q1 q2 q3 => by
            rw [hF₂ q q1 q3, hF₁ q q1 q2]
          obtain ⟨s₃, S₃, run₃, hF₃⟩ := walk_run u v [] cs s₂ S₂
            (by rw [hF₂ .U (by decide) (by decide), hU₁]; simp) (by simpa using hV₂)
            (by rw [hS₂ .P (by decide) (by decide) (by decide), hP])
            (by rw [hS₂ .T (by decide) (by decide) (by decide), hT]; simp)
          rw [edgesOk_of_some_some cs h₁ h₂]
          by_cases he : edgeOk cs u v = true
          · rw [ite_eq_left he] at run₃
            obtain ⟨hP₃, hT₃, hU₃, hV₃, hF₃'⟩ := hF₃ he
            obtain ⟨s₄, S₄, run₄, hT₄, hP₄, hF₄⟩ := back_run (cs.take (max u v + 1))
              (cs.drop (max u v + 1)) s₃ S₃ hP₃ (by simpa using hT₃)
            have hlt : r₂.length < r.length := by omega
            obtain ⟨s₅, S₅, run₅⟩ := ih r₂.length (by omega) r₂ rfl s₄ S₄
              (by rw [hF₄ .X (by decide) (by decide),
                hF₃' .X (by decide) (by decide) (by decide) (by decide), hX₂])
              (by simpa using hP₄) hT₄
              (by rw [hF₄ .U (by decide) (by decide), hU₃])
              (by rw [hF₄ .V (by decide) (by decide), hV₃])
            refine ⟨s₅, S₅, ?_⟩
            rw [he, Bool.true_and]
            refine (((((hr₀.le le_rfl).trans (run₁.le le_rfl)).trans (run₂.le le_rfl)).trans
              run₃).trans ((run₄.le le_rfl).trans run₅)).mono ?_
            have ht : (cs.take (max u v + 1)).length ≤ max u v + 1 := List.length_take_le _ _
            have hm : max u v ≤ u + v := by omega
            omega
          · rw [ite_eq_right he] at run₃
            have he' : edgeOk cs u v = false := by simpa using he
            rw [he', Bool.false_and]
            refine ⟨s₃, S₃, ((((hr₀.le le_rfl).trans (run₁.le le_rfl)).trans
              (run₂.le le_rfl)).trans run₃).mono ?_⟩
            have hm : max u v ≤ u + v := by omega
            omega

/-- **The verifier machine.** From `start` with `x` on `X`, `w` on `W` and the other stacks
empty, `prog` reaches `yes` if `colCheck x w` and `no` otherwise, within
`8 (|x| + |w| + 1)³` steps (linearly many, in fact). -/
theorem run (x w : List Bool) (v : Bool) (St : ∀ _ : K, List Sym)
    (hX : St .X = x.map Sym.bit) (hW : St .W = w.map Sym.bit)
    (h0 : ∀ k, k ≠ .X → k ≠ .W → St k = []) :
    ∃ v' S', RunLe prog (8 * (x.length + w.length + 1) ^ 3) ⟨some start, v, St⟩
      ⟨some (if colCheck x w then .yes else .no), v', S'⟩ := by
  set L := x.length + w.length + 1 with hL
  have hL3 : L ≤ L ^ 3 := by
    have : 0 < L := by omega
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 3 := Nat.pow_le_pow_right this (by omega)
  rw [colCheck_eq]
  cases h₁ : readUnaryLength x with
  | none =>
      obtain ⟨v', S', h⟩ := readU_none (c := .N) (self := .rdN) (next := .load) rfl (by decide)
        x v St h₁ hX
      exact ⟨v', S', h.mono (by omega)⟩
  | some p =>
      obtain ⟨n, r⟩ := p
      dsimp only
      have hx := (readUnaryLength_eq_some_iff _ _ _).1 h₁
      have hxl : x.length = n + 1 + r.length := by rw [hx]; simp; omega
      obtain ⟨v₁, S₁, run₁, hX₁, hN₁, hF₁⟩ := readU_some (c := .N) (self := .rdN) (next := .load)
        rfl (by decide) n 0 r v St (by rw [hX, hx]) (by simp [h0 .N (by decide) (by decide)])
      obtain ⟨v₂, S₂, run₂, hF₂⟩ := load_run n w [] v₁ S₁ (by simpa using hN₁)
        (by rw [hF₁ .W (by decide) (by decide), hW])
        (by rw [hF₁ .T (by decide) (by decide), h0 .T (by decide) (by decide)]; rfl)
      by_cases hc : 2 * n ≤ w.length ∧ (cols w n).all okCol = true
      · rw [ite_eq_left hc] at run₂
        obtain ⟨hT₂, hF₂'⟩ := hF₂ hc
        have hS₂ : ∀ q, q ≠ .X → q ≠ .N → q ≠ .W → q ≠ .T → S₂ q = St q :=
          fun q q1 q2 q3 q4 => by rw [hF₂' q q2 q3 q4, hF₁ q q1 q2]
        obtain ⟨v₃, S₃, run₃, hT₃, hP₃, hF₃⟩ := moveB_run (M := prog) (self := .mkP)
          (next := .edge) rfl (show K.T ≠ K.P by decide) (flat (cols w n)).reverse
          ((flat (cols w n)).reverse.map Sym.bit) [] v₂ S₂ (by simpa using hT₂)
          (by simp [IsBitBlock, Sym.bit?, Function.comp_def]) (by simp [EndsBitBlock])
        obtain ⟨v₄, S₄, run₄⟩ := edges_run (cols w n) r v₃ S₃
          (by rw [hF₃ .X (by decide) (by decide), hF₂' .X (by decide) (by decide) (by decide),
            hX₁])
          (by rw [hP₃, hS₂ .P (by decide) (by decide) (by decide) (by decide),
            h0 .P (by decide) (by decide)]; simp [List.map_reverse])
          hT₃
          (by rw [hF₃ .U (by decide) (by decide), hS₂ .U (by decide) (by decide) (by decide)
            (by decide), h0 .U (by decide) (by decide)])
          (by rw [hF₃ .V (by decide) (by decide), hS₂ .V (by decide) (by decide) (by decide)
            (by decide), h0 .V (by decide) (by decide)])
        have hb : (decide (2 * n ≤ w.length) && (cols w n).all okCol) = true := by
          simpa using hc
        simp only [hb, Bool.true_and]
        refine ⟨v₄, S₄, ((((run₁.le le_rfl).trans run₂).trans (run₃.le le_rfl)).trans
          run₄).mono ?_⟩
        simp only [List.length_reverse, length_flat, length_cols]
        nlinarith
      · rw [ite_eq_right hc] at run₂
        have hb : (decide (2 * n ≤ w.length) && (cols w n).all okCol) = false := by
          rw [Bool.eq_false_iff]
          intro h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact hc h
        simp only [hb, Bool.false_and]
        exact ⟨v₂, S₂, ((run₁.le le_rfl).trans run₂).mono (by nlinarith)⟩

/-! ### Deprecated aliases: the edge-list parser moved to `Karp.Color` -/

@[deprecated (since := "2026-10-15")]
alias length_lt_of_readUnaryLength := Karp.length_lt_of_readUnaryLength
@[deprecated (since := "2026-10-15")] alias decodeEs := Karp.decodeEs
@[deprecated (since := "2026-10-15")] alias decodeE := Karp.decodeE
@[deprecated (since := "2026-10-15")] alias edgeBits := Karp.edgeBits
@[deprecated (since := "2026-10-15")] alias decodeEs_nil := Karp.decodeEs_nil
@[deprecated (since := "2026-10-15")] alias decodeEs_of_none := Karp.decodeEs_of_none
@[deprecated (since := "2026-10-15")] alias decodeEs_of_some_none := Karp.decodeEs_of_some_none
@[deprecated (since := "2026-10-15")] alias decodeEs_of_some_some := Karp.decodeEs_of_some_some
@[deprecated (since := "2026-10-15")] alias decodeEs_edgeBits := Karp.decodeEs_edgeBits
@[deprecated (since := "2026-10-15")] alias edgeBits_of_decodeEs := Karp.edgeBits_of_decodeEs
@[deprecated (since := "2026-10-15")] alias encodeE_eq := Karp.encodeE_eq
@[deprecated (since := "2026-10-15")] alias decodeE_encodeE := Karp.decodeE_encodeE
@[deprecated (since := "2026-10-15")] alias encodeE_of_decodeE := Karp.encodeE_of_decodeE

end Cslib.Complexity.Karp.ColVerify
