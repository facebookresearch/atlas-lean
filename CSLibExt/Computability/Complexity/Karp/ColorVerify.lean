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

/-- **Color code of a vertex in a witness.** The color code of vertex $i$ in a bit string $w$ is
the pair of bits at positions $2i$ and $2i + 1$ of $w$ (counting from $0$), where a position past
the end of $w$ reads as $0$. The codes $00$, $01$, $10$ stand for the colors $0$, $1$, $2$; $11$
is invalid. -/
def col (w : List Bool) (i : ℕ) : Bool × Bool := (w.getD (2 * i) false, w.getD (2 * i + 1) false)

/-- **Valid color code.** A color code, a pair of bits $(c_1, c_2)$, is valid when it is not
$11$, that is, when $c_1$ and $c_2$ are not both $1$. -/
def okCol (c : Bool × Bool) : Bool := !(c.1 && c.2)

/-- **The 3-COLOR verifier.** The verifier accepts an input $x$ and a witness $w$ (bit strings)
iff $x$ decodes to a number $n$ and an edge list $E$, every endpoint of an edge in $E$ is less
than $n$, $w$ has at least $2n$ bits, every vertex $i < n$ has a valid color code in $w$ (bits
$2i$ and $2i + 1$, not $11$), and the two ends of every edge $(u, v) \in E$ with $u \ne v$ have
different color codes. -/
def colCheck (x w : List Bool) : Bool :=
  match decodeE x with
  | none => false
  | some (n, es) => es.all (fun e => decide (e.1 < n) && decide (e.2 < n)) &&
      decide (2 * n ≤ w.length) && (List.range n).all (fun i => okCol (col w i)) &&
      es.all fun e => e.1 == e.2 || col w e.1 != col w e.2

/-- **Acceptance condition of the 3-COLOR verifier.** For all bit strings $x$ and $w$, the verifier
accepts $(x, w)$ iff there are a natural number $n$ and a list $E$ of pairs of natural numbers
such that $x$ is the encoding of the graph with $n$ vertices and edge list $E$, both entries of
every pair in $E$ are less than $n$, $w$ has at least $2n$ bits, the color code of every vertex
$i < n$ in $w$ is valid, and for every $(u, v) \in E$ with $u \ne v$ the color codes of $u$ and
$v$ in $w$ differ. -/
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

/-- **Two-bit code of a color.** The code of a color $c \in \{0, 1, 2\}$ is the pair of bits whose
first bit is $1$ iff $c = 2$ and whose second bit is $1$ iff $c = 1$: $0 \mapsto 00$,
$1 \mapsto 01$ and $2 \mapsto 10$. -/
def code (c : Fin 3) : Bool × Bool := (decide (c = 2), decide (c = 1))

/-- **Decoding a color code.** The color in $\{0, 1, 2\}$ of a pair of bits $(a, b)$, writing $0$
for false and $1$ for true: $(0, 1)$ decodes to $1$, $(1, 0)$ decodes to $2$, and both $(0, 0)$
and the invalid code $(1, 1)$ decode to $0$. -/
def uncode : Bool × Bool → Fin 3
  | (false, true) => 1
  | (true, false) => 2
  | _ => 0

/-- **Decoding a color code recovers the color.** For every color $c \in \{0, 1, 2\}$, decoding
the two-bit code of $c$ (where $0 \mapsto 00$, $1 \mapsto 01$, $2 \mapsto 10$) gives back $c$. -/
theorem uncode_code (c : Fin 3) : uncode (code c) = c := by
  fin_cases c <;> rfl

/-- **Color codes are valid.** For each color $c \in \{0, 1, 2\}$, the code of $c$ (which is
$00$, $01$ or $10$) is a valid color code, that is, it is not $11$. -/
theorem okCol_code (c : Fin 3) : okCol (code c) = true := by
  fin_cases c <;> rfl

/-- **Re-encoding a decoded valid color.** For every valid color code $c$ (a pair of bits other
than $11$), the code of the color that $c$ decodes to is $c$. -/
theorem code_uncode {c : Bool × Bool} (h : okCol c = true) : code (uncode c) = c := by
  obtain ⟨a, b⟩ := c
  cases a <;> cases b <;> first | rfl | simp [okCol] at h

/-- **Flattening pairs of bits.** The flattening of a list $[(a_1, b_1), \dots, (a_k, b_k)]$ of
pairs of bits is the list of bits $[a_1, b_1, \dots, a_k, b_k]$. -/
def flat (cs : List (Bool × Bool)) : List Bool := cs.flatMap fun c => [c.1, c.2]

/-- **Flattening the empty list.** The flattening of the empty list of pairs of bits is the empty
list of bits. -/
@[simp] theorem flat_nil : flat [] = [] := rfl

/-- **Flattening a nonempty list.** For a pair of bits $c = (a, b)$ and a list $cs$ of pairs of
bits, the flattening of the list with head $c$ and tail $cs$ is the list with $a$ first, then $b$,
then the flattening of $cs$. -/
@[simp] theorem flat_cons (c : Bool × Bool) (cs : List (Bool × Bool)) :
    flat (c :: cs) = c.1 :: c.2 :: flat cs := rfl

/-- **Flattening a concatenation.** For lists $cs$ and $ds$ of pairs of bits, the flattening of
the concatenation of $cs$ and $ds$ is the concatenation of the flattening of $cs$ and the
flattening of $ds$. -/
theorem flat_append (cs ds : List (Bool × Bool)) : flat (cs ++ ds) = flat cs ++ flat ds :=
  List.flatMap_append

/-- **Length of a flattening.** For every list $cs$ of pairs of bits, the flattening of $cs$ has
length $2|cs|$, two bits per pair. -/
@[simp] theorem length_flat (cs : List (Bool × Bool)) : (flat cs).length = 2 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]; omega

/-- **Color codes of flattened pairs.** For every list $cs$ of pairs of bits and every natural
number $i$, the color code of vertex $i$ in the flattening of $cs$ is the $i$-th pair of $cs$
(counting from $0$) if $i$ is less than the length of $cs$, and $00$ otherwise. -/
theorem col_flat : ∀ (cs : List (Bool × Bool)) (i : ℕ), col (flat cs) i = cs.getD i (false, false)
  | [], i => by simp [col]
  | c :: cs, 0 => by simp [col]
  | c :: cs, i + 1 => by
      rw [List.getD_cons_succ, ← col_flat cs i, col, col, flat_cons,
        show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
      simp only [List.getD_cons_succ]

/-- **Color codes of a flattened coloring.** For every $n$, every map $f$ from $\{0, \dots, n - 1\}$
to pairs of bits and every $i < n$, the color code of vertex $i$ in the flattening of the list
$f(0), \dots, f(n - 1)$ is $f(i)$. -/
theorem col_flat_ofFn {n : ℕ} (f : Fin n → Bool × Bool) (i : Fin n) :
    col (flat (List.ofFn f)) i = f i := by
  rw [col_flat, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

/-- **3-colorability by witness bits.** Let $n \in \mathbb{N}$ and let $es$ be a list of pairs of
natural numbers whose entries are all less than $n$. The graph on the vertices $0, \dots, n-1$
with edge list $es$ (symmetrized, loops dropped) is 3-colorable iff there is a list $w$ of exactly
$2n$ bits such that, writing the color code of vertex $i$ for the pair of bits $2i$ and $2i+1$ of
$w$, the color code of every vertex $i < n$ is valid (not $11$), and for every edge $(u, v)$ in
$es$ with $u \ne v$ the color codes of $u$ and $v$ differ. -/
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

/-- **3-COLOR is verified by the witness check.** A bit string $x$ is in 3-COLOR iff some bit
string $w$ of length at most $2|x|$ is accepted together with $x$ by the 3-COLOR verifier. -/
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

/-- **Witness colors of the first $n$ vertices.** For a bit list $w$ and $n \in \mathbb{N}$, the
list of the color codes of the vertices $0, 1, \dots, n-1$ in $w$, in that order, where the color
code of vertex $i$ is the pair of bits $2i$ and $2i+1$ of $w$ (a missing bit reads as false). -/
def cols (w : List Bool) (n : ℕ) : List (Bool × Bool) := (List.range n).map (col w)

/-- **Edge verdict.** For a list $cs$ of color codes (pairs of bits), one per vertex, and
$u, v \in \mathbb{N}$, the edge $(u, v)$ passes iff $u$ and $v$ are both less than the length of
$cs$ and either $u = v$ or entries $u$ and $v$ of $cs$ differ. -/
def edgeOk (cs : List (Bool × Bool)) (u v : ℕ) : Bool :=
  decide (u < cs.length) && decide (v < cs.length) &&
    (u == v || cs.getD u (false, false) != cs.getD v (false, false))

/-- **Edge-loop verdict.** For a list $cs$ of color codes and a bit list $r$, the verdict is true
iff $r$ parses as a list of edges, each written as two unary numbers $u$ and $v$ (a number $k$ as
$k$ ones, then a zero), and every edge $(u, v)$ of that list passes the edge verdict with vertex
colors $cs$. -/
def edgesOk (cs : List (Bool × Bool)) (r : List Bool) : Bool :=
  match decodeEs r with
  | none => false
  | some es => es.all fun e => edgeOk cs e.1 e.2

/-- **Number of witness colors.** For every list of bits $w$ and every $n \in \mathbb{N}$, the
list of the witness color codes of the vertices $0, \dots, n - 1$ read from $w$ has length $n$. -/
@[simp] theorem length_cols (w : List Bool) (n : ℕ) : (cols w n).length = n := by
  simp [cols]

/-- **Reading a witness color.** For a list of bits $w$ and natural numbers $i$ and $n$, write
$c_w(j)$ for the color code of vertex $j$ in $w$: the pair of bits $2j$ and $2j + 1$ of $w$
(counting from $0$), each read as false past the end of $w$. If $i < n$, then entry $i$
(counting from $0$) of the list $c_w(0), \dots, c_w(n - 1)$ of witness colors is $c_w(i)$. -/
theorem getD_cols {w : List Bool} {n i : ℕ} (hi : i < n) :
    (cols w n).getD i (false, false) = col w i := by
  simp [cols, List.getD_eq_getElem?_getD, hi]

/-- **Peeling a vertex off the witness colors.** For bits $a, b$, a bit list $w$ and
$n \in \mathbb{N}$, the color codes of the vertices $0, \dots, n$ read from the bit list $a, b, w$
(the list $w$ with $a$ and $b$ prepended) are $(a, b)$ followed by the color codes of the vertices
$0, \dots, n-1$ read from $w$. -/
theorem cols_cons_cons (a b : Bool) (w : List Bool) (n : ℕ) :
    cols (a :: b :: w) (n + 1) = (a, b) :: cols w n := by
  rw [cols, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1

/-- **The 3-COLOR verifier as an edge loop.** For all bit strings $x$ and $w$, the verifier accepts
$(x, w)$ iff reading a unary prefix $1^n 0$ off $x$ succeeds, giving $n$ and the rest $r$ of $x$,
and then $w$ has at least $2n$ bits, each of the witness colors $c_0, \dots, c_{n-1}$ of $w$ is
valid (not $11$), and the edge loop accepts $r$ with the vertex colors $c_0, \dots, c_{n-1}$. -/
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

/-- **Shifting the edge verdict past the first color.** For a color code $c$, a list $cs$ of color
codes and $u, v \in \mathbb{N}$, the edge verdict for $(u + 1, v + 1)$ with vertex colors $c$
followed by $cs$ equals the edge verdict for $(u, v)$ with vertex colors $cs$. -/
theorem edgeOk_cons_succ (c : Bool × Bool) (cs : List (Bool × Bool)) (u v : ℕ) :
    edgeOk (c :: cs) (u + 1) (v + 1) = edgeOk cs u v := by
  simp [edgeOk]

/-! ### The machine -/

/-- **Stacks of the 3-COLOR verifier.** The verifier has seven stacks: the input $X$ and the
witness $W$; the counter $N$ (for the number $n$ of vertices); the color stack $P$ (the $n$ color
codes, vertex $0$ on top) and its scratch stack $T$; and the endpoint counters $U$ and $V$. -/
inductive K | X | W | N | P | T | U | V
  deriving DecidableEq

/-- `K` is finite. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .W, .N, .P, .T, .U, .V], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Labels of the 3-COLOR verifier.** The labels are: read the number $n$ of vertices onto the
counter stack $N$; load the witness colors onto the scratch stack $T$; move them onto the color
stack $P$; start an edge; read its first endpoint onto the counter stack $U$; read its second
endpoint onto the counter stack $V$; walk the colors towards both endpoints; for each pair of
bits $(a, b)$, walk on towards the farther endpoint holding the nearer one's color $(a, b)$, one
label for counter $U$ and one for counter $V$; restore $P$; accept; reject. -/
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

/-- **Statements of the 3-COLOR verifier.** The type of statements of the verifier as a
multi-stack Turing machine in Mathlib's model: each of the seven stacks (the input, the witness,
the counter for the number of vertices, the color stack and its scratch stack, and the two
endpoint counters) holds symbols of the SAT verifier's alphabet, the labels are the verifier's
labels, and the internal state is a single bit. -/
abbrev Stmt := TM2.Stmt (fun _ : K => Sym) Lab Bool

/-- **Unary reader of the 3-COLOR verifier.** Given a counter stack $c$ and labels $s$ (its own)
and $t$ (the next): if the input stack $X$ is empty, reject; otherwise pop a bit off $X$; if it
is $1$, push a unit onto $c$ and go back to $s$, and if it is $0$, go to $t$. A symbol of $X$
that is not a bit is read as $0$. -/
def readU (c : K) (self next : Lab) : Stmt :=
  .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
    .pop .X (fun _ o => bitOf Sym.bit? o) <| .branch id
      (.push c (fun _ => .bit true) (.goto fun _ => self)) (.goto fun _ => next)

/-- **Load step of the 3-COLOR verifier.** If the counter stack $N$ is empty, go to the label
that moves the codes onto the color stack $P$. Otherwise pop one symbol off $N$ and two bits $a$,
$b$ off the witness stack $W$, pushing each onto the scratch stack $T$ as it is popped (so the
codes end up reversed on $T$), and go back to the load label; reject instead if $W$ is empty
when a bit is due, or if $a$ and $b$ are both $1$ (the invalid code $11$). A symbol of $W$ that
is not a bit is read as $0$. -/
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

/-- **Edge-loop start of the 3-COLOR verifier.** The verifier statement that begins checking the
next edge: if the input stack $X$ is empty it goes to the accepting label, and otherwise it goes
to the label that reads the first endpoint of the next edge onto the counter $U$. -/
def edgeS : Stmt :=
  .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .yes) (.goto fun _ => .rdU)

/-- **Moving one color code in the 3-COLOR verifier.** Given a map $f$ from pairs of bits to
labels: if the color stack $P$ is empty, reject (an endpoint lies past the last vertex);
otherwise pop two bits $a$, $b$ off $P$, push them onto the scratch stack $T$ in that order (so
$b$ ends on top), and go to the label $f(a, b)$. A missing or non-bit symbol is read as $0$. -/
def mvP (f : Bool → Bool → Lab) : Stmt :=
  .peek .P (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
    .pop .P (fun _ o => bitOf Sym.bit? o) <| .push .T (fun a => .bit a) <| .branch id
      (.pop .P (fun _ o => bitOf Sym.bit? o) <| .push .T (fun b => .bit b) <| .goto (f true))
      (.pop .P (fun _ o => bitOf Sym.bit? o) <| .push .T (fun b => .bit b) <| .goto (f false))

/-- **One step of the joint walk of the 3-COLOR verifier.** The statement pops the top symbol of
each of the endpoint counters $U$ and $V$ (a pop from an empty counter leaves it empty) and then
moves the next color code $(a, b)$ from the color stack $P$ onto the scratch stack $T$, rejecting
if $P$ is empty. It continues at the joint walk again if both counters were nonempty; at the walk
towards the endpoint of $U$, holding the color $(a, b)$, if only $U$ was nonempty (so $(a, b)$ is
the color of the endpoint of $V$); at the walk towards the endpoint of $V$, holding $(a, b)$, if
only $V$ was nonempty; and at the restoring label $\mathsf{back}$ if both were empty. In the last
case the edge is a loop, which passes once its endpoint's color exists. -/
def walkS : Stmt :=
  .pop .U (fun _ o => o.isSome) <| .branch id
    (.pop .V (fun _ o => o.isSome) <| .branch id (mvP fun _ _ => .walk) (mvP .walkU))
    (.pop .V (fun _ o => o.isSome) <| .branch id (mvP .walkV) (mvP fun _ _ => .back))

/-- **One step of the walk towards the farther endpoint.** Given a stack $k$ of the 3-COLOR
verifier (used as a counter), a label $\ell$ and a pair of bits $(a, b)$ (the color of the
nearer endpoint), the statement pops the top symbol of $k$ and then moves the next color code
$(a', b')$ from the color stack $P$ onto the scratch stack $T$, rejecting if $P$ is empty. If $k$
was nonempty it continues at $\ell$. Otherwise $(a', b')$ is the color of the farther endpoint,
and the statement rejects if $(a', b') = (a, b)$ and continues at the restoring label
$\mathsf{back}$ if not. -/
def walk1S (k : K) (self : Lab) (a b : Bool) : Stmt :=
  .pop k (fun _ o => o.isSome) <| .branch id (mvP fun _ _ => self)
    (mvP fun a' b' => if a' = a ∧ b' = b then .no else .back)

/-- **The 3-COLOR verifier machine.** The verifier is the program on the seven stacks $X$
(input), $W$ (witness), $N$, $P$, $T$, $U$, $V$, with internal state a bit, that runs as follows.
It reads the unary number $n$ off $X$ onto the counter $N$; loads the first $n$ color codes of
$W$ onto $T$, rejecting if $W$ runs out or one of these $n$ codes is $11$; moves the bits on top
of $T$ onto the color stack $P$; and then repeatedly starts an edge, accepting if $X$ is
exhausted and otherwise reading the endpoints $u$ and $v$ in unary onto the counters $U$ and
$V$, walking the colors from $P$ onto $T$ towards both endpoints, and moving the passed colors
back from $T$ onto $P$ before the next edge. Reading a number rejects if $X$ runs out; the walk
rejects if an endpoint has no color or if the two endpoints of a non-loop edge have the same
color. The accepting and rejecting labels halt. -/
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

/-- **Start label of the 3-coloring verifier.** The 3-coloring verifier machine starts at the
label that reads the vertex count $n$, written in unary on the input stack $X$, onto the counter
stack $N$. -/
def start : Lab := .rdN

/-! ### Runs of the phases -/

/-- **One step of the 3-COLOR verifier.** Let $l$ and $l'$ be labels, $v$ an internal state and
$S$ an assignment of stacks. If executing the verifier's statement at $l$ from state $v$ and
stacks $S$ ends at label $l'$, then for some internal state $v'$ and stacks $S'$ the verifier
goes in one step from label $l$ with state $v$ and stacks $S$ to label $l'$ with state $v'$ and
stacks $S'$. -/
theorem run_one {l l' : Lab} {v : Bool} {S : ∀ _ : K, List Sym}
    (h : (TM2.stepAux (prog l) v S).l = some l') :
    ∃ v' S', Run prog 1 ⟨some l, v, S⟩ ⟨some l', v', S'⟩ :=
  ⟨_, _, Run.single (by rw [← h])⟩

/-- **Interleaved updates of two stacks of the 3-COLOR verifier.** Let $a \ne b$ be two stacks of
the verifier, $S$ an assignment of a list of symbols to every stack, and $p, p', t, t'$ lists of
symbols. Setting stack $a$ to $p$, then $b$ to $t$, then $a$ to $p'$, then $b$ to $t'$ gives the
same assignment as setting $a$ to $p'$ and then $b$ to $t'$. -/
theorem update_update_update_update {a b : K} (hab : a ≠ b) (S : ∀ _ : K, List Sym)
    (p p' t t' : List Sym) :
    update (update (update (update S a p) b t) a p') b t' = update (update S a p') b t' := by
  rw [update_comm hab.symm, update_idem, update_idem]

/-- **Moving one color code from the color stack.** Let $f$ assign a label to each pair of
bits, and suppose the color stack $P$ of stacks $S$ holds, from the top, the bit symbols $c_1$
and $c_2$ followed by a rest $r$. Then executing the color-moving block with continuation $f$,
from any internal value and the stacks $S$, ends at label $f(c_1, c_2)$ with internal value
$c_2$ and with the stacks $S$ changed only in that $P$ becomes $r$ and the scratch stack $T$
gets $c_1$ and then $c_2$ pushed on top (so $c_2$ is on top). -/
theorem stepAux_mvP_cons (f : Bool → Bool → Lab) (c : Bool × Bool) (rest : List Sym) (s : Bool)
    (S : ∀ _ : K, List Sym) (hP : S .P = .bit c.1 :: .bit c.2 :: rest) :
    TM2.stepAux (mvP f) s S =
      ⟨some (f c.1 c.2), c.2, update (update S .P rest) .T (.bit c.2 :: .bit c.1 :: S .T)⟩ := by
  obtain ⟨a, b⟩ := c
  cases a <;> cases b <;>
    simp [mvP, TM2.stepAux, hP, bitOf, Sym.bit?, update_update_update_update]

/-- **The color-moving block rejects on an empty color stack.** If the color stack $P$ of
stacks $S$ is empty, then for every continuation $f$ (a label for each pair of bits), executing
the color-moving block with continuation $f$ from any internal value and the stacks $S$ ends at
the rejecting label with internal value true and the stacks $S$ unchanged. -/
theorem stepAux_mvP_nil (f : Bool → Bool → Lab) (s : Bool) (S : ∀ _ : K, List Sym)
    (hP : S .P = []) : TM2.stepAux (mvP f) s S = ⟨some .no, true, S⟩ := by
  simp [mvP, TM2.stepAux, hP]

/-- **Walk-on step with the counter exhausted.** Let $k$ be a stack, $\ell$ a label and $a, b$
bits. If stack $k$ of stacks $S$ is empty, then executing the walk-on block for counter $k$,
label $\ell$ and held color $(a, b)$, from any internal value and the stacks $S$, has the same
outcome as executing, from internal value false and the stacks $S$, the color-moving block
that continues to the rejecting label if the color it moves is $(a, b)$ and to the label that
restores the color stack otherwise. -/
theorem stepAux_walk1S_nil (k : K) (self : Lab) (a b s : Bool) (St : ∀ _ : K, List Sym)
    (hk : St k = []) : TM2.stepAux (walk1S k self a b) s St =
      TM2.stepAux (mvP fun a' b' => if a' = a ∧ b' = b then .no else .back) false St := by
  have : update St k [] = St := by rw [← hk, update_eq_self]
  simp [walk1S, TM2.stepAux, hk, this]

/-- **Walk-on step with a unit on the counter.** Write $1^j$ for the stack of $j$ copies of the
bit symbol for true. Let $k$ be a stack, $\ell$ a label and $a, b$ bits. If stack $k$ of
stacks $S$ holds $1^{j+1}$, then executing the walk-on block for counter $k$, label $\ell$ and
held color $(a, b)$, from any internal value and the stacks $S$, has the same outcome as
executing, from internal value true and the stacks $S$ with stack $k$ replaced by $1^j$, the
color-moving block that continues to $\ell$ whatever color it moves. -/
theorem stepAux_walk1S_cons (k : K) (self : Lab) (a b s : Bool) (St : ∀ _ : K, List Sym)
    (j : ℕ) (hk : St k = cnt (Sym.bit true) (j + 1)) : TM2.stepAux (walk1S k self a b) s St =
      TM2.stepAux (mvP fun _ _ => self) true (update St k (cnt (Sym.bit true) j)) := by
  simp [walk1S, TM2.stepAux, hk, cnt_succ]

/-- **The walk towards the farther endpoint decides the edge.** Let $k$ be a stack of the 3-COLOR
verifier other than the color stack $P$ and the scratch stack $T$, $(a, b)$ a pair of bits, and
$\ell$ a label whose statement is the step of the walk towards the farther endpoint on the
counter $k$, holding the color $(a, b)$ and continuing at $\ell$. Let $j$ be a natural number,
$\mathit{pre}$ and $\mathit{post}$ lists of color codes, $s$ a bit and $S$ an assignment of a list
of symbols to every stack. Suppose that $S$ holds $j$ unit symbols on $k$, the bits of
$\mathit{post}$ on $P$ (each code $(a', b')$ contributing $a'$ then $b'$, the first code on top),
and the bits of $\mathit{pre}$, flattened the same way, in reverse order on $T$. Started at $\ell$
with internal state $s$ and stacks $S$, the verifier reaches within at most $j + 1$ steps, with
some internal state and stacks $S'$, the label $\mathsf{back}$ if $j$ is less than the length of
$\mathit{post}$ and the code at position $j$ of $\mathit{post}$ differs from $(a, b)$, and the
label $\mathsf{no}$ otherwise. If $j$ is less than the length of $\mathit{post}$, the stacks $S'$
hold the bits of $\mathit{post}$ after its first $j + 1$ codes on $P$, the bits of $\mathit{pre}$
followed by those of the first $j + 1$ codes of $\mathit{post}$, flattened and in reverse order,
on $T$, nothing on $k$, and agree with $S$ on every other stack. -/
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

/-- **Joint-walk step with both counters nonempty.** Write $1^j$ for the stack of $j$ copies of
the bit symbol for true. If the endpoint counters of stacks $S$ hold $U = 1^{u+1}$ and
$V = 1^{v+1}$, then executing the joint-walk block from any internal value and the stacks $S$
has the same outcome as executing, from internal value true and the stacks $S$ with $U$
replaced by $1^u$ and $V$ by $1^v$, the color-moving block that continues to the joint-walk
label whatever color it moves. -/
theorem stepAux_walkS_cons_cons (s : Bool) (St : ∀ _ : K, List Sym) (u v : ℕ)
    (hU : St .U = cnt (Sym.bit true) (u + 1)) (hV : St .V = cnt (Sym.bit true) (v + 1)) :
    TM2.stepAux walkS s St = TM2.stepAux (mvP fun _ _ => .walk) true
      (update (update St .U (cnt (Sym.bit true) u)) .V (cnt (Sym.bit true) v)) := by
  simp [walkS, TM2.stepAux, hU, hV, cnt_succ]

/-- **Joint-walk step when the second endpoint counter runs out first.** Write $1^j$ for the
stack of $j$ copies of the bit symbol for true. If the endpoint counters of stacks $S$ hold
$U = 1^{u+1}$ and $V$ empty, then executing the joint-walk block from any internal value and
the stacks $S$ has the same outcome as executing, from internal value false and the stacks $S$
with $U$ replaced by $1^u$, the color-moving block that, after moving a color $(a, b)$,
continues to the label that walks on along $U$ holding $(a, b)$. -/
theorem stepAux_walkS_cons_nil (s : Bool) (St : ∀ _ : K, List Sym) (u : ℕ)
    (hU : St .U = cnt (Sym.bit true) (u + 1)) (hV : St .V = []) :
    TM2.stepAux walkS s St = TM2.stepAux (mvP .walkU) false
      (update St .U (cnt (Sym.bit true) u)) := by
  have : update (update St .U (cnt (Sym.bit true) u)) .V [] =
      update St .U (cnt (Sym.bit true) u) := by
    rw [← hV, ← update_of_ne (show K.V ≠ K.U by decide) (cnt (Sym.bit true) u) St, update_eq_self]
  simp [walkS, TM2.stepAux, hU, hV, cnt_succ, this]

/-- **Joint-walk step when the first endpoint counter runs out first.** Write $1^j$ for the
stack of $j$ copies of the bit symbol for true. If the endpoint counters of stacks $S$ hold
$U$ empty and $V = 1^{v+1}$, then executing the joint-walk block from any internal value and
the stacks $S$ has the same outcome as executing, from internal value true and the stacks $S$
with $V$ replaced by $1^v$, the color-moving block that, after moving a color $(a, b)$,
continues to the label that walks on along $V$ holding $(a, b)$. -/
theorem stepAux_walkS_nil_cons (s : Bool) (St : ∀ _ : K, List Sym) (v : ℕ)
    (hU : St .U = []) (hV : St .V = cnt (Sym.bit true) (v + 1)) :
    TM2.stepAux walkS s St = TM2.stepAux (mvP .walkV) true
      (update St .V (cnt (Sym.bit true) v)) := by
  have : update St .U [] = St := by rw [← hU, update_eq_self]
  simp [walkS, TM2.stepAux, hU, hV, cnt_succ, this]

/-- **Joint-walk step with both counters exhausted.** If the endpoint counters $U$ and $V$ of
stacks $S$ are both empty, then executing the joint-walk block from any internal value and the
stacks $S$ has the same outcome as executing, from internal value false and the same stacks
$S$, the color-moving block that continues to the label restoring the color stack whatever
color it moves.

This is the case of a loop edge. -/
theorem stepAux_walkS_nil_nil (s : Bool) (St : ∀ _ : K, List Sym) (hU : St .U = [])
    (hV : St .V = []) : TM2.stepAux walkS s St = TM2.stepAux (mvP fun _ _ => .back) false St := by
  have h₁ : update St .U [] = St := by rw [← hU, update_eq_self]
  have h₂ : update St .V [] = St := by rw [← hV, update_eq_self]
  simp [walkS, TM2.stepAux, hU, hV, h₁, h₂]

/-- **Edge verdict for an edge starting at vertex 0.** For a color code $c$, a list $cs$ of color
codes and $v \in \mathbb{N}$, the edge $(0, v + 1)$ passes the edge verdict with vertex colors $c$
followed by $cs$ iff $v$ is less than the length of $cs$ and entry $v$ of $cs$ differs from $c$. -/
theorem edgeOk_zero_succ (c : Bool × Bool) (cs : List (Bool × Bool)) (v : ℕ) :
    edgeOk (c :: cs) 0 (v + 1) = true ↔ v < cs.length ∧ cs.getD v (false, false) ≠ (c.1, c.2) := by
  simp [edgeOk, ne_comm]

/-- **Edge verdict for an edge ending at vertex 0.** For a color code $c$, a list $cs$ of color
codes and $u \in \mathbb{N}$, the edge $(u + 1, 0)$ passes the edge verdict with vertex colors $c$
followed by $cs$ iff $u$ is less than the length of $cs$ and entry $u$ of $cs$ differs from $c$. -/
theorem edgeOk_succ_zero (c : Bool × Bool) (cs : List (Bool × Bool)) (u : ℕ) :
    edgeOk (c :: cs) (u + 1) 0 = true ↔ u < cs.length ∧ cs.getD u (false, false) ≠ (c.1, c.2) := by
  simp [edgeOk]

/-- **The joint walk of the 3-COLOR verifier decides one edge.** Let $u, v$ be natural numbers,
$\mathit{pre}$ and $\mathit{post}$ lists of color codes (pairs of bits), $s$ a bit and $S$ an
assignment of a list of symbols to every stack. Suppose that $S$ holds $u$ unit symbols on the
counter $U$ and $v$ on the counter $V$, the bits of $\mathit{post}$ on the color stack $P$ (each
code $(a, b)$ contributing $a$ then $b$, the first code on top), and the bits of $\mathit{pre}$,
flattened the same way, in reverse order on the scratch stack $T$. Started at the label
$\mathsf{walk}$ with internal state $s$ and stacks $S$, the verifier reaches within at most
$\max(u, v) + 1$ steps, with some internal state and stacks $S'$, the label $\mathsf{back}$ if the
edge $(u, v)$ passes against the colors $\mathit{post}$ and the label $\mathsf{no}$ otherwise. The
edge passes when $u$ and $v$ are both less than the length of $\mathit{post}$ and either $u = v$
or the codes at positions $u$ and $v$ of $\mathit{post}$ differ. If it passes then, with
$m = \max(u, v) + 1$, the stacks $S'$ hold the bits of $\mathit{post}$ after its first $m$ codes
on $P$, the bits of $\mathit{pre}$ followed by those of the first $m$ codes of $\mathit{post}$,
flattened and in reverse order, on $T$, nothing on $U$ and $V$, and agree with $S$ on every other
stack. -/
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

/-- **The unary reader on a terminated number.** Let $c \ne X$ be a stack and $s$, $t$ labels
such that the verifier runs, at $s$, the unary reader from $X$ onto the counter $c$ that loops at
$s$ and exits to $t$. Let $k, j$ be natural numbers and $r$ a list of bits. If $X$ holds $k$ ones,
then a zero, then $r$, and $c$ holds exactly $j$ units, then from label $s$, in any internal
state, the verifier reaches label $t$ in exactly $k + 1$ steps, with $X$ holding $r$, $c$ holding
exactly $k + j$ units, and every other stack as at the start. -/
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

/-- **The unary reader rejects an unterminated number.** Let $c \ne X$ be a stack and $s$, $t$
labels such that the verifier runs, at $s$, the unary reader from $X$ onto the counter $c$ that
loops at $s$ and exits to $t$. If $X$ holds a bit list $l$ on which reading a unary number
fails, that is, $l$ consists of ones only, then from label $s$, in any internal state and with
any other stacks, the verifier reaches the rejecting label within at most $|l| + 1$ steps. -/
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

/-- **Run of the load phase of the 3-COLOR verifier.** Let $n$ be a natural number and $w$, $a$
lists of bits. Start the verifier at its load label, in any internal state, with stacks in which
the counter $N$ holds exactly $n$ units, the witness stack $W$ holds $w$ and the scratch stack $T$
holds $a$. Then within at most $n + 1$ steps the verifier reaches the label that moves the codes
onto the color stack $P$ if $w$ has at least $2n$ bits and the color codes of the vertices
$0, \dots, n - 1$ (vertex $i$ has the code $w_{2i} w_{2i+1}$) are all valid, that is, none is
$11$; otherwise it reaches the rejecting label. In the first case $T$ then holds the first $2n$
bits of $w$ in reverse order on top of $a$, and every stack other than $N$, $W$ and $T$ is as at
the start. -/
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

/-- **Edge-loop verdict after one parsed edge.** Let $cs$ be a list of color codes and $r$ a bit
list. If $r$ begins with $u$ in unary ($u$ ones, then a zero) followed by the rest $r_1$, and
$r_1$ begins with $v$ in unary followed by the rest $r_2$, then the edge-loop verdict on $r$ with
vertex colors $cs$ holds iff the edge verdict for $(u, v)$ holds and the edge-loop verdict on
$r_2$ holds. -/
theorem edgesOk_of_some_some (cs : List (Bool × Bool)) {r r₁ r₂ : List Bool} {u v : ℕ}
    (h₁ : readUnaryLength r = some (u, r₁)) (h₂ : readUnaryLength r₁ = some (v, r₂)) :
    edgesOk cs r = (edgeOk cs u v && edgesOk cs r₂) := by
  unfold edgesOk
  rw [decodeEs_of_some_some h₁ h₂]
  cases decodeEs r₂ <;> simp

/-- **Restoring the color stack in the 3-COLOR verifier.** Let $\mathit{pre}$ and $\mathit{post}$
be lists of pairs of bits, let $s$ be a Boolean state, and let $S$ assign to each stack a list of
symbols. Suppose that in $S$ the stack $P$ holds the bits of the flattening of $\mathit{post}$
and the stack $T$ holds the bits of the flattening of $\mathit{pre}$ in reverse order (as bit
symbols, top first). Then the verifier program runs in exactly $2 |\mathit{pre}| + 1$ steps from
the label back with state $s$ and stacks $S$ to the label edge with some state $s'$ and stacks
$S'$ such that $T$ is empty in $S'$, $P$ holds the bits of the flattening of $\mathit{pre}$
followed by $\mathit{post}$, and every stack other than $T$ and $P$ is unchanged. -/
theorem back_run (pre post : List (Bool × Bool)) (s : Bool) (St : ∀ _ : K, List Sym)
    (hP : St .P = (flat post).map Sym.bit) (hT : St .T = (flat pre).reverse.map Sym.bit) :
    ∃ s' S', Run prog (2 * pre.length + 1) ⟨some .back, s, St⟩ ⟨some .edge, s', S'⟩ ∧
      S' .T = [] ∧ S' .P = (flat (pre ++ post)).map Sym.bit ∧
      ∀ q, q ≠ .T → q ≠ .P → S' q = St q := by
  obtain ⟨s', S', h, hT', hP', hF⟩ := moveB_run (M := prog) (self := .back) (next := .edge) rfl
    (show K.T ≠ K.P by decide) (flat pre).reverse ((flat pre).reverse.map Sym.bit) [] s St
    (by simp [hT]) (by simp [IsBitBlock, Sym.bit?, Function.comp_def]) (by simp [EndsBitBlock])
  exact ⟨s', S', by simpa using h, hT', by simp [hP', hP, flat_append, List.map_reverse], hF⟩

/-- **Correctness and running time of the edge loop.** Let $cs$ be a list of color codes (pairs
of bits) and $r$ a list of bits, and encode an edge $(u, v)$ of natural numbers as $u$ ones, a
zero, $v$ ones and a zero. Call $r$ good for $cs$ when $r$ is a concatenation of encoded edges
such that, for every edge $(u, v)$ among them, $u$ and $v$ are below the length of $cs$ and, if
$u \ne v$, entries $u$ and $v$ of $cs$ (counting from $0$) differ. Suppose the 3-COLOR verifier
is at its edge label, in any internal state, with the input stack $X$ holding the bits of $r$
(first bit on top), the color stack $P$ holding the bits of the flattening of $cs$, the stacks
$T$, $U$ and $V$ empty, and the other stacks arbitrary. Then in at most $4|r| + 1$ steps it
reaches, in some internal state and with some stack contents, the accepting label if $r$ is good
for $cs$, and the rejecting label otherwise. -/
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

/-- **Correctness and time bound of the 3-coloring verifier machine.** Let $x$ and $w$ be
bit strings. Start the verifier machine at its start label, with any internal value, with $x$
written as bit symbols on the input stack $X$, $w$ written as bit symbols on the witness stack
$W$, and all other stacks empty. Then within at most $8(|x| + |w| + 1)^3$ steps it reaches the
accepting label if the 3-coloring check accepts $(x, w)$, and the rejecting label otherwise.

The machine in fact runs in linearly many steps; only the cubic bound is stated here. -/
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
