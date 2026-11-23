/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.DenseToBinary

/-!
# Correctness of Karp's reduction SAT ≤ 3-COLOR

`satDec_eq_col3Dec_reduceCol`: the reduction `reduceCol` of
`CSLibExt.Computability.Complexity.Karp.Color` preserves membership (Karp 1972, through the
OR-gadget construction of Garey, Johnson and Stockmeyer, *Some simplified NP-complete graph
problems*, Theoret. Comput. Sci. 1 (1976)). The core is `cnfSat_iff_colorable`:

* (→) From an assignment `v` satisfying `φ`, color the palette `T, F, B` as `0, 1, 2`, the
  vertex `L` of an occurrence `T` iff its literal is true under `v` (and `M` with the other of
  `T, F`), and each OR gadget so that its output is the or of its inputs (`or_gadget_colors`).
  The coloring is built along the construction (`colColored_colOcc`, `colColored_colOr`, ...);
  every clause output comes out `T`, as its edges to `F` and `B` demand.
* (←) Rename the colors of a 3-coloring so that the palette is `0, 1, 2`. A clause output is
  `T`, so by `or_gadget_sound` some literal vertex of the clause is `T` (`sound_colClause`). The
  consistency edges make all occurrences of one variable agree, so reading each variable off any
  of its occurrences gives a satisfying assignment. An empty clause has a vertex adjacent to the
  whole palette, so neither side holds.

The construction's invariants are `ColGood` (vertices below `next`, no loops, the palette
triangle, the triangle `L, M, B` of each occurrence, consistency edges between all pairs of
occurrences) and `ColGrows` (edges and occurrences only accumulate).
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL

/-! ### The instance codec -/

/-- A unary number ended by `false` determines the number and the rest. -/
private theorem replicate_false_inj {a b : ℕ} {r r' : List Bool}
    (h : List.replicate a true ++ false :: r = List.replicate b true ++ false :: r') :
    a = b ∧ r = r' := by
  simpa using congrArg readUnaryLength h

theorem encodeE_inj {n n' : ℕ} {es es' : List (ℕ × ℕ)} (h : encodeE n es = encodeE n' es') :
    n = n' ∧ es = es' := by
  obtain ⟨rfl, hr⟩ := replicate_false_inj h
  clear h
  refine ⟨rfl, ?_⟩
  induction es generalizing es' with
  | nil => cases es' <;> simp_all
  | cons e es ih =>
    cases es' with
    | nil => simp at hr
    | cons e' es' =>
      simp only [List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append] at hr
      obtain ⟨h1, hr⟩ := replicate_false_inj hr
      obtain ⟨h2, hr⟩ := replicate_false_inj hr
      rw [ih hr, Prod.ext h1 h2]

theorem col3Dec_encodeE_eq_true {n : ℕ} {es : List (ℕ × ℕ)} :
    col3Dec (encodeE n es) = true ↔
      (∀ e ∈ es, e.1 < n ∧ e.2 < n) ∧ (edgeGraph n es).Colorable 3 := by
  simp only [col3Dec, decide_eq_true_eq]
  constructor
  · rintro ⟨n', es', h, hb, hc⟩
    obtain ⟨rfl, rfl⟩ := encodeE_inj h
    exact ⟨hb, hc⟩
  · rintro ⟨hb, hc⟩
    exact ⟨n, es, rfl, hb, hc⟩

@[simp] theorem edgeGraph_reverse (n : ℕ) (es : List (ℕ × ℕ)) :
    edgeGraph n es.reverse = edgeGraph n es := by
  simp [edgeGraph]

/-- **The complete graph on four vertices is not 3-colorable.** The graph on the vertices
$0, 1, 2, 3$ with an edge between every two distinct vertices has no proper coloring with
$3$ colors. -/
theorem not_colorable_noCol :
    ¬(edgeGraph 4 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]).Colorable 3 := by
  rintro ⟨C⟩
  obtain ⟨i, j, hij, hc⟩ := Fintype.exists_ne_map_eq_of_card_lt C (by simp)
  refine C.valid ?_ hc
  rw [edgeGraph, SimpleGraph.fromRel_adj]
  refine ⟨hij, ?_⟩
  fin_cases i <;> fin_cases j <;> simp_all

theorem col3Dec_noCol : col3Dec noCol = false := by
  rw [Bool.eq_false_iff, ne_eq, noCol, col3Dec_encodeE_eq_true]
  exact fun h => not_colorable_noCol h.2

/-! ### Colorings as functions on `ℕ` -/

/-- **Proper 3-colorings of an edge list.** A map $c : \mathbb{N} \to \{0, 1, 2\}$ properly colors
a list $E$ of pairs of natural numbers when $c(a) \ne c(b)$ for every pair $(a, b)$ in $E$. -/
def ColProper (c : ℕ → Fin 3) (es : List (ℕ × ℕ)) : Prop :=
  ∀ e ∈ es, c e.1 ≠ c e.2

theorem ColProper.mono {c : ℕ → Fin 3} {es es' : List (ℕ × ℕ)} (h : ColProper c es')
    (hs : es ⊆ es') : ColProper c es :=
  fun e he => h e (hs he)

/-- **3-colorability through colorings of the natural numbers.** Let $n$ be a natural number and
$E$ a list of pairs $(a, b)$ of natural numbers with $a < n$, $b < n$ and $a \ne b$. The graph on
$\{0, \dots, n - 1\}$ with edge list $E$ is 3-colorable if and only if some map
$c : \mathbb{N} \to \{0, 1, 2\}$ satisfies $c(a) \ne c(b)$ for every pair $(a, b)$ in $E$. -/
theorem colorable_iff_exists_colProper {n : ℕ} {es : List (ℕ × ℕ)}
    (hb : ∀ e ∈ es, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) :
    (edgeGraph n es).Colorable 3 ↔ ∃ c, ColProper c es := by
  constructor
  · rintro ⟨C⟩
    refine ⟨fun k => if h : k < n then C ⟨k, h⟩ else 0, fun e he => ?_⟩
    obtain ⟨h1, h2, hne⟩ := hb e he
    simp only [h1, h2, dite_true]
    exact C.valid ((SimpleGraph.fromRel_adj _ _ _).2
      ⟨fun h => hne (congrArg Fin.val h), Or.inl he⟩)
  · rintro ⟨c, hc⟩
    refine ⟨SimpleGraph.Coloring.mk (fun i => c i) fun {i j} h => ?_⟩
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · exact hc _ h
    · exact (hc _ h).symm

/-! ### Three colors -/

/-- **Coloring an OR gadget.** Read the colors $0, 1, 2$ as $T$, $F$ and $B$. For all
colors $c_a, c_o \in \{0, 1, 2\}$ with $c_a \ne 2$ and $c_o \ne 2$, there are colors
$c_u, c_v, c_w \in \{0, 1, 2\}$ with $c_a \ne c_u$, $c_o \ne c_v$, $c_u \ne c_v$,
$c_u \ne c_w$, $c_v \ne c_w$ and $c_w \ne 2$, such that $c_w = 0$ if and only if
$c_a = 0$ or $c_o = 0$.

These are the conditions for a proper coloring of an OR gadget with inputs $a, o$, fresh
vertices $u, v, w$ and edges $au$, $ov$, $uv$, $uw$, $vw$, $wB$, where $B$ has color $2$:
if both inputs are colored $T$ or $F$, the gadget can be colored so that its output $w$ is
$T$ or $F$, and $T$ exactly when some input is $T$. -/
theorem or_gadget_colors : ∀ ca co : Fin 3, ca ≠ 2 → co ≠ 2 → ∃ cu cv cw : Fin 3,
    ca ≠ cu ∧ co ≠ cv ∧ cu ≠ cv ∧ cu ≠ cw ∧ cv ≠ cw ∧ cw ≠ 2 ∧
      (cw = 0 ↔ ca = 0 ∨ co = 0) := by
  decide

/-- **Soundness of the OR gadget.** Read the colors $0, 1, 2$ as $T$, $F$ and $B$. If
colors $c_a, c_o, c_u, c_v, c_w \in \{0, 1, 2\}$ satisfy $c_a \ne 2$, $c_o \ne 2$,
$c_a \ne c_u$, $c_o \ne c_v$, $c_u \ne c_v$, $c_u \ne c_w$, $c_v \ne c_w$ and $c_w = 0$,
then $c_a = 0$ or $c_o = 0$.

That is, in a proper coloring of an OR gadget with inputs $a, o$, fresh vertices $u, v, w$
and edges $au$, $ov$, $uv$, $uw$, $vw$, if both inputs are colored $T$ or $F$ and the
output $w$ is $T$, then some input is $T$. -/
theorem or_gadget_sound : ∀ ca co cu cv cw : Fin 3, ca ≠ 2 → co ≠ 2 → ca ≠ cu → co ≠ cv →
    cu ≠ cv → cu ≠ cw → cv ≠ cw → cw = 0 → ca = 0 ∨ co = 0 := by
  decide

/-- Renaming colors so that `a, b` become `0, 1` (and the rest `2`) keeps distinct colors
distinct. -/
private theorem fin3_rename : ∀ x y a b : Fin 3, a ≠ b → x ≠ y →
    (if x = a then 0 else if x = b then 1 else 2 : Fin 3) ≠
      (if y = a then 0 else if y = b then 1 else 2 : Fin 3) := by
  decide

private theorem tf_ne : ∀ x b : Bool,
    (if x = b then (0 : Fin 3) else 1) ≠ (if x = b then 1 else 0) := by
  decide

private theorem tf_ne_two : ∀ x b : Bool, (if x = b then (0 : Fin 3) else 1) ≠ 2 := by
  decide

private theorem ft_ne_two : ∀ x b : Bool, (if x = b then (1 : Fin 3) else 0) ≠ 2 := by
  decide

private theorem tf_ne_of_ne : ∀ x b b' : Bool, b' ≠ b →
    (if x = b' then (0 : Fin 3) else 1) ≠ (if x = b then 0 else 1) := by
  decide

private theorem ft_ne_of_ne : ∀ x b b' : Bool, b' ≠ b →
    (if x = b' then (1 : Fin 3) else 0) ≠ (if x = b then 1 else 0) := by
  decide

/-! ### Unfolding the construction -/

/-- **Adding a literal occurrence takes two new vertices.** For a literal $l$ and a state $s$ of
the SAT-to-3-COLOR construction whose next free vertex is $n$, the state obtained by adding the
occurrence $l$ to $s$ has next free vertex $n + 2$. -/
@[simp] theorem colOcc_next (l : ℕ × Bool) (s : ColSt) : (colOcc l s).1.next = s.next + 2 :=
  rfl

@[simp] theorem colOcc_prev (l : ℕ × Bool) (s : ColSt) :
    (colOcc l s).1.prev = (l.1, l.2, s.next, s.next + 1) :: s.prev :=
  rfl

@[simp] theorem colOcc_em (l : ℕ × Bool) (s : ColSt) :
    (colOcc l s).1.em = s.em ++ [(s.next, s.next + 1), (s.next, 2), (s.next + 1, 2)] ++
      s.prev.flatMap (consEdges l s.next (s.next + 1)) :=
  rfl

@[simp] theorem colOcc_snd (l : ℕ × Bool) (s : ColSt) : (colOcc l s).2 = s.next :=
  rfl

@[simp] theorem colOr_next (a o : ℕ) (s : ColSt) : (colOr a o s).1.next = s.next + 3 :=
  rfl

@[simp] theorem colOr_prev (a o : ℕ) (s : ColSt) : (colOr a o s).1.prev = s.prev :=
  rfl

@[simp] theorem colOr_em (a o : ℕ) (s : ColSt) :
    (colOr a o s).1.em = s.em ++ [(a, s.next), (o, s.next + 1), (s.next, s.next + 1),
      (s.next, s.next + 2), (s.next + 1, s.next + 2), (s.next + 2, 2)] :=
  rfl

@[simp] theorem colOr_snd (a o : ℕ) (s : ColSt) : (colOr a o s).2 = s.next + 2 :=
  rfl

theorem colLits_nil (o : ℕ) (s : ColSt) :
    colLits [] o s = ⟨s.next, s.prev, s.em ++ [(o, 1), (o, 2)]⟩ :=
  rfl

theorem colLits_cons (l : ℕ × Bool) (ls : List (ℕ × Bool)) (o : ℕ) (s : ColSt) :
    colLits (l :: ls) o s =
      colLits ls (colOr (colOcc l s).2 o (colOcc l s).1).2
        (colOr (colOcc l s).2 o (colOcc l s).1).1 :=
  rfl

/-! ### Growth -/

/-- **Growth of construction states.** A construction state $s'$ extends a construction state $s$
when the next free vertex of $s'$ is at least that of $s$, every edge emitted in $s$ is emitted in
$s'$, and every occurrence recorded in $s$ is recorded in $s'$. -/
structure ColGrows (s s' : ColSt) : Prop where
  /-- `next` does not decrease. -/
  next : s.next ≤ s'.next
  /-- Edges accumulate. -/
  em : s.em ⊆ s'.em
  /-- Occurrences accumulate. -/
  prev : s.prev ⊆ s'.prev

theorem ColGrows.refl (s : ColSt) : ColGrows s s :=
  ⟨le_rfl, List.Subset.refl _, List.Subset.refl _⟩

theorem ColGrows.trans {s₁ s₂ s₃ : ColSt} (h₁ : ColGrows s₁ s₂) (h₂ : ColGrows s₂ s₃) :
    ColGrows s₁ s₃ :=
  ⟨h₁.next.trans h₂.next, List.Subset.trans h₁.em h₂.em, List.Subset.trans h₁.prev h₂.prev⟩

/-- **Extending a state makes it grow.** Let $s$ be a construction state with next free vertex
$m$, let $n \ge m$, and let $E$ be a list of pairs of natural numbers. Then the state with next
free vertex $n$, the same recorded occurrences as $s$, and emitted edges those of $s$ followed by
$E$ extends $s$: its next free vertex is at least that of $s$, and its emitted edges and recorded
occurrences include those of $s$. -/
theorem colGrows_extend (s : ColSt) {n : ℕ} (es : List (ℕ × ℕ)) (hn : s.next ≤ n) :
    ColGrows s ⟨n, s.prev, s.em ++ es⟩ :=
  ⟨hn, List.subset_append_left _ _, List.Subset.refl _⟩

theorem colGrows_colOcc (l : ℕ × Bool) (s : ColSt) : ColGrows s (colOcc l s).1 :=
  ⟨by simp, fun e he => by simp [he], fun q hq => by simp [hq]⟩

theorem colGrows_colOr (a o : ℕ) (s : ColSt) : ColGrows s (colOr a o s).1 :=
  colGrows_extend s _ (by omega)

theorem colGrows_colLits :
    ∀ (ls : List (ℕ × Bool)) (o : ℕ) (s : ColSt), ColGrows s (colLits ls o s)
  | [], o, s => colGrows_extend s _ le_rfl
  | l :: ls, o, s => by
    rw [colLits_cons]
    exact ((colGrows_colOcc l s).trans (colGrows_colOr _ _ _)).trans (colGrows_colLits _ _ _)

theorem colGrows_colClause (C : CNFClause) (s : ColSt) : ColGrows s (colClause C s) := by
  unfold colClause
  split
  · exact colGrows_extend s _ (by omega)
  · exact (colGrows_colOcc _ _).trans (colGrows_colLits _ _ _)

theorem colGrows_foldl :
    ∀ (cs : CNF) (s : ColSt), ColGrows s (cs.foldl (fun s C => colClause C s) s)
  | [], s => ColGrows.refl s
  | C :: cs, s => (colGrows_colClause C s).trans (colGrows_foldl cs _)

/-! ### Well-formedness -/

/-- **Well-formed construction states.** A construction state $s$ with next free vertex $n$ is
well formed when $3 \le n$; every emitted edge $(a, b)$ has $a < n$, $b < n$ and $a \ne b$; the
literal vertex and the negation vertex of every recorded occurrence are smaller than $n$; the
pairs $(0, 1)$, $(0, 2)$ and $(1, 2)$ are emitted edges (the palette triangle); for every
recorded occurrence with literal vertex $L$ and negation vertex $M$, the pairs $(L, M)$, $(L, 2)$
and $(M, 2)$ are emitted edges; and whenever an occurrence with variable $x$, polarity $b$,
literal vertex $L$ and negation vertex $M$ comes before an occurrence with the same variable $x$,
polarity $b'$, literal vertex $L'$ and negation vertex $M'$ in the list of recorded occurrences
(which lists the latest first), the pairs $(L', M)$ and $(M', L)$ are emitted edges if $b' = b$,
and the pairs $(L', L)$ and $(M', M)$ are emitted edges if $b' \ne b$. -/
structure ColGood (s : ColSt) : Prop where
  /-- The palette is allocated. -/
  three_le : 3 ≤ s.next
  /-- Edges join two distinct allocated vertices. -/
  em_lt : ∀ e ∈ s.em, e.1 < s.next ∧ e.2 < s.next ∧ e.1 ≠ e.2
  /-- Occurrence vertices are allocated. -/
  prev_lt : ∀ q ∈ s.prev, q.2.2.1 < s.next ∧ q.2.2.2 < s.next
  /-- The palette triangle. -/
  palette : (0, 1) ∈ s.em ∧ (0, 2) ∈ s.em ∧ (1, 2) ∈ s.em
  /-- The triangle `L, M, B` of each occurrence. -/
  tri : ∀ q ∈ s.prev, (q.2.2.1, q.2.2.2) ∈ s.em ∧ (q.2.2.1, 2) ∈ s.em ∧ (q.2.2.2, 2) ∈ s.em
  /-- Consistency edges between each occurrence and every earlier one. -/
  cons : s.prev.Pairwise fun q q' => ∀ e ∈ consEdges (q.1, q.2.1) q.2.2.1 q.2.2.2 q', e ∈ s.em

theorem colGood_init : ColGood ⟨3, [], [(0, 1), (0, 2), (1, 2)]⟩ where
  three_le := le_rfl
  em_lt := by decide
  prev_lt := by simp
  palette := by simp
  tri := by simp
  cons := List.Pairwise.nil

/-- **Extending a well-formed state keeps it well formed.** Let $s$ be a well-formed
construction state with next free vertex $m$, let $n \ge m$, and let $E$ be a list of pairs
$(a, b)$ of natural numbers with $a < n$, $b < n$ and $a \ne b$. Then the state with next free
vertex $n$, the same recorded occurrences as $s$, and emitted edges those of $s$ followed by $E$
is well formed. -/
theorem ColGood.extend {s : ColSt} (h : ColGood s) {n : ℕ} (es : List (ℕ × ℕ))
    (hn : s.next ≤ n) (hes : ∀ e ∈ es, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) :
    ColGood ⟨n, s.prev, s.em ++ es⟩ := by
  have g : s.em ⊆ s.em ++ es := List.subset_append_left _ _
  refine ⟨h.three_le.trans hn, fun e he => ?_, fun q hq => ?_,
    ⟨g h.palette.1, g h.palette.2.1, g h.palette.2.2⟩, fun q hq => ?_,
    h.cons.imp fun hq e he => g (hq e he)⟩
  · dsimp only
    rcases List.mem_append.1 he with he | he
    · have := h.em_lt e he
      omega
    · exact hes e he
  · dsimp only
    have := h.prev_lt q hq
    omega
  · obtain ⟨t1, t2, t3⟩ := h.tri q hq
    exact ⟨g t1, g t2, g t3⟩

theorem colGood_colOcc {l : ℕ × Bool} {s : ColSt} (h : ColGood s) : ColGood (colOcc l s).1 := by
  have h3 := h.three_le
  have g := colGrows_colOcc l s
  refine ⟨by simp; omega, fun e he => ?_, fun q hq => ?_,
    ⟨g.em h.palette.1, g.em h.palette.2.1, g.em h.palette.2.2⟩, fun q hq => ?_, ?_⟩
  · simp only [colOcc_em, colOcc_next, List.mem_append, List.mem_cons, List.mem_flatMap,
      List.not_mem_nil, or_false] at he ⊢
    rcases he with (he | rfl | rfl | rfl) | ⟨q, hq, he⟩
    · have := h.em_lt e he
      omega
    · omega
    · omega
    · omega
    · have := h.prev_lt q hq
      unfold consEdges at he
      split_ifs at he <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at he <;>
        rcases he with rfl | rfl <;> omega
  · simp only [colOcc_prev, colOcc_next, List.mem_cons] at hq ⊢
    rcases hq with rfl | hq
    · dsimp only
      omega
    · have := h.prev_lt q hq
      omega
  · simp only [colOcc_prev, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp
    · obtain ⟨t1, t2, t3⟩ := h.tri q hq
      exact ⟨g.em t1, g.em t2, g.em t3⟩
  · simp only [colOcc_prev, List.pairwise_cons]
    refine ⟨fun q hq e he => ?_, h.cons.imp fun hq e he => g.em (hq e he)⟩
    simp only [colOcc_em, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨q, hq, he⟩

theorem colGood_colOr {a o : ℕ} {s : ColSt} (h : ColGood s) (ha : a < s.next)
    (ho : o < s.next) : ColGood (colOr a o s).1 := by
  have h3 := h.three_le
  refine h.extend _ (by omega) fun e he => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem colGood_colLits :
    ∀ (ls : List (ℕ × Bool)) (o : ℕ) (s : ColSt), ColGood s → 3 ≤ o → o < s.next →
      ColGood (colLits ls o s)
  | [], o, s, h, ho3, ho => by
    refine h.extend _ le_rfl fun e he => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> omega
  | l :: ls, o, s, h, ho3, ho => by
    rw [colLits_cons]
    have h1 := colGood_colOcc (l := l) h
    refine colGood_colLits ls _ _ (colGood_colOr h1 (by simp) (by simp; omega)) ?_ ?_ <;>
      simp only [colOr_snd, colOr_next, colOcc_next] <;> omega

theorem colGood_colClause {C : CNFClause} {s : ColSt} (h : ColGood s) :
    ColGood (colClause C s) := by
  have h3 := h.three_le
  unfold colClause
  split
  · refine h.extend _ (by omega) fun e he => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> omega
  · exact colGood_colLits _ _ _ (colGood_colOcc h) h3 (by simp)

theorem colGood_foldl :
    ∀ (cs : CNF) (s : ColSt), ColGood s → ColGood (cs.foldl (fun s C => colClause C s) s)
  | [], _, h => h
  | _ :: cs, _, h => colGood_foldl cs _ (colGood_colClause h)

theorem colGood_colSt (φ : CNF) : ColGood (colSt φ) :=
  colGood_foldl _ _ colGood_init

/-- **The construction's edges lie below its vertex count.** For every CNF formula $\varphi$,
both endpoints of every edge emitted by the construction for $\varphi$ are smaller than the
number of vertices the construction allocates (its next free vertex). -/
theorem colSt_em_lt (φ : CNF) :
    ∀ e ∈ (colSt φ).em, e.1 < (colSt φ).next ∧ e.2 < (colSt φ).next :=
  fun e he => ⟨((colGood_colSt φ).em_lt e he).1, ((colGood_colSt φ).em_lt e he).2.1⟩

/-! ### Satisfiable formulas give 3-colorable graphs -/

/-- **Colorings that follow an assignment.** Let $s$ be a construction state, let
$v : \mathbb{N} \to \mathrm{Bool}$ be an assignment, and let $c : \mathbb{N} \to \{0, 1, 2\}$ be a
coloring. Then $c$ colors $s$ according to $v$ when $c(0) = 0$, $c(1) = 1$ and $c(2) = 2$ (the
palette vertices $T$, $F$, $B$), $c(a) \ne c(b)$ for every edge $(a, b)$ emitted in $s$, and for
every occurrence recorded in $s$ with variable $x$, polarity $b$, literal vertex $L$ and negation
vertex $M$: if $v(x) = b$ then $c(L) = 0$ and $c(M) = 1$, and otherwise $c(L) = 1$ and
$c(M) = 0$. -/
structure ColColored (v : ℕ → Bool) (c : ℕ → Fin 3) (s : ColSt) : Prop where
  /-- `T` is `0`. -/
  zero : c 0 = 0
  /-- `F` is `1`. -/
  one : c 1 = 1
  /-- `B` is `2`. -/
  two : c 2 = 2
  /-- The edges are properly colored. -/
  proper : ColProper c s.em
  /-- Occurrences are colored by `v`. -/
  occ : ∀ q ∈ s.prev, c q.2.2.1 = (if v q.1 = q.2.1 then 0 else 1) ∧
    c q.2.2.2 = (if v q.1 = q.2.1 then 1 else 0)

theorem colColored_colOcc {v : ℕ → Bool} {c : ℕ → Fin 3} {l : ℕ × Bool} {s : ColSt}
    (hg : ColGood s) (hc : ColColored v c s) :
    ∃ c', ColColored v c' (colOcc l s).1 ∧ (∀ k < s.next, c' k = c k) ∧
      c' s.next = (if v l.1 = l.2 then 0 else 1) := by
  let c' : ℕ → Fin 3 := fun k =>
    if k = s.next then (if v l.1 = l.2 then 0 else 1)
    else if k = s.next + 1 then (if v l.1 = l.2 then 1 else 0) else c k
  have hlt : ∀ k < s.next, c' k = c k := fun k hk => by
    simp [c', show k ≠ s.next by omega, show k ≠ s.next + 1 by omega]
  have hL : c' s.next = (if v l.1 = l.2 then 0 else 1) := by simp [c']
  have hM : c' (s.next + 1) = (if v l.1 = l.2 then 1 else 0) := by simp [c']
  have h3 := hg.three_le
  have hB : c' 2 = 2 := by rw [hlt 2 (by omega), hc.two]
  refine ⟨c', ⟨by rw [hlt 0 (by omega), hc.zero], by rw [hlt 1 (by omega), hc.one], hB, ?_, ?_⟩,
    hlt, hL⟩
  · intro e he
    simp only [colOcc_em, List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil,
      or_false] at he
    rcases he with (he | rfl | rfl | rfl) | ⟨q, hq, he⟩
    · obtain ⟨h1, h2, -⟩ := hg.em_lt e he
      rw [hlt _ h1, hlt _ h2]
      exact hc.proper e he
    · rw [hL, hM]
      exact tf_ne _ _
    · rw [hL, hB]
      exact tf_ne_two _ _
    · rw [hM, hB]
      exact ft_ne_two _ _
    · obtain ⟨hq1, hq2⟩ := hg.prev_lt q hq
      obtain ⟨hcq1, hcq2⟩ := hc.occ q hq
      unfold consEdges at he
      split_ifs at he with hx hpol
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · rw [hlt _ hq1, hM, hcq1, hx, hpol]
          exact tf_ne _ _
        · rw [hlt _ hq2, hL, hcq2, hx, hpol]
          exact (tf_ne _ _).symm
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · rw [hlt _ hq1, hL, hcq1, hx]
          exact tf_ne_of_ne _ _ _ hpol
        · rw [hlt _ hq2, hM, hcq2, hx]
          exact ft_ne_of_ne _ _ _ hpol
      · simp at he
  · intro q hq
    simp only [colOcc_prev, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨hL, hM⟩
    · obtain ⟨hq1, hq2⟩ := hg.prev_lt q hq
      rw [hlt _ hq1, hlt _ hq2]
      exact hc.occ q hq

theorem colColored_colOr {v : ℕ → Bool} {c : ℕ → Fin 3} {a o : ℕ} {s : ColSt}
    (hg : ColGood s) (hc : ColColored v c s) (ha : a < s.next) (ho : o < s.next)
    (ha2 : c a ≠ 2) (ho2 : c o ≠ 2) :
    ∃ c', ColColored v c' (colOr a o s).1 ∧ (∀ k < s.next, c' k = c k) ∧
      c' (s.next + 2) ≠ 2 ∧ (c' (s.next + 2) = 0 ↔ c a = 0 ∨ c o = 0) := by
  obtain ⟨cu, cv, cw, h1, h2, h3, h4, h5, h6, h7⟩ := or_gadget_colors (c a) (c o) ha2 ho2
  let c' : ℕ → Fin 3 := fun k =>
    if k = s.next then cu else if k = s.next + 1 then cv else if k = s.next + 2 then cw else c k
  have hlt : ∀ k < s.next, c' k = c k := fun k hk => by
    simp [c', show k ≠ s.next by omega, show k ≠ s.next + 1 by omega,
      show k ≠ s.next + 2 by omega]
  have hu : c' s.next = cu := by simp [c']
  have hv : c' (s.next + 1) = cv := by simp [c']
  have hw : c' (s.next + 2) = cw := by simp [c']
  have hn3 := hg.three_le
  have hB : c' 2 = 2 := by rw [hlt 2 (by omega), hc.two]
  refine ⟨c', ⟨by rw [hlt 0 (by omega), hc.zero], by rw [hlt 1 (by omega), hc.one], hB, ?_, ?_⟩,
    hlt, by rw [hw]; exact h6, by rw [hw]; exact h7⟩
  · intro e he
    simp only [colOr_em, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨he1, he2, -⟩ := hg.em_lt e he
      rw [hlt _ he1, hlt _ he2]
      exact hc.proper e he
    · rw [hlt _ ha, hu]
      exact h1
    · rw [hlt _ ho, hv]
      exact h2
    · rw [hu, hv]
      exact h3
    · rw [hu, hw]
      exact h4
    · rw [hv, hw]
      exact h5
    · rw [hw, hB]
      exact h6
  · intro q hq
    obtain ⟨hq1, hq2⟩ := hg.prev_lt q hq
    rw [hlt _ hq1, hlt _ hq2]
    exact hc.occ q hq

theorem colColored_colLits {v : ℕ → Bool} (ls : List (ℕ × Bool)) :
    ∀ (o : ℕ) (s : ColSt) (c : ℕ → Fin 3), ColGood s → ColColored v c s → 3 ≤ o →
      o < s.next → c o ≠ 2 → (c o = 0 ∨ ∃ l ∈ ls, v l.1 = l.2) →
      ∃ c', ColColored v c' (colLits ls o s) := by
  induction ls with
  | nil =>
    intro o s c hg hc ho3 ho ho2 hsat
    have h0 : c o = 0 := by simpa using hsat
    refine ⟨c, ⟨hc.zero, hc.one, hc.two, fun e he => ?_, hc.occ⟩⟩
    simp only [colLits_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | rfl | rfl
    · exact hc.proper e he
    · rw [h0, hc.one]
      decide
    · rw [h0, hc.two]
      decide
  | cons l ls ih =>
    intro o s c hg hc ho3 ho ho2 hsat
    obtain ⟨c1, hc1, hlt1, hL⟩ := colColored_colOcc (l := l) hg hc
    have hg1 := colGood_colOcc (l := l) hg
    obtain ⟨c2, hc2, -, hw2, hw⟩ := colColored_colOr (a := s.next) (o := o) hg1 hc1
      (by simp) (by simp only [colOcc_next]; omega) (by rw [hL]; exact tf_ne_two _ _)
      (by rw [hlt1 o ho]; exact ho2)
    rw [colLits_cons]
    refine ih _ _ c2 (colGood_colOr hg1 (by simp) (by simp only [colOcc_next]; omega)) hc2
      (by simp only [colOr_snd, colOcc_next]; omega) (by simp) hw2 ?_
    rcases hsat with h0 | ⟨l', hl', hv⟩
    · exact Or.inl (hw.2 (Or.inr (by rw [hlt1 o ho]; exact h0)))
    · rcases List.mem_cons.1 hl' with rfl | hl'
      · exact Or.inl (hw.2 (Or.inl (by rw [hL]; simp [hv])))
      · exact Or.inr ⟨l', hl', hv⟩

theorem colColored_colClause {v : ℕ → Bool} {c : ℕ → Fin 3} {C : CNFClause} {s : ColSt}
    (hg : ColGood s) (hc : ColColored v c s) (hsat : ∃ l ∈ C, v l.1 = l.2) :
    ∃ c', ColColored v c' (colClause C s) := by
  obtain ⟨l', hl', hv⟩ := hsat
  cases hC : C.reverse with
  | nil => simp [List.reverse_eq_nil_iff.1 hC] at hl'
  | cons l ls =>
    simp only [colClause, hC]
    obtain ⟨c1, hc1, -, hL⟩ := colColored_colOcc (l := l) hg hc
    refine colColored_colLits ls _ _ c1 (colGood_colOcc hg) hc1 hg.three_le (by simp)
      (by rw [colOcc_snd, hL]; exact tf_ne_two _ _) ?_
    have : l' ∈ l :: ls := by rw [← hC]; simpa using hl'
    rcases List.mem_cons.1 this with rfl | hl''
    · left
      rw [colOcc_snd, hL]
      simp [hv]
    · exact Or.inr ⟨l', hl'', hv⟩

theorem colColored_foldl {v : ℕ → Bool} :
    ∀ (cs : CNF) (s : ColSt) (c : ℕ → Fin 3), ColGood s → ColColored v c s →
      (∀ C ∈ cs, ∃ l ∈ C, v l.1 = l.2) →
      ∃ c', ColColored v c' (cs.foldl (fun s C => colClause C s) s)
  | [], _, c, _, hc, _ => ⟨c, hc⟩
  | C :: cs, s, c, hg, hc, hsat => by
    obtain ⟨c1, hc1⟩ := colColored_colClause hg hc (hsat C List.mem_cons_self)
    exact colColored_foldl cs _ c1 (colGood_colClause hg) hc1
      fun C' hC' => hsat C' (List.mem_cons_of_mem _ hC')

theorem colorable_of_cnfSat {φ : CNF} (h : CNFSat φ) :
    (edgeGraph (colSt φ).next (colSt φ).em).Colorable 3 := by
  obtain ⟨v, hv⟩ := h
  let c₀ : ℕ → Fin 3 := fun k => if k = 0 then 0 else if k = 1 then 1 else 2
  have hc₀ : ColColored v c₀ ⟨3, [], [(0, 1), (0, 2), (1, 2)]⟩ := by
    refine ⟨rfl, rfl, rfl, fun e he => ?_, by simp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> decide
  obtain ⟨c, hc⟩ := colColored_foldl φ.reverse _ c₀ colGood_init hc₀ fun C hC => by
    obtain ⟨x, b, hxb, hvx⟩ := hv C (List.mem_reverse.1 hC)
    exact ⟨(x, b), hxb, hvx⟩
  exact (colorable_iff_exists_colProper (colGood_colSt φ).em_lt).2 ⟨c, hc.proper⟩

/-! ### 3-colorable graphs give satisfiable formulas -/

/-- **Output of the OR gadget under a proper 3-coloring.** Let $c : \mathbb{N} \to \{0, 1, 2\}$
with $c(2) = 2$, let $a$ and $o$ be natural numbers, let $s$ be a state of the SAT-to-3-COLOR
construction and let $E$ be a list of pairs of natural numbers such that $c(u) \ne c(v)$ for
every pair $(u, v)$ in $E$. Apply the OR gadget to $a$, $o$ and $s$, giving a new state and an
output vertex $w$, and suppose every edge in the emitted-edge list of the new state belongs to
$E$. If $c(a) \ne 2$ and $c(o) \ne 2$, then $c(w) \ne 2$, and if $c(w) = 0$ then $c(a) = 0$ or
$c(o) = 0$. -/
theorem sound_colOr {c : ℕ → Fin 3} {a o : ℕ} {s : ColSt} {E : List (ℕ × ℕ)} (h2 : c 2 = 2)
    (hp : ColProper c E) (hsub : (colOr a o s).1.em ⊆ E) (ha : c a ≠ 2) (ho : c o ≠ 2) :
    c (colOr a o s).2 ≠ 2 ∧ (c (colOr a o s).2 = 0 → c a = 0 ∨ c o = 0) := by
  have e : ∀ x y, (x, y) ∈ (colOr a o s).1.em → c x ≠ c y := fun x y h => hp _ (hsub h)
  have hw2 := e _ _ (show (s.next + 2, 2) ∈ _ by simp)
  rw [h2] at hw2
  refine ⟨hw2, or_gadget_sound _ _ (c s.next) (c (s.next + 1)) _ ha ho ?_ ?_ ?_ ?_ ?_⟩ <;>
    exact e _ _ (by simp)

theorem sound_colLits {c : ℕ → Fin 3} (h1 : c 1 = 1) (h2 : c 2 = 2) (ls : List (ℕ × Bool)) :
    ∀ (o : ℕ) (s : ColSt), ColProper c (colLits ls o s).em → c o ≠ 2 →
      c o = 0 ∨ ∃ q ∈ (colLits ls o s).prev, (q.1, q.2.1) ∈ ls ∧ c q.2.2.1 = 0 := by
  induction ls with
  | nil =>
    intro o s hp ho2
    have h := hp (o, 1) (by simp [colLits_nil])
    dsimp only at h
    rw [h1] at h
    left
    omega
  | cons l ls ih =>
    intro o s hp ho2
    rw [colLits_cons] at hp ⊢
    have g2 := colGrows_colLits ls (colOr (colOcc l s).2 o (colOcc l s).1).2
      (colOr (colOcc l s).2 o (colOcc l s).1).1
    have g1 := colGrows_colOr (colOcc l s).2 o (colOcc l s).1
    have hL2 : c (colOcc l s).2 ≠ 2 := by
      have := hp _ (g2.em (g1.em (show ((colOcc l s).2, 2) ∈ (colOcc l s).1.em by simp)))
      rwa [h2] at this
    obtain ⟨hw2, hor⟩ := sound_colOr h2 hp g2.em hL2 ho2
    rcases ih _ _ hp hw2 with hw0 | ⟨q, hq, hql, hq0⟩
    · rcases hor hw0 with h | h
      · exact Or.inr ⟨(l.1, l.2, s.next, s.next + 1), g2.prev (g1.prev (by simp)), by simp, h⟩
      · exact Or.inl h
    · exact Or.inr ⟨q, hq, List.mem_cons_of_mem _ hql, hq0⟩

theorem sound_colClause {c : ℕ → Fin 3} (h0 : c 0 = 0) (h1 : c 1 = 1) (h2 : c 2 = 2)
    {C : CNFClause} {s : ColSt} (hp : ColProper c (colClause C s).em) :
    ∃ q ∈ (colClause C s).prev, (q.1, q.2.1) ∈ C ∧ c q.2.2.1 = 0 := by
  cases hC : C.reverse with
  | nil =>
    simp only [colClause, hC] at hp
    have a := hp (s.next, 0) (by simp)
    have b := hp (s.next, 1) (by simp)
    have d := hp (s.next, 2) (by simp)
    dsimp only at a b d
    rw [h0] at a
    rw [h1] at b
    rw [h2] at d
    omega
  | cons l ls =>
    simp only [colClause, hC] at hp ⊢
    have g := colGrows_colLits ls (colOcc l s).2 (colOcc l s).1
    have hL2 : c (colOcc l s).2 ≠ 2 := by
      have := hp _ (g.em (show ((colOcc l s).2, 2) ∈ (colOcc l s).1.em by simp))
      rwa [h2] at this
    have hmem : ∀ x ∈ l :: ls, x ∈ C := fun x hx => by
      rw [← List.mem_reverse, hC]
      exact hx
    rcases sound_colLits h1 h2 ls _ _ hp hL2 with h | ⟨q, hq, hql, hq0⟩
    · exact ⟨(l.1, l.2, s.next, s.next + 1), g.prev (by simp), hmem _ (by simp), h⟩
    · exact ⟨q, hq, hmem _ (List.mem_cons_of_mem _ hql), hq0⟩

theorem sound_foldl {c : ℕ → Fin 3} (h0 : c 0 = 0) (h1 : c 1 = 1) (h2 : c 2 = 2) :
    ∀ (cs : CNF) (s : ColSt), ColProper c (cs.foldl (fun s C => colClause C s) s).em →
      ∀ C ∈ cs, ∃ q ∈ (cs.foldl (fun s C => colClause C s) s).prev,
        (q.1, q.2.1) ∈ C ∧ c q.2.2.1 = 0
  | [], _, _, _, hC => absurd hC List.not_mem_nil
  | C :: cs, s, hp, C', hC' => by
    have g := colGrows_foldl cs (colClause C s)
    rcases List.mem_cons.1 hC' with rfl | hC'
    · obtain ⟨q, hq, h⟩ := sound_colClause h0 h1 h2 (hp.mono g.em)
      exact ⟨q, g.prev hq, h⟩
    · exact sound_foldl h0 h1 h2 cs _ hp C' hC'

theorem cnfSat_of_colorable {φ : CNF}
    (h : (edgeGraph (colSt φ).next (colSt φ).em).Colorable 3) : CNFSat φ := by
  classical
  have hg := colGood_colSt φ
  obtain ⟨c₀, hc₀⟩ := (colorable_iff_exists_colProper hg.em_lt).1 h
  -- Rename the colors so that the palette is `0, 1, 2`.
  let c : ℕ → Fin 3 := fun k => if c₀ k = c₀ 0 then 0 else if c₀ k = c₀ 1 then 1 else 2
  have h01 : c₀ 0 ≠ c₀ 1 := hc₀ _ hg.palette.1
  have h02 : c₀ 0 ≠ c₀ 2 := hc₀ _ hg.palette.2.1
  have h12 : c₀ 1 ≠ c₀ 2 := hc₀ _ hg.palette.2.2
  have hp : ColProper c (colSt φ).em := fun e he => fin3_rename _ _ _ _ h01 (hc₀ e he)
  have h0 : c 0 = 0 := by simp [c]
  have h1 : c 1 = 1 := by simp [c, h01.symm]
  have h2 : c 2 = 2 := by simp [c, h02.symm, h12.symm]
  -- Every clause has an occurrence whose literal vertex is `T`.
  have hcl : ∀ C ∈ φ, ∃ q ∈ (colSt φ).prev, (q.1, q.2.1) ∈ C ∧ c q.2.2.1 = 0 :=
    fun C hC => sound_foldl h0 h1 h2 φ.reverse _ hp C (List.mem_reverse.2 hC)
  have htri : ∀ q ∈ (colSt φ).prev, c q.2.2.1 ≠ c q.2.2.2 ∧ c q.2.2.1 ≠ 2 ∧ c q.2.2.2 ≠ 2 :=
    fun q hq => by
      obtain ⟨t1, t2, t3⟩ := hg.tri q hq
      exact ⟨hp _ t1, h2 ▸ hp _ t2, h2 ▸ hp _ t3⟩
  -- The value of a variable read off one of its occurrences.
  let val : ℕ × Bool × ℕ × ℕ → Bool := fun q => if c q.2.2.1 = 0 then q.2.1 else !q.2.1
  have hpw : (colSt φ).prev.Pairwise fun q q' => q.1 = q'.1 → val q = val q' := by
    refine hg.cons.imp_of_mem fun {q q'} hq hq' hce hx => ?_
    obtain ⟨a1, a2, a3⟩ := htri q hq
    obtain ⟨-, b2, -⟩ := htri q' hq'
    unfold consEdges at hce
    split_ifs at hce with hx' hpol
    · dsimp only at hpol
      have e1 := hp _ (hce (q'.2.2.1, q.2.2.2) (by simp))
      dsimp only at e1
      have hiff : c q'.2.2.1 = 0 ↔ c q.2.2.1 = 0 := by omega
      simp only [val, hpol, hiff]
    · dsimp only at hpol
      have e1 := hp _ (hce (q'.2.2.1, q.2.2.1) (by simp))
      dsimp only at e1
      have hiff : c q'.2.2.1 = 0 ↔ ¬c q.2.2.1 = 0 := by omega
      have hneg : q'.2.1 = !q.2.1 := Bool.eq_not_iff.2 hpol
      by_cases hq0 : c q.2.2.1 = 0
      · simp [val, hq0, hiff.not.2 (not_not.2 hq0), hneg]
      · simp [val, hq0, hiff.2 hq0, hneg]
    · exact absurd hx.symm hx'
  have hcons : ∀ q ∈ (colSt φ).prev, ∀ q' ∈ (colSt φ).prev, q.1 = q'.1 → val q = val q' := by
    intro q hq q' hq' hx
    by_cases hqq : q = q'
    · rw [hqq]
    · have : Std.Symm fun q q' : ℕ × Bool × ℕ × ℕ => q.1 = q'.1 → val q = val q' :=
        ⟨fun _ _ h hab => (h hab.symm).symm⟩
      exact hpw.forall hq hq' hqq hx
  refine ⟨fun x => (((colSt φ).prev.find? fun q => q.1 == x).map val).getD false,
    fun C hC => ?_⟩
  obtain ⟨q, hq, hqC, hq0⟩ := hcl C hC
  refine ⟨q.1, q.2.1, hqC, ?_⟩
  change (((colSt φ).prev.find? fun q' => q'.1 == q.1).map val).getD false = q.2.1
  cases hf : (colSt φ).prev.find? fun q' => q'.1 == q.1 with
  | none => exact absurd (List.find?_eq_none.1 hf q hq) (by simp)
  | some q' =>
    have hx : q'.1 = q.1 := by simpa using List.find?_some hf
    simp only [Option.map_some, Option.getD_some]
    rw [hcons q' (List.mem_of_find?_eq_some hf) q hq hx]
    simp [val, hq0]

/-- **Correctness of the reduction from SAT to 3-coloring.** A CNF formula $\varphi$ is satisfiable
if and only if the graph built from $\varphi$ by the Garey–Johnson–Stockmeyer construction is
3-colorable. Here, writing $n$ for the number of vertices the construction allocates, the graph
has vertex set $\{0, \dots, n - 1\}$, and two distinct vertices are adjacent when the
construction emits an edge between them in either order. -/
theorem cnfSat_iff_colorable (φ : CNF) :
    CNFSat φ ↔ (edgeGraph (colSt φ).next (colSt φ).em).Colorable 3 :=
  ⟨colorable_of_cnfSat, cnfSat_of_colorable⟩

/-! ### The reduction on bit strings -/

/-- **Correctness of the SAT to 3-COLOR map on bit strings.** For every bit string $x$, SAT
accepts $x$ if and only if 3-COLOR accepts the image of $x$ under the SAT to 3-COLOR reduction
map on bit strings. -/
theorem satDec_eq_col3Dec_reduceCol (x : List Bool) : satDec x = col3Dec (reduceCol x) := by
  unfold reduceCol
  split
  next φ h =>
    rw [decodeCNF_eq_some_iff] at h
    subst h
    rw [Bool.eq_iff_iff, DenseSAT.ToBinary.satDec_encodeCNF, toCol, col3Dec_encodeE_eq_true,
      cnfSat_iff_colorable, edgeGraph_reverse]
    simp only [List.mem_reverse]
    exact ⟨fun h => ⟨colSt_em_lt φ, h⟩, fun h => h.2⟩
  next h => rw [DenseSAT.ToBinary.satDec_of_decodeCNF_eq_none h, col3Dec_noCol]

end Cslib.Complexity.Karp
