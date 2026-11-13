/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.SegmentIntersection
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Data.Fintype.Card

/-!
# Sweeping: whether any two segments intersect

CLRS `ANY-SEGMENTS-INTERSECT` (third edition, Section 33.2): sort the `2n` endpoints from left to
right (left endpoints before right endpoints at equal `x`, then lower `y` first), and sweep a
vertical line across them, keeping the segments it crosses ordered from bottom to top. At a left
endpoint the segment is inserted and tested against its new neighbours; at a right endpoint its
two neighbours, which become adjacent, are tested against each other and the segment is deleted.
The tests are `SEGMENTS-INTERSECT` from `SegmentIntersection.lean`, and the insertion position is
found with `DIRECTION`.

## Main results

* `anySegmentsIntersect_ret_eq_true_iff` (CLRS Theorem 33.1): under CLRS's assumptions that no
  segment is vertical and no three segments share a point, the sweep returns `true` exactly when
  two distinct segments intersect.
* `anySegmentsIntersect_time_le`: the cost is at most `n² + 24 n`.

The proof follows CLRS. Soundness holds because every report comes from a test of two distinct
segments (`AnySegments.exists_meets_of_run_eq_none`). For completeness let `p` be a leftmost
intersection point, of segments `a` and `b` (`AnySegments.exists_leftmost_meet`). Left of `p` no
two segments cross, so the status list stays sorted by height (`AnySegments.run_pairwise_lt`) and
is sorted non-strictly on the line `x = p.1` (`AnySegments.run_pairwise_le`); every pair of
neighbours has been tested (`AnySegments.run_isChain`). If `p` is the left endpoint of `a`,
inserting `a` places it next to `b`, the only listed segment through `p`
(`AnySegments.run_eq_none_of_left`). Otherwise `a` and `b` are neighbours just before the sweep
reaches `p`, since a segment between them would pass through `p` too
(`AnySegments.run_eq_none_of_lt`).

Points are pairs over a linearly ordered field (`ℚ` for execution, `ℝ`), segments are Mathlib's
`segment 𝕜 p q`, and the input is `n` segments indexed by `Fin n`, each given by its two endpoints
in either order.

The first two sections are general facts used by the sweep: a non-vertical segment is the graph of
`lineY` over its `x`-range, two such segments that change order between two abscissas cross in
between, and their intersection has a leftmost point; and insertion into sorted lists. They are
kept here, next to their only client, while MathlibExt changes are on hold for CI scoping (#8003),
and can be promoted to MathlibExt later.

## Cost model

One unit per `DIRECTION` and `ON-SEGMENT` evaluated, as in `SegmentIntersection.lean`: each
`SEGMENTS-INTERSECT` costs at most `8`, and inserting a segment costs one `DIRECTION` per listed
segment scanned. The status is a sorted list, so an insertion scans up to `n` segments and the
bound is `O(n²)`. CLRS keeps the status in a red-black tree for `O(n lg n)`; the sort and the
list bookkeeping (splitting at a deleted segment) are not charged.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

open Cslib.Algorithms.Lean TimeM

universe u

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ## Non-vertical segments as graphs -/

/-- **Height of a line at an abscissa.** For points $p = (p_1, p_2)$ and $q = (q_1, q_2)$ in $K^2$,
$K$ a field, and $x \in K$, this is $p_2 + (x - p_1)(q_2 - p_2)/(q_1 - p_1)$, with division by
zero read as $0$. When $p_1 \ne q_1$ it is the height at $x$ of the line through $p$ and $q$. -/
def lineY (p q : 𝕜 × 𝕜) (x : 𝕜) : 𝕜 := p.2 + (x - p.1) * (q.2 - p.2) / (q.1 - p.1)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem lineY_sub (p q : 𝕜 × 𝕜) (x x' : 𝕜) :
    lineY p q x - lineY p q x' = (x - x') * ((q.2 - p.2) / (q.1 - p.1)) := by
  simp only [lineY]
  ring

/-- **A non-vertical segment is the graph of its line.** Let $p$ and $q$ be points of the plane
over a linearly ordered field, where a point $z$ has coordinates $(z_1, z_2)$, and suppose
$p_1 < q_1$. A point $z$ lies on the segment from $p$ to $q$ if and only if $p_1 \le z_1 \le q_1$
and $z_2$ is the height at abscissa $z_1$ of the line through $p$ and $q$. -/
theorem mem_segment_iff_lineY {p q z : 𝕜 × 𝕜} (hpq : p.1 < q.1) :
    z ∈ segment 𝕜 p q ↔ p.1 ≤ z.1 ∧ z.1 ≤ q.1 ∧ z.2 = lineY p q z.1 := by
  have hd : q.1 - p.1 ≠ 0 := sub_ne_zero.2 hpq.ne'
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    have ha' : a = 1 - b := by linarith
    subst ha'
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    simp only [lineY]
    field_simp
    ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨1 - (z.1 - p.1) / (q.1 - p.1), (z.1 - p.1) / (q.1 - p.1),
      by rw [sub_nonneg, div_le_one (by linarith)]; linarith,
      div_nonneg (by linarith) (by linarith), by ring, ?_⟩
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, h3, lineY]
      field_simp
      ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem lineY_left (p q : 𝕜 × 𝕜) : lineY p q p.1 = p.2 := by simp [lineY]

omit [IsStrictOrderedRing 𝕜] in
/-- **DIRECTION as a scaled vertical offset.** Let $\Bbbk$ be a field with a linear order, let
$p, q, r \in \Bbbk^2$, writing $p = (p_x, p_y)$ and likewise for $q$ and $r$, with $p_x < q_x$, and
let $y_{pq}(x)$ be the height at $x$ of the line through $p$ and $q$. Then
$\mathrm{DIRECTION}(p, q, r) = (q_x - p_x)\,(y_{pq}(r_x) - r_y)$. -/
theorem direction_eq_lineY {p q : 𝕜 × 𝕜} (hpq : p.1 < q.1) (r : 𝕜 × 𝕜) :
    direction p q r = (q.1 - p.1) * (lineY p q r.1 - r.2) := by
  have hd : q.1 - p.1 ≠ 0 := sub_ne_zero.2 hpq.ne'
  simp only [direction, cross, Prod.fst_sub, Prod.snd_sub, lineY]
  field_simp
  ring

theorem direction_neg_iff {p q : 𝕜 × 𝕜} (hpq : p.1 < q.1) (r : 𝕜 × 𝕜) :
    direction p q r < 0 ↔ lineY p q r.1 < r.2 := by
  rw [direction_eq_lineY hpq, mul_neg_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨by linarith, by linarith⟩

/-- **Crossing of two non-vertical segments.** Let $K$ be a linearly ordered field, write $z_1$ for
the first coordinate of a point $z \in K^2$, and let $[p, q]$ and $[p', q']$ be segments in $K^2$
with $p_1 < q_1$ and $p'_1 < q'_1$. For $t \in K$ let $y(t)$ be the height at $t$ of the line
through $p$ and $q$, and $y'(t)$ that of the line through $p'$ and $q'$. Let $a < b$ with
$p_1 \le a$, $p'_1 \le a$, $b \le q_1$ and $b \le q'_1$. If $y(a) < y'(a)$ and $y'(b) \le y(b)$,
then some $z \in [p, q] \cap [p', q']$ has $a < z_1 \le b$, and $z_1 < b$ if moreover
$y'(b) < y(b)$. -/
theorem exists_mem_inter_of_cross {p q p' q' : 𝕜 × 𝕜} (hpq : p.1 < q.1) (hpq' : p'.1 < q'.1)
    {x₀ x₁ : 𝕜} (hx : x₀ < x₁) (hp : p.1 ≤ x₀) (hq : x₁ ≤ q.1) (hp' : p'.1 ≤ x₀)
    (hq' : x₁ ≤ q'.1) (h₀ : lineY p q x₀ < lineY p' q' x₀)
    (h₁ : lineY p' q' x₁ ≤ lineY p q x₁) :
    ∃ z ∈ segment 𝕜 p q ∩ segment 𝕜 p' q', x₀ < z.1 ∧ z.1 ≤ x₁ ∧
      (lineY p' q' x₁ < lineY p q x₁ → z.1 < x₁) := by
  set s := (q'.2 - p'.2) / (q'.1 - p'.1) - (q.2 - p.2) / (q.1 - p.1) with hs
  have hf : ∀ x, lineY p' q' x - lineY p q x =
      (lineY p' q' x₀ - lineY p q x₀) + (x - x₀) * s := by
    intro x
    have h1 := lineY_sub p q x x₀
    have h2 := lineY_sub p' q' x x₀
    rw [hs]
    linear_combination h2 - h1
  set f₀ := lineY p' q' x₀ - lineY p q x₀ with hf₀
  have hf₀pos : 0 < f₀ := by rw [hf₀]; linarith
  have hx1 := hf x₁
  have hsneg : s < 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  set r := x₀ - f₀ / s with hr
  have hrx : x₀ < r := by
    rw [hr, sub_eq_add_neg, lt_add_iff_pos_right, neg_pos]
    exact div_neg_of_pos_of_neg hf₀pos hsneg
  have hrs : (r - x₀) * s = -f₀ := by
    rw [hr, sub_sub_cancel_left, neg_mul, div_mul_cancel₀ _ hsneg.ne]
  have hrle : r ≤ x₁ := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hroot : lineY p' q' r = lineY p q r := by
    have := hf r
    linarith
  refine ⟨(r, lineY p q r), ⟨(mem_segment_iff_lineY hpq).2 ⟨by simp; linarith, by simp; linarith,
      rfl⟩, (mem_segment_iff_lineY hpq').2 ⟨by simp; linarith, by simp; linarith,
      by simp [hroot]⟩⟩, hrx, hrle, fun hlt => ?_⟩
  simp only
  by_contra hcon
  push Not at hcon
  nlinarith

/-- **Leftmost point of the intersection of two segments.** Let $K$ be a linearly ordered field,
write $x_1$ for the first coordinate of a point $x \in K^2$, and let $[p, q]$ and $[p', q']$ be
segments in $K^2$ with $p_1 < q_1$ and $p'_1 < q'_1$. If $[p, q] \cap [p', q']$ is nonempty, then
it contains a point $m$ with $m_1 \le w_1$ for every $w \in [p, q] \cap [p', q']$. -/
theorem exists_leftmost_mem_inter {p q p' q' z : 𝕜 × 𝕜} (hpq : p.1 < q.1) (hpq' : p'.1 < q'.1)
    (hz : z ∈ segment 𝕜 p q ∩ segment 𝕜 p' q') :
    ∃ m ∈ segment 𝕜 p q ∩ segment 𝕜 p' q', ∀ w ∈ segment 𝕜 p q ∩ segment 𝕜 p' q', m.1 ≤ w.1 := by
  obtain ⟨⟨hz1, hz2, hz3⟩, ⟨hz1', hz2', hz3'⟩⟩ :=
    And.intro ((mem_segment_iff_lineY hpq).1 hz.1) ((mem_segment_iff_lineY hpq').1 hz.2)
  set lo := max p.1 p'.1 with hlo
  by_cases h0 : lineY p q lo = lineY p' q' lo
  · refine ⟨(lo, lineY p q lo), ⟨(mem_segment_iff_lineY hpq).2 ⟨le_max_left _ _, ?_, rfl⟩,
      (mem_segment_iff_lineY hpq').2 ⟨le_max_right _ _, ?_, h0⟩⟩, fun w hw => ?_⟩
    · exact (max_le hz1 hz1').trans hz2
    · exact (max_le hz1 hz1').trans hz2'
    · obtain ⟨hw1, -, -⟩ := (mem_segment_iff_lineY hpq).1 hw.1
      obtain ⟨hw1', -, -⟩ := (mem_segment_iff_lineY hpq').1 hw.2
      exact max_le hw1 hw1'
  · refine ⟨z, hz, fun w hw => ?_⟩
    obtain ⟨-, -, hw3⟩ := (mem_segment_iff_lineY hpq).1 hw.1
    obtain ⟨-, -, hw3'⟩ := (mem_segment_iff_lineY hpq').1 hw.2
    by_contra hlt
    push Not at hlt
    -- two distinct zeros of the affine difference force it to vanish everywhere
    have e1 := lineY_sub p q z.1 w.1
    have e2 := lineY_sub p' q' z.1 w.1
    have e3 := lineY_sub p q lo w.1
    have e4 := lineY_sub p' q' lo w.1
    have hzw : z.1 - w.1 ≠ 0 := sub_ne_zero.2 hlt.ne'
    have hslope : (q.2 - p.2) / (q.1 - p.1) = (q'.2 - p'.2) / (q'.1 - p'.1) := by
      apply mul_left_cancel₀ hzw
      linear_combination -e1 + e2 - hz3 + hz3' + hw3 - hw3'
    apply h0
    linear_combination e3 - e4 + hw3' - hw3 + (lo - w.1) * hslope

/-! ## Sorted lists of graphs -/

section Lists

variable {α : Type*} {f : α → 𝕜} {y : 𝕜}

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **Inserting into a strictly sorted list.** Let $f$ map a type $\alpha$ to a linearly ordered
set, let $T$ be a list over $\alpha$ with $f(j) < f(k)$ whenever $j$ occurs before $k$, let
$i \in \alpha$ be such that $f(j) \ne f(i)$ for every $j$ in $T$, and let $P$ be a predicate that
holds for an element $j$ of $T$ exactly when $f(j) < f(i)$. Insert $i$ just before the first
element of $T$ not satisfying $P$: the list made of the longest prefix of $T$ satisfying $P$, then
$i$, then the rest of $T$. In this list, $f(j) < f(k)$ whenever $j$ occurs before $k$. -/
theorem pairwise_takeWhile_append_cons_dropWhile_lt {T : List α} {i : α} (p : α → Bool)
    (hp : ∀ j ∈ T, p j = true ↔ f j < f i) (hT : T.Pairwise (fun j k => f j < f k))
    (hne : ∀ j ∈ T, f j ≠ f i) :
    (T.takeWhile p ++ i :: T.dropWhile p).Pairwise (fun j k => f j < f k) := by
  have hsplit := List.takeWhile_append_dropWhile (p := p) (l := T)
  have hA : ∀ j ∈ T.takeWhile p, f j < f i := fun j hj =>
    (hp j ((List.takeWhile_prefix p).subset hj)).1 (List.mem_takeWhile_imp hj)
  have hB : ∀ k ∈ T.dropWhile p, f i < f k := by
    intro k hk
    obtain ⟨b, B, hbB⟩ : ∃ b B, T.dropWhile p = b :: B := by
      cases h : T.dropWhile p with
      | nil => rw [h] at hk; simp at hk
      | cons b B => exact ⟨b, B, rfl⟩
    have hb : p b = false := by
      have := List.head_dropWhile_not p (l := T) (by rw [hbB]; simp)
      simpa [hbB] using this
    have hbT : b ∈ T := (List.dropWhile_suffix p).subset (by rw [hbB]; simp)
    have hfb : f i < f b := by
      have h1 : ¬ f b < f i := fun h => by simp [(hp b hbT).2 h] at hb
      exact lt_of_le_of_ne (not_lt.1 h1) (hne b hbT).symm
    rw [hbB] at hk
    rcases List.mem_cons.1 hk with rfl | hk
    · exact hfb
    · have hpw : (b :: B).Pairwise (fun j k => f j < f k) := by
        rw [← hbB]
        exact hT.sublist (List.dropWhile_suffix p).sublist
      exact hfb.trans (List.rel_of_pairwise_cons hpw hk)
  rw [← hsplit] at hT
  rw [List.pairwise_append] at hT ⊢
  refine ⟨hT.1, List.pairwise_cons.2 ⟨hB, hT.2.1⟩, fun j hj k hk => ?_⟩
  rcases List.mem_cons.1 hk with rfl | hk
  · exact hA j hj
  · exact hT.2.2 j hj k hk

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **Inserting into a weakly sorted list.** Let $f$ map a type $\alpha$ to a linearly ordered
set, let $T$ be a list over $\alpha$ with $f(j) \le f(k)$ whenever $j$ occurs before $k$, let
$i \in \alpha$, and let $P$ be a predicate that holds for an element $j$ of $T$ exactly when
$f(j) < f(i)$. Insert $i$ just before the first element of $T$ not satisfying $P$: the list made
of the longest prefix of $T$ satisfying $P$, then $i$, then the rest of $T$. In this list,
$f(j) \le f(k)$ whenever $j$ occurs before $k$. -/
theorem pairwise_takeWhile_append_cons_dropWhile_le {T : List α} {i : α} (p : α → Bool)
    (hp : ∀ j ∈ T, p j = true ↔ f j < f i) (hT : T.Pairwise (fun j k => f j ≤ f k)) :
    (T.takeWhile p ++ i :: T.dropWhile p).Pairwise (fun j k => f j ≤ f k) := by
  have hsplit := List.takeWhile_append_dropWhile (p := p) (l := T)
  have hA : ∀ j ∈ T.takeWhile p, f j ≤ f i := fun j hj =>
    ((hp j ((List.takeWhile_prefix p).subset hj)).1 (List.mem_takeWhile_imp hj)).le
  have hB : ∀ k ∈ T.dropWhile p, f i ≤ f k := by
    intro k hk
    obtain ⟨b, B, hbB⟩ : ∃ b B, T.dropWhile p = b :: B := by
      cases h : T.dropWhile p with
      | nil => rw [h] at hk; simp at hk
      | cons b B => exact ⟨b, B, rfl⟩
    have hb : p b = false := by
      have := List.head_dropWhile_not p (l := T) (by rw [hbB]; simp)
      simpa [hbB] using this
    have hbT : b ∈ T := (List.dropWhile_suffix p).subset (by rw [hbB]; simp)
    have hfb : f i ≤ f b := not_lt.1 fun h => by simp [(hp b hbT).2 h] at hb
    rw [hbB] at hk
    rcases List.mem_cons.1 hk with rfl | hk
    · exact hfb
    · have hpw : (b :: B).Pairwise (fun j k => f j ≤ f k) := by
        rw [← hbB]
        exact hT.sublist (List.dropWhile_suffix p).sublist
      exact hfb.trans (List.rel_of_pairwise_cons hpw hk)
  rw [← hsplit] at hT
  rw [List.pairwise_append] at hT ⊢
  refine ⟨hT.1, List.pairwise_cons.2 ⟨hB, hT.2.1⟩, fun j hj k hk => ?_⟩
  rcases List.mem_cons.1 hk with rfl | hk
  · exact hA j hj
  · exact hT.2.2 j hj k hk

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **First element at or above a uniquely attained height.** Let $f$ map a type to a linearly
ordered set, let $y$ be a value, and let $T$ be a list sorted non-strictly by $f$, that is,
$f(j) \le f(k)$ whenever $j$ occurs before $k$ in $T$. Suppose $b$ lies in $T$ with $f(b) = y$,
and every element $c \ne b$ of $T$ has $f(c) \ne y$. Then removing from $T$ its longest prefix of
elements $j$ with $f(j) < y$ leaves a list whose first element is $b$. -/
theorem head?_dropWhile_eq_of_unique {T : List α} {b : α} (p : α → Bool)
    (hp : ∀ j ∈ T, p j = true ↔ f j < y) (hT : T.Pairwise (fun j k => f j ≤ f k)) (hb : b ∈ T)
    (hfb : f b = y) (huniq : ∀ c ∈ T, c ≠ b → f c ≠ y) :
    (T.dropWhile p).head? = some b := by
  have hsplit := List.takeWhile_append_dropWhile (p := p) (l := T)
  have hbA : b ∉ T.takeWhile p := fun h => by
    have := (hp b hb).1 (List.mem_takeWhile_imp h)
    rw [hfb] at this
    exact lt_irrefl _ this
  have hbB : b ∈ T.dropWhile p := by
    rw [← hsplit] at hb
    rcases List.mem_append.1 hb with h | h
    · exact absurd h hbA
    · exact h
  obtain ⟨c, B, hcB⟩ : ∃ c B, T.dropWhile p = c :: B := by
    cases h : T.dropWhile p with
    | nil => rw [h] at hbB; simp at hbB
    | cons c B => exact ⟨c, B, rfl⟩
  rw [hcB]
  simp only [List.head?_cons, Option.some.injEq]
  by_contra hcb
  have hcT : c ∈ T := (List.dropWhile_suffix p).subset (by rw [hcB]; simp)
  have hc : p c = false := by
    have := List.head_dropWhile_not p (l := T) (by rw [hcB]; simp)
    simpa [hcB] using this
  have hyc : y < f c := lt_of_le_of_ne (not_lt.1 fun h => by simp [(hp c hcT).2 h] at hc)
    (huniq c hcT hcb).symm
  have hpw : (c :: B).Pairwise (fun j k => f j ≤ f k) := by
    rw [← hcB]
    exact hT.sublist (List.dropWhile_suffix p).sublist
  rw [hcB] at hbB
  rcases List.mem_cons.1 hbB with h | h
  · exact hcb h.symm
  · have := List.rel_of_pairwise_cons hpw h
    rw [hfb] at this
    exact absurd this (not_le.2 hyc)

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **Splitting a list at two distinct members.** If $a$ and $b$ are distinct members of a list
$T$, then there are elements $u$, $w$ with either $u = a$ and $w = b$, or $u = b$ and $w = a$, and
lists $A$, $M$, $B$ such that $T$ is the concatenation of $A$, the element $u$, $M$, the element
$w$ and $B$, in this order. -/
theorem exists_append_of_mem_of_mem {T : List α} {a b : α} (ha : a ∈ T) (hb : b ∈ T)
    (hab : a ≠ b) :
    ∃ u w A M B, (u = a ∧ w = b ∨ u = b ∧ w = a) ∧ T = A ++ u :: (M ++ w :: B) := by
  obtain ⟨A, R, rfl⟩ := List.append_of_mem ha
  rcases List.mem_append.1 hb with hbA | hbR
  · obtain ⟨A', M, rfl⟩ := List.append_of_mem hbA
    exact ⟨b, a, A', M, R, Or.inr ⟨rfl, rfl⟩, by simp⟩
  · rcases List.mem_cons.1 hbR with h | hbR
    · exact absurd h.symm hab
    · obtain ⟨M, B, rfl⟩ := List.append_of_mem hbR
      exact ⟨a, b, A, M, B, Or.inl ⟨rfl, rfl⟩, rfl⟩

end Lists

/-! ## The algorithm -/

namespace AnySegments

variable {n : ℕ} (S : Fin n → (𝕜 × 𝕜) × (𝕜 × 𝕜))

/-- **Left endpoint of a segment.** Let $K$ be a linearly ordered set and $S$ a family of segments
in $K^2$, segment $i$ being given by its two endpoints $(a, b)$ in either order. The left endpoint
of segment $i$ is $a$ if $a_1 \le b_1$ and $b$ otherwise, where $a_1$ and $b_1$ are the first
coordinates. -/
def left (i : Fin n) : 𝕜 × 𝕜 := if (S i).1.1 ≤ (S i).2.1 then (S i).1 else (S i).2

/-- **Right endpoint of a segment.** Write $z_1$ for the abscissa of a point $z$. If segment $i$
is given by the endpoints $u$ and $v$, in this order, its right endpoint is $v$ when
$u_1 \le v_1$ and $u$ otherwise. -/
def right (i : Fin n) : 𝕜 × 𝕜 := if (S i).1.1 ≤ (S i).2.1 then (S i).2 else (S i).1

/-- **Sweep event.** For $n$ segments indexed by $0, \dots, n-1$, an event is a pair $(i, b)$ of a
segment index $i$ and a Boolean $b$; it stands for the left endpoint of segment $i$ when $b$ is
true and for its right endpoint when $b$ is false. -/
abbrev Event (n : ℕ) := Fin n × Bool

/-- **Endpoint of an event.** The point of the sweep event $(i, b)$ is the left endpoint of
segment $i$ when $b$ is true (a left-endpoint event) and the right endpoint of segment $i$ when
$b$ is false. -/
def point (e : Event n) : 𝕜 × 𝕜 := if e.2 then left S e.1 else right S e.1

/-- **Sweep order on endpoint events.** Let $K$ be a linearly ordered set and $S$ a family of
segments in $K^2$, each given by its two endpoints. An endpoint event $e$ of $S$ standing for the
point $(x, y)$ gets the key $(x, \varepsilon, y)$, compared lexicographically, where
$\varepsilon = 0$ if $e$ is a left endpoint and $\varepsilon = 1$ if it is a right endpoint. So
events are ordered by $x$; at equal $x$, left endpoints come first; then by $y$. This is the
endpoint order of CLRS. -/
def key (e : Event n) : 𝕜 ×ₗ (ℕ ×ₗ 𝕜) :=
  toLex ((point S e).1, toLex (if e.2 then 0 else 1, (point S e).2))

/-- **Sorted sweep events.** For $n$ segments, each given by its two endpoints, the left endpoint
of a segment is its endpoint with the smaller $x$-coordinate, or its first given endpoint when
both $x$-coordinates agree, and the right endpoint is the other one. The event list consists of
the $2n$ events, the left and the right endpoint of each segment, sorted by the $x$-coordinate
of the endpoint, with left endpoints before right endpoints at equal $x$, and then by the
$y$-coordinate of the endpoint; events that tie appear in increasing order of segment index.
This is line 2 of CLRS ANY-SEGMENTS-INTERSECT. -/
def events : List (Event n) :=
  ((List.finRange n).map (·, true) ++ (List.finRange n).map (·, false)).mergeSort
    fun e f => decide (key S e ≤ key S f)

/-- **Segment strictly below a point.** For a segment $j$, write $l_j$ for its endpoint with the
smaller $x$-coordinate, or for its first given endpoint when both $x$-coordinates agree, and $r_j$
for its other endpoint. For a point $q$, segment $j$ is below $q$ when
$\mathrm{DIRECTION}(l_j, r_j, q) < 0$.

For a non-vertical segment this says that the line through $l_j$ and $r_j$ passes strictly below
$q$ at the abscissa of $q$. -/
def below (j : Fin n) (q : 𝕜 × 𝕜) : Bool := decide (direction (left S j) (right S j) q < 0)

/-- **Intersection test for two input segments.** Given $n$ segments in the plane over a
linearly ordered field, each given by its two endpoints, and indices $i, j < n$, this runs CLRS
`SEGMENTS-INTERSECT` on the left and right endpoints of segment $i$ and the left and right
endpoints of segment $j$. It returns that procedure's Boolean answer together with its cost in
`DIRECTION` and `ON-SEGMENT` evaluations. -/
def test (i j : Fin n) : TimeM ℕ Bool :=
  segmentsIntersect (left S i) (right S i) (left S j) (right S j)

/-- **Testing a segment against an optional neighbour.** Given a segment $i$ and possibly a
neighbour $j$, return the result of `SEGMENTS-INTERSECT` on segments $i$ and $j$, with its cost,
when $j$ is given, and return false at no cost when there is no neighbour. -/
def testOpt (i : Fin n) : Option (Fin n) → TimeM ℕ Bool
  | none => pure false
  | some j => test S i j

/-- **Testing the neighbours of a deleted segment.** Given $n$ segments in the plane over a
linearly ordered field and two optional segment indices $a$ and $b$ (in the sweep, the segments
just below and just above a deleted segment, when they exist), this runs the intersection test
of segments $a$ and $b$ when both indices are present, and otherwise returns `false` at no
cost. -/
def testPair : Option (Fin n) → Option (Fin n) → TimeM ℕ Bool
  | some a, some b => test S a b
  | _, _ => pure false

/-- **The any-segments-intersect sweep.** CLRS `ANY-SEGMENTS-INTERSECT`, lines 3-11: the sweep
processes a list of events with a status list $T$ of segments ordered from bottom to top, returns
true as soon as an intersection test succeeds, and returns false once the events run out. At the
left endpoint $p$ of segment $i$, split $T$ as $A$ followed by $B$, where $A$ is the longest
initial part of $T$ whose segments pass strictly below $p$ by the `DIRECTION` test; this scan
costs $\min(|A| + 1, |T|)$, one `DIRECTION` per segment scanned. Segment $i$ is tested with
`SEGMENTS-INTERSECT` against the first segment of $B$ and then against the last segment of $A$
(when these exist), and the sweep continues with $A$, then $i$, then $B$. At the right endpoint
of segment $i$, with $A$ the part of $T$ before the first occurrence of $i$ and $B$ the part
after it, the last segment of $A$ is tested against the first segment of $B$ when both exist,
and the sweep continues with $A$ followed by $B$. -/
def sweep : List (Event n) → List (Fin n) → TimeM ℕ Bool
  | [], _ => pure false
  | (i, true) :: es, T => do
      ✓[min ((T.takeWhile (below S · (left S i))).length + 1) T.length]
      let b₁ ← testOpt S i (T.dropWhile (below S · (left S i))).head?
      if b₁ then pure true else do
      let b₂ ← testOpt S i (T.takeWhile (below S · (left S i))).getLast?
      if b₂ then pure true else
      sweep es (T.takeWhile (below S · (left S i)) ++ i :: T.dropWhile (below S · (left S i)))
  | (i, false) :: es, T => do
      let b ← testPair S (T.takeWhile (· != i)).getLast? (T.dropWhile (· != i)).tail.head?
      if b then pure true else sweep es (T.takeWhile (· != i) ++ (T.dropWhile (· != i)).tail)

/-- **One step of the sweep.** A step takes an event and a status list $T$ of segments, ordered
from bottom to top, and returns a new status list, or no result when an intersection is reported.
At the left endpoint $p$ of segment $i$, split $T$ as $A$ followed by $B$, where $A$ is the longest
initial part of $T$ whose segments pass strictly below $p$ by the `DIRECTION` test. If
`SEGMENTS-INTERSECT` reports that $i$ meets the first segment of $B$ or the last segment of $A$
(when these exist), there is no result; otherwise the new status list is $A$, then $i$, then $B$.
At the right endpoint of segment $i$, let $A$ be the part of $T$ before the first occurrence of
$i$ and $B$ the part after it (so $A$ is all of $T$ and $B$ is empty when $i$ does not occur). If
both the last segment of $A$ and the first segment of $B$ exist and `SEGMENTS-INTERSECT` reports
that they meet, there is no result; otherwise the new status list is $A$ followed by $B$. -/
def step : Event n → List (Fin n) → Option (List (Fin n))
  | (i, true), T =>
      if (testOpt S i (T.dropWhile (below S · (left S i))).head?).ret ||
          (testOpt S i (T.takeWhile (below S · (left S i))).getLast?).ret then none
      else some (T.takeWhile (below S · (left S i)) ++ i :: T.dropWhile (below S · (left S i)))
  | (i, false), T =>
      if (testPair S (T.takeWhile (· != i)).getLast? (T.dropWhile (· != i)).tail.head?).ret then
        none
      else some (T.takeWhile (· != i) ++ (T.dropWhile (· != i)).tail)

/-- **Running the sweep over a list of events.** Starting from a status list $T$, the sweep steps
are applied to the events in order, each to the status list left by the previous one. The result
is the final status list, or no result as soon as some step reports an intersection; on the empty
list of events the result is $T$. -/
def run : List (Event n) → List (Fin n) → Option (List (Fin n))
  | [], T => some T
  | e :: es, T => (step S e T).bind (run es)

omit [IsStrictOrderedRing 𝕜] in
theorem sweep_ret (E : List (Event n)) (T : List (Fin n)) :
    (sweep S E T).ret = (run S E T).isNone := by
  induction E generalizing T with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨i, _ | _⟩ := e
    · simp only [sweep, ret_bind, run, step]
      split_ifs with h <;> simp [ih]
    · simp only [sweep, ret_bind, run, step]
      by_cases h1 : (testOpt S i (T.dropWhile (below S · (left S i))).head?).ret = true
      · simp [h1]
      · by_cases h2 : (testOpt S i (T.takeWhile (below S · (left S i))).getLast?).ret = true
        · simp [h1, h2]
        · simp only [Bool.not_eq_true] at h1 h2
          simp [h1, h2, ih]

omit [IsStrictOrderedRing 𝕜] in
theorem run_append (P Q : List (Event n)) (T : List (Fin n)) :
    run S (P ++ Q) T = (run S P T).bind (run S Q) := by
  induction P generalizing T with
  | nil => simp [run]
  | cons e es ih =>
    simp only [List.cons_append, run, ih]
    cases step S e T <;> simp

omit [IsStrictOrderedRing 𝕜] in
theorem run_concat (P : List (Event n)) (e : Event n) (T : List (Fin n)) :
    run S (P ++ [e]) T = (run S P T).bind (step S e) := by
  rw [run_append]
  cases run S P T <;> simp [run]

/-! ## Endpoints and events -/

section Events

variable {S}

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem left_fst_le (i : Fin n) : (left S i).1 ≤ (right S i).1 := by
  unfold left right
  split_ifs with h
  · exact h
  · exact (not_le.1 h).le

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem left_fst_lt {i : Fin n} (hv : (S i).1.1 ≠ (S i).2.1) : (left S i).1 < (right S i).1 := by
  unfold left right
  split_ifs with h
  · exact lt_of_le_of_ne h hv
  · exact not_le.1 h

omit [IsStrictOrderedRing 𝕜] in
theorem segment_left_right (i : Fin n) :
    segment 𝕜 (left S i) (right S i) = segment 𝕜 (S i).1 (S i).2 := by
  unfold left right
  split_ifs
  · rfl
  · exact segment_symm 𝕜 _ _

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **Left endpoint events precede right endpoint events.** Let $K$ be a linearly ordered set
and $S$ a family of segments in $K^2$, each given by its two endpoints. For every segment $i$ of
$S$, the left endpoint event of $i$ is strictly smaller than its right endpoint event in the sweep
order on events (by $x$-coordinate, then left endpoints before right endpoints, then by
$y$-coordinate). -/
theorem key_left_lt_right (i : Fin n) : key S (i, true) < key S (i, false) := by
  simp only [key, point, ite_true, Bool.false_eq_true, ite_false, Prod.Lex.toLex_lt_toLex]
  rcases (left_fst_le (S := S) i).lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, Or.inl (by norm_num)⟩

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem mem_events (e : Event n) : e ∈ events S := by
  rw [events, (List.mergeSort_perm _ _).mem_iff]
  obtain ⟨i, _ | _⟩ := e <;> simp

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem nodup_events : (events S).Nodup := by
  rw [events, (List.mergeSort_perm _ _).nodup_iff, List.nodup_append]
  refine ⟨(List.nodup_finRange n).map fun _ _ h => by simpa using h,
    (List.nodup_finRange n).map fun _ _ h => by simpa using h, ?_⟩
  simp

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem sorted_events : (events S).Pairwise fun e f => key S e ≤ key S f := by
  refine (List.pairwise_mergeSort (fun a b c hab hbc => ?_) (fun a b => ?_) _).imp
    fun h => of_decide_eq_true h
  · simp only [decide_eq_true_eq] at hab hbc ⊢
    exact hab.trans hbc
  · simpa using le_total (key S a) (key S b)

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem key_le_of_eq_append {P Q : List (Event n)} (hE : events S = P ++ Q) {e f : Event n}
    (he : e ∈ P) (hf : f ∈ Q) : key S e ≤ key S f := by
  have h := sorted_events (S := S)
  rw [hE, List.pairwise_append] at h
  exact h.2.2 e he f hf

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **A sweep prefix with a right endpoint has its left endpoint.** Let $K$ be a linearly ordered
set and $S$ a family of $n$ segments in $K^2$, each given by its two endpoints. If the sorted sweep
event list of $S$ is a list $P$ followed by a list $Q$, and $P$ contains the right endpoint event
of a segment $j$, then $P$ also contains the left endpoint event of $j$. -/
theorem left_mem_of_right_mem {P Q : List (Event n)} (hE : events S = P ++ Q) {j : Fin n}
    (hj : (j, false) ∈ P) : (j, true) ∈ P := by
  obtain ⟨P₁, P₂, rfl⟩ := List.append_of_mem hj
  have hmem := mem_events (S := S) (j, true)
  rw [hE] at hmem
  simp only [List.append_assoc, List.cons_append, List.mem_append, List.mem_cons,
    Prod.mk.injEq, Bool.true_eq_false, and_false, false_or] at hmem
  rcases hmem with h | h
  · exact List.mem_append_left _ h
  · exfalso
    have := key_le_of_eq_append (S := S) (P := P₁ ++ [(j, false)]) (Q := P₂ ++ Q) (by simp [hE])
      (e := (j, false)) (f := (j, true)) (by simp) (List.mem_append.2 h)
    exact absurd this (not_le.2 (key_left_lt_right j))

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem fst_le_of_key_le {e f : Event n} (h : key S e ≤ key S f) :
    (point S e).1 ≤ (point S f).1 := by
  simp only [key, Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

end Events

/-! ## Invariants of the status list -/

section Invariants

variable {S}

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **Splitting a list at the first occurrence of a member.** If $i$ occurs in a list $T$ of
indices in $\{0, \dots, n-1\}$, then $T$ is the longest initial part of $T$ not containing $i$,
followed by $i$, followed by the part of $T$ after the first occurrence of $i$. -/
theorem takeWhile_append_cons_tail_dropWhile {T : List (Fin n)} {i : Fin n} (hi : i ∈ T) :
    T.takeWhile (· != i) ++ i :: (T.dropWhile (· != i)).tail = T := by
  have hsplit := List.takeWhile_append_dropWhile (p := (· != i)) (l := T)
  cases h : T.dropWhile (· != i) with
  | nil =>
    rw [h, List.append_nil] at hsplit
    rw [← hsplit] at hi
    have := List.mem_takeWhile_imp hi
    simp at this
  | cons c B =>
    have hc := List.head_dropWhile_not (· != i) (l := T) (by rw [h]; simp)
    simp only [h, List.head_cons, bne_eq_false_iff_eq] at hc
    subst hc
    rw [h] at hsplit
    simpa using hsplit

omit [IsStrictOrderedRing 𝕜] in
/-- **The sweep status holds the active segments.** Let $P$ be an initial part of the sorted list
of events. If running the sweep over $P$ from the empty status list reports no intersection and
ends with status list $T$, then $T$ has no repeated entries, and a segment $j$ belongs to $T$
exactly when the left endpoint event of $j$ is in $P$ and the right endpoint event of $j$ is not. -/
theorem run_mem_iff {P Q : List (Event n)} (hE : events S = P ++ Q) {T : List (Fin n)}
    (hT : run S P [] = some T) : T.Nodup ∧ ∀ j, j ∈ T ↔ (j, true) ∈ P ∧ (j, false) ∉ P := by
  induction P using List.reverseRecOn generalizing Q T with
  | nil =>
    simp only [run, Option.some.injEq] at hT
    subst hT
    simp
  | append_singleton P' e ih =>
    rw [run_concat] at hT
    obtain ⟨T', hT', hstep⟩ := Option.bind_eq_some_iff.1 hT
    have hE' : events S = P' ++ e :: Q := by rw [hE]; simp
    obtain ⟨hnd, hmem⟩ := ih hE' hT'
    have hnodup := nodup_events (S := S)
    rw [hE'] at hnodup
    have heP : e ∉ P' := fun h => by
      rw [List.nodup_append] at hnodup
      exact hnodup.2.2 e h e (by simp) rfl
    obtain ⟨i, _ | _⟩ := e
    · -- a right endpoint: delete `i`
      have hiP : (i, true) ∈ P' := by
        have := left_mem_of_right_mem (S := S) (j := i) (P := P' ++ [(i, false)]) (Q := Q) hE
          (by simp)
        simpa using this
      have hiT : i ∈ T' := (hmem i).2 ⟨hiP, heP⟩
      simp only [step] at hstep
      split_ifs at hstep
      cases hstep
      have hsplit := takeWhile_append_cons_tail_dropWhile hiT
      rw [← hsplit] at hnd hmem
      refine ⟨(List.nodup_middle.1 hnd).of_cons, fun j => ?_⟩
      have hnd' := List.nodup_middle.1 hnd
      have := hmem j
      simp only [List.mem_append, List.mem_cons] at this hnd' ⊢
      simp only [List.nodup_cons, List.mem_append] at hnd'
      by_cases hji : j = i
      · subst hji
        simp only [hnd'.1, false_iff, not_and, not_not]
        intro _
        simp
      · simp only [hji, false_or] at this
        simpa [hji] using this
    · -- a left endpoint: insert `i`
      have hiT : i ∉ T' := fun h => heP ((hmem i).1 h).1
      have hfalse : (i, false) ∉ P' := fun h => heP (left_mem_of_right_mem (S := S) hE' h)
      simp only [step] at hstep
      split_ifs at hstep
      cases hstep
      have hsplit := List.takeWhile_append_dropWhile (p := (below S · (left S i))) (l := T')
      rw [← hsplit] at hnd hmem hiT
      refine ⟨List.nodup_middle.2 (List.nodup_cons.2 ⟨hiT, hnd⟩), fun j => ?_⟩
      have := hmem j
      simp only [List.mem_append, List.mem_cons] at this ⊢
      by_cases hji : j = i
      · subst hji
        simp [hfalse]
      · simp [hji, this]

/-- **Meeting segments.** Let $K$ be a field with a linear order and $S$ a family of segments in
$K^2$, each given by its two endpoints. Segments $i$ and $j$ of $S$ meet when the closed segment
between the endpoints of $i$ and the closed segment between the endpoints of $j$ have a point in
common. -/
def Meets (S : Fin n → (𝕜 × 𝕜) × (𝕜 × 𝕜)) (i j : Fin n) : Prop :=
  (segment 𝕜 (left S i) (right S i) ∩ segment 𝕜 (left S j) (right S j)).Nonempty

omit [IsStrictOrderedRing 𝕜] in
theorem meets_comm {i j : Fin n} : Meets S i j ↔ Meets S j i := by
  simp only [Meets, Set.inter_comm]

theorem test_ret {i j : Fin n} : (test S i j).ret = true ↔ Meets S i j :=
  segmentsIntersect_ret_eq_true_iff _ _ _ _

/-- **Neighbours on the sweep status are disjoint.** Let $P$ be an initial part of the sorted list
of events. If running the sweep over $P$ from the empty status list reports no intersection and
ends with status list $T$, then no two consecutive segments of $T$ meet. -/
theorem run_isChain {P Q : List (Event n)} (hE : events S = P ++ Q) {T : List (Fin n)}
    (hT : run S P [] = some T) : T.IsChain fun j k => ¬ Meets S j k := by
  induction P using List.reverseRecOn generalizing Q T with
  | nil =>
    simp only [run, Option.some.injEq] at hT
    subst hT
    exact List.IsChain.nil
  | append_singleton P' e ih =>
    rw [run_concat] at hT
    obtain ⟨T', hT', hstep⟩ := Option.bind_eq_some_iff.1 hT
    have hE' : events S = P' ++ e :: Q := by rw [hE]; simp
    have hch := ih hE' hT'
    obtain ⟨i, _ | _⟩ := e
    · have hnodup := nodup_events (S := S)
      rw [hE'] at hnodup
      have heP : (i, false) ∉ P' := fun h => by
        rw [List.nodup_append] at hnodup
        exact hnodup.2.2 _ h _ (by simp) rfl
      have hiP : (i, true) ∈ P' := by
        have := left_mem_of_right_mem (S := S) (j := i) (P := P' ++ [(i, false)]) (Q := Q) hE
          (by simp)
        simpa using this
      have hiT : i ∈ T' := ((run_mem_iff hE' hT').2 i).2 ⟨hiP, heP⟩
      simp only [step] at hstep
      split_ifs at hstep with htest
      cases hstep
      rw [← takeWhile_append_cons_tail_dropWhile hiT] at hch
      obtain ⟨hA, hB, -⟩ := List.isChain_append.1 hch
      refine List.isChain_append.2 ⟨hA, (List.isChain_cons.1 hB).2, fun x hx y hy => ?_⟩
      rw [Option.mem_def] at hx hy
      rw [hx, hy] at htest
      simpa [testPair, test_ret] using htest
    · simp only [step] at hstep
      split_ifs at hstep with htest
      cases hstep
      simp only [Bool.or_eq_true, not_or] at htest
      obtain ⟨h₁, h₂⟩ := htest
      rw [← List.takeWhile_append_dropWhile (p := (below S · (left S i))) (l := T')] at hch
      obtain ⟨hA, hB, -⟩ := List.isChain_append.1 hch
      refine List.isChain_append.2 ⟨hA, List.isChain_cons.2 ⟨fun y hy => ?_, hB⟩,
        fun x hx y hy => ?_⟩
      · rw [Option.mem_def] at hy
        rw [hy] at h₁
        simpa [testOpt, test_ret] using h₁
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        rw [Option.mem_def] at hx
        rw [hx] at h₂
        rw [meets_comm]
        simpa [testOpt, test_ret] using h₂

/-- **Soundness of the any-segments-intersect sweep.** Let $S$ be a family of $n$ segments in
$K^2$, $K$ a linearly ordered field, and split the sorted list of their $2n$ endpoint events as
$P$ followed by $Q$. If running the sweep over $P$ from the empty status list succeeds with status
list $T$, and running it over $Q$ from $T$ reports an intersection, then there are two distinct
indices $i \ne j$ such that segments $i$ and $j$ meet.

In particular, when the sweep over all the events reports an intersection, two distinct segments
meet. -/
theorem exists_meets_of_run_eq_none {P Q : List (Event n)} (hE : events S = P ++ Q)
    {T : List (Fin n)} (hT : run S P [] = some T) (hQ : run S Q T = none) :
    ∃ i j, i ≠ j ∧ Meets S i j := by
  induction Q generalizing P T with
  | nil => simp [run] at hQ
  | cons e Q ih =>
    simp only [run] at hQ
    cases hs : step S e T with
    | some T' =>
      rw [hs] at hQ
      exact ih (P := P ++ [e]) (by simp [hE]) (by rw [run_concat, hT]; exact hs) hQ
    | none =>
      obtain ⟨hnd, hmem⟩ := run_mem_iff hE hT
      have hnodup := nodup_events (S := S)
      rw [hE] at hnodup
      have heP : e ∉ P := fun h => by
        rw [List.nodup_append] at hnodup
        exact hnodup.2.2 e h e (by simp) rfl
      obtain ⟨i, _ | _⟩ := e
      · have hiP : (i, true) ∈ P := by
          have := left_mem_of_right_mem (S := S) (j := i) (P := P ++ [(i, false)]) (Q := Q)
            (by simp [hE]) (by simp)
          simpa using this
        have hiT : i ∈ T := (hmem i).2 ⟨hiP, heP⟩
        simp only [step] at hs
        split_ifs at hs with htest
        rw [← takeWhile_append_cons_tail_dropWhile hiT] at hnd
        cases ha : (T.takeWhile (· != i)).getLast? with
        | none => simp [ha, testPair] at htest
        | some a =>
          cases hb : (T.dropWhile (· != i)).tail.head? with
          | none => simp [ha, hb, testPair] at htest
          | some b =>
            refine ⟨a, b, fun hab => ?_, test_ret.1 (by simpa [ha, hb, testPair] using htest)⟩
            subst hab
            rw [List.nodup_append] at hnd
            exact hnd.2.2 a (List.mem_of_getLast? ha) a
              (List.mem_cons_of_mem _ (List.mem_of_head? hb)) rfl
      · have hiT : i ∉ T := fun h => heP ((hmem i).1 h).1
        simp only [step] at hs
        split_ifs at hs with htest
        simp only [Bool.or_eq_true] at htest
        rcases htest with h | h
        · cases hb : (T.dropWhile (below S · (left S i))).head? with
          | none => simp [hb, testOpt] at h
          | some b =>
            refine ⟨i, b, fun hib => hiT ?_, test_ret.1 (by simpa [hb, testOpt] using h)⟩
            rw [hib]
            exact (List.dropWhile_suffix _).subset (List.mem_of_head? hb)
        · cases hb : (T.takeWhile (below S · (left S i))).getLast? with
          | none => simp [hb, testOpt] at h
          | some b =>
            refine ⟨i, b, fun hib => hiT ?_, test_ret.1 (by simpa [hb, testOpt] using h)⟩
            rw [hib]
            exact (List.takeWhile_prefix _).subset (List.mem_of_getLast? hb)

end Invariants

/-! ## Completeness -/

section Completeness

variable {S} (hv : ∀ i, (left S i).1 < (right S i).1) {px : 𝕜}
  (hmin : ∀ i j z, i ≠ j → z ∈ segment 𝕜 (left S i) (right S i) →
    z ∈ segment 𝕜 (left S j) (right S j) → px ≤ z.1)
include hv hmin

/-- **The sweep order persists before the leftmost intersection.** Let finitely many segments in
the plane over a linearly ordered field be given, where a point $z$ has coordinates $(z_1, z_2)$
and segment $j$ has left endpoint $l_j$ and right endpoint $r_j$ with $(l_j)_1 < (r_j)_1$. Write
$y_j(t)$ for the height at abscissa $t$ of the line through $l_j$ and $r_j$. Let $p_x$ be such
that every point shared by two distinct segments has abscissa at least $p_x$, let
$x \le x' < p_x$, and let $T$ be a list of segments such that $(l_j)_1 \le x$ and
$x' \le (r_j)_1$ for every $j$ in $T$. If $y_j(x) < y_k(x)$ whenever $j$ occurs before $k$ in
$T$, then $y_j(x') < y_k(x')$ whenever $j$ occurs before $k$ in $T$. -/
theorem pairwise_lt_of_pairwise_lt {T : List (Fin n)} {x x' : 𝕜} (hxx : x ≤ x') (hx' : x' < px)
    (hact : ∀ j ∈ T, (left S j).1 ≤ x ∧ x' ≤ (right S j).1)
    (hT : T.Pairwise fun j k => lineY (left S j) (right S j) x < lineY (left S k) (right S k) x) :
    T.Pairwise fun j k => lineY (left S j) (right S j) x' < lineY (left S k) (right S k) x' := by
  rcases hxx.lt_or_eq with hlt | rfl
  · refine hT.imp_of_mem fun {j k} hj hk hjk => ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨z, ⟨hzj, hzk⟩, -, hz, -⟩ := exists_mem_inter_of_cross (hv j) (hv k) hlt
      (hact j hj).1 (hact j hj).2 (hact k hk).1 (hact k hk).2 hjk hcon
    have hne : j ≠ k := fun h => by subst h; exact lt_irrefl _ hjk
    linarith [hmin j k z hne hzj hzk]
  · exact hT

/-- **The sweep order holds weakly at the leftmost intersection.** Let finitely many segments in
the plane over a linearly ordered field be given, where a point $z$ has coordinates $(z_1, z_2)$
and segment $j$ has left endpoint $l_j$ and right endpoint $r_j$ with $(l_j)_1 < (r_j)_1$. Write
$y_j(t)$ for the height at abscissa $t$ of the line through $l_j$ and $r_j$. Let $p_x$ be such
that every point shared by two distinct segments has abscissa at least $p_x$, let $x < p_x$, and
let $T$ be a list of segments such that $(l_j)_1 \le x$ and $p_x \le (r_j)_1$ for every $j$ in
$T$. If $y_j(x) < y_k(x)$ whenever $j$ occurs before $k$ in $T$, then $y_j(p_x) \le y_k(p_x)$
whenever $j$ occurs before $k$ in $T$. -/
theorem pairwise_le_of_pairwise_lt {T : List (Fin n)} {x : 𝕜} (hx : x < px)
    (hact : ∀ j ∈ T, (left S j).1 ≤ x ∧ px ≤ (right S j).1)
    (hT : T.Pairwise fun j k => lineY (left S j) (right S j) x < lineY (left S k) (right S k) x) :
    T.Pairwise fun j k => lineY (left S j) (right S j) px ≤ lineY (left S k) (right S k) px := by
  refine hT.imp_of_mem fun {j k} hj hk hjk => ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨z, ⟨hzj, hzk⟩, -, -, hz⟩ := exists_mem_inter_of_cross (hv j) (hv k) hx
    (hact j hj).1 (hact j hj).2 (hact k hk).1 (hact k hk).2 hjk hcon.le
  have hne : j ≠ k := fun h => by subst h; exact lt_irrefl _ hjk
  linarith [hmin j k z hne hzj hzk, hz hcon]

omit hmin in
theorem below_iff {j : Fin n} (q : 𝕜 × 𝕜) :
    below S j q = true ↔ lineY (left S j) (right S j) q.1 < q.2 := by
  simp only [below, decide_eq_true_eq]
  exact direction_neg_iff (hv j) q

/-- **Phase one: the status list is strictly sorted between the processed and remaining events.**
Fix a number $p_x$ in the field of coordinates. Suppose no segment is vertical (each segment's
left endpoint has smaller $x$-coordinate than its right endpoint) and every point common to two
distinct segments has $x$-coordinate at least $p_x$. Split the sorted list of events as $P$
followed by $Q$, where the endpoint of every event of $P$ has $x$-coordinate less than $p_x$, and
suppose running the sweep over $P$ from the empty status list reports no intersection and ends
with status list $T$. Let $x < p_x$ be at least the $x$-coordinate of the endpoint of every event
of $P$ and at most that of every event of $Q$. Then whenever segment $j$ comes before segment $k$
in $T$, the height at $x$ of the line through the endpoints of $j$ is less than that of the line
through the endpoints of $k$. -/
theorem run_pairwise_lt {P Q : List (Event n)} (hE : events S = P ++ Q)
    (hP : ∀ e ∈ P, (point S e).1 < px) {T : List (Fin n)} (hT : run S P [] = some T) {x : 𝕜}
    (hxP : ∀ e ∈ P, (point S e).1 ≤ x) (hxQ : ∀ e ∈ Q, x ≤ (point S e).1) (hx : x < px) :
    T.Pairwise fun j k => lineY (left S j) (right S j) x < lineY (left S k) (right S k) x := by
  induction P using List.reverseRecOn generalizing Q T x with
  | nil =>
    simp only [run, Option.some.injEq] at hT
    subst hT
    exact List.Pairwise.nil
  | append_singleton P' e ih =>
    have hT₀ := hT
    rw [run_concat] at hT
    obtain ⟨T', hT', hstep⟩ := Option.bind_eq_some_iff.1 hT
    have hE' : events S = P' ++ e :: Q := by rw [hE]; simp
    set xe := (point S e).1 with hxe
    have hle : ∀ e' ∈ P', (point S e').1 ≤ xe := fun e' he' =>
      fst_le_of_key_le (key_le_of_eq_append hE' he' (by simp))
    have hge : ∀ f ∈ e :: Q, xe ≤ (point S f).1 := by
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact le_rfl
      · exact fst_le_of_key_le (key_le_of_eq_append hE (by simp) hf)
    have hsorted' := ih hE' (fun e' he' => hP e' (by simp [he'])) hT' hle hge
      (hP e (by simp))
    obtain ⟨-, hmem'⟩ := run_mem_iff hE' hT'
    obtain ⟨-, hmem⟩ := run_mem_iff hE hT₀
    -- every segment on the new list spans `[xe, x]`
    have hact : ∀ j ∈ T, (left S j).1 ≤ xe ∧ x ≤ (right S j).1 := by
      intro j hj
      obtain ⟨hl, hr⟩ := (hmem j).1 hj
      refine ⟨?_, ?_⟩
      · rcases List.mem_append.1 hl with hl | hl
        · exact hle _ hl
        · rw [List.mem_singleton] at hl
          rw [hxe, ← hl]
          simp [point]
      · have hrE := mem_events (S := S) (j, false)
        rw [hE] at hrE
        rcases List.mem_append.1 hrE with h | h
        · exact absurd h hr
        · exact hxQ _ h
    -- sorted at `xe` after the step
    have hstepsorted : T.Pairwise fun j k =>
        lineY (left S j) (right S j) xe < lineY (left S k) (right S k) xe := by
      obtain ⟨i, _ | _⟩ := e
      · simp only [step] at hstep
        split_ifs at hstep
        cases hstep
        have hnodup := nodup_events (S := S)
        rw [hE'] at hnodup
        have heP : (i, false) ∉ P' := fun h => by
          rw [List.nodup_append] at hnodup
          exact hnodup.2.2 _ h _ (by simp) rfl
        have hiP : (i, true) ∈ P' := by
          have := left_mem_of_right_mem (S := S) (j := i) (P := P' ++ [(i, false)]) (Q := Q) hE
            (by simp)
          simpa using this
        have hiT : i ∈ T' := (hmem' i).2 ⟨hiP, heP⟩
        rw [← takeWhile_append_cons_tail_dropWhile hiT] at hsorted'
        exact hsorted'.sublist ((List.sublist_cons_self _ _).append_left _)
      · simp only [step] at hstep
        split_ifs at hstep
        cases hstep
        have hxi : xe = (left S i).1 := by simp [hxe, point]
        have hiT : i ∉ T' := by
          intro h
          have hnodup := nodup_events (S := S)
          rw [hE', List.nodup_append] at hnodup
          exact hnodup.2.2 _ ((hmem' i).1 h).1 _ (by simp) rfl
        apply pairwise_takeWhile_append_cons_dropWhile_lt (f := fun j =>
          lineY (left S j) (right S j) xe)
        · intro j _
          rw [below_iff hv, hxi, lineY_left]
        · exact hsorted'
        · intro j hj hji
          simp only [hxi, lineY_left] at hji
          obtain ⟨hl, hr⟩ := (hmem' j).1 hj
          have hjl : (left S j).1 ≤ (left S i).1 := by
            have := hle _ hl
            simpa [hxi, point] using this
          have hjr : (left S i).1 ≤ (right S j).1 := by
            have hrE := mem_events (S := S) (j, false)
            rw [hE'] at hrE
            rcases List.mem_append.1 hrE with h | h
            · exact absurd h hr
            · have := hge _ h
              simpa [hxi, point] using this
          have hmemj : left S i ∈ segment 𝕜 (left S j) (right S j) :=
            (mem_segment_iff_lineY (hv j)).2 ⟨hjl, hjr, hji.symm⟩
          have hji' : j ≠ i := fun h => hiT (h ▸ hj)
          have := hmin j i (left S i) hji' hmemj (left_mem_segment 𝕜 _ _)
          have hlt := hP (i, true) (by simp)
          simp only [point, ite_true] at hlt
          linarith
    exact pairwise_lt_of_pairwise_lt hv hmin (hxP e (by simp)) hx hact hstepsorted

/-- **The status list is weakly sorted after the events left of a vertical line.** Fix a number
$p_x$ in the field of coordinates. Suppose no segment is vertical (each segment's left endpoint
has smaller $x$-coordinate than its right endpoint) and every point common to two distinct
segments has $x$-coordinate at least $p_x$. Split the sorted list of events as $P$ followed by
$Q$, where the endpoint of every event of $P$ has $x$-coordinate less than $p_x$ and that of every
event of $Q$ has $x$-coordinate at least $p_x$. If running the sweep over $P$ from the empty
status list reports no intersection and ends with status list $T$, then whenever segment $j$
comes before segment $k$ in $T$, the height at $p_x$ of the line through the endpoints of $j$ is
at most that of the line through the endpoints of $k$. -/
theorem run_pairwise_le_of_lt {P Q : List (Event n)} (hE : events S = P ++ Q)
    (hP : ∀ e ∈ P, (point S e).1 < px) (hQ : ∀ e ∈ Q, px ≤ (point S e).1) {T : List (Fin n)}
    (hT : run S P [] = some T) :
    T.Pairwise fun j k => lineY (left S j) (right S j) px ≤ lineY (left S k) (right S k) px := by
  rcases List.eq_nil_or_concat' P with rfl | ⟨P', e₀, rfl⟩
  · simp only [run, Option.some.injEq] at hT
    subst hT
    exact List.Pairwise.nil
  · have hx₀ := hP e₀ (by simp)
    have hle : ∀ e ∈ P' ++ [e₀], (point S e).1 ≤ (point S e₀).1 := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact fst_le_of_key_le (key_le_of_eq_append (P := P') (Q := e₀ :: Q) (by simp [hE]) he
          (by simp))
      · rw [List.mem_singleton] at he
        rw [he]
    have hsorted := run_pairwise_lt hv hmin hE hP hT hle
      (fun e he => (hx₀.trans_le (hQ e he)).le) hx₀
    obtain ⟨-, hmem⟩ := run_mem_iff hE hT
    refine pairwise_le_of_pairwise_lt hv hmin hx₀ (fun j hj => ⟨?_, ?_⟩) hsorted
    · have := hle _ ((hmem j).1 hj).1
      simpa [point] using this
    · have hrE := mem_events (S := S) (j, false)
      rw [hE] at hrE
      rcases List.mem_append.1 hrE with h | h
      · exact absurd h ((hmem j).1 hj).2
      · simpa [point] using hQ _ h

/-- **Phase two: inserting left endpoints on a vertical line keeps the status weakly sorted.**
Fix a number $p_x$ in the field of coordinates. Suppose no segment is vertical (each segment's
left endpoint has smaller $x$-coordinate than its right endpoint) and every point common to two
distinct segments has $x$-coordinate at least $p_x$. Split the sorted list of events as $P_1$,
then $P_2$, then $Q$, where the endpoint of every event of $P_1$ has $x$-coordinate less than
$p_x$, every event of $P_2$ is a left endpoint with $x$-coordinate equal to $p_x$, and the
endpoint of every event of $Q$ has $x$-coordinate at least $p_x$. If running the sweep over $P_1$
followed by $P_2$ from the empty status list reports no intersection and ends with status list
$T$, then whenever segment $j$ comes before segment $k$ in $T$, the height at $p_x$ of the line
through the endpoints of $j$ is at most that of the line through the endpoints of $k$. -/
theorem run_pairwise_le {P₁ P₂ Q : List (Event n)} (hE : events S = P₁ ++ P₂ ++ Q)
    (hP₁ : ∀ e ∈ P₁, (point S e).1 < px) (hP₂ : ∀ e ∈ P₂, e.2 = true ∧ (point S e).1 = px)
    (hQ : ∀ e ∈ Q, px ≤ (point S e).1) {T : List (Fin n)} (hT : run S (P₁ ++ P₂) [] = some T) :
    T.Pairwise fun j k => lineY (left S j) (right S j) px ≤ lineY (left S k) (right S k) px := by
  induction P₂ using List.reverseRecOn generalizing Q T with
  | nil =>
    rw [List.append_nil] at hE hT
    exact run_pairwise_le_of_lt hv hmin hE hP₁ hQ hT
  | append_singleton P₂' e ih =>
    rw [← List.append_assoc, run_concat] at hT
    obtain ⟨T', hT', hstep⟩ := Option.bind_eq_some_iff.1 hT
    have hsorted' := ih (Q := e :: Q) (by rw [hE]; simp) (fun e' he' => hP₂ e' (by simp [he']))
      (by
        intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact (hP₂ f (by simp)).2.ge
        · exact hQ f hf) hT'
    obtain ⟨i, b⟩ := e
    obtain ⟨hb, hxi⟩ := hP₂ (i, b) (by simp)
    simp only at hb
    subst hb
    simp only [point, ite_true] at hxi
    simp only [step] at hstep
    split_ifs at hstep
    cases hstep
    apply pairwise_takeWhile_append_cons_dropWhile_le (f := fun j =>
      lineY (left S j) (right S j) px)
    · intro j _
      rw [below_iff hv, ← hxi, lineY_left]
    · exact hsorted'

end Completeness

section Cases

variable {S} (hv : ∀ i, (left S i).1 < (right S i).1)
  (h3 : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ z, z ∈ segment 𝕜 (left S i) (right S i) →
    z ∈ segment 𝕜 (left S j) (right S j) → z ∉ segment 𝕜 (left S k) (right S k))
include hv h3

/-- **Sweep completeness when the leftmost intersection is inside both segments.** Let $n$
segments in the plane over a linearly ordered field be given, where $z_1$ is the abscissa of a
point $z$ and segment $i$ has left endpoint $l_i$ and right endpoint $r_i$ with
$(l_i)_1 < (r_i)_1$, and suppose no point lies on three distinct segments. Let $a \ne b$ be
segments that share a point $p$ such that every point shared by two distinct segments has
abscissa at least $p_1$, and suppose $(l_a)_1 < p_1$ and $(l_b)_1 < p_1$. Then the sweep, run on
the sorted list of endpoint events from the empty status list, reports an intersection.

Just before the sweep line reaches $p$, the segments $a$ and $b$ are neighbours on the status
list, so they were tested. -/
theorem run_eq_none_of_lt {a b : Fin n} (hab : a ≠ b) {p : 𝕜 × 𝕜}
    (hpa : p ∈ segment 𝕜 (left S a) (right S a)) (hpb : p ∈ segment 𝕜 (left S b) (right S b))
    (hmin : ∀ i j z, i ≠ j → z ∈ segment 𝕜 (left S i) (right S i) →
      z ∈ segment 𝕜 (left S j) (right S j) → p.1 ≤ z.1)
    (hla : (left S a).1 < p.1) (hlb : (left S b).1 < p.1) : run S (events S) [] = none := by
  set P := (events S).takeWhile fun e => decide ((point S e).1 < p.1) with hPdef
  set Q := (events S).dropWhile fun e => decide ((point S e).1 < p.1) with hQdef
  have hE : events S = P ++ Q := List.takeWhile_append_dropWhile.symm
  have hP : ∀ e ∈ P, (point S e).1 < p.1 := fun e he => by
    simpa using List.mem_takeWhile_imp he
  have hQ : ∀ e ∈ Q, p.1 ≤ (point S e).1 := by
    intro e he
    obtain ⟨q₀, Q', hQ'⟩ : ∃ q₀ Q', Q = q₀ :: Q' := by
      cases h : Q with
      | nil => rw [h] at he; simp at he
      | cons q₀ Q' => exact ⟨q₀, Q', rfl⟩
    have hq₀ : p.1 ≤ (point S q₀).1 := by
      have := List.head_dropWhile_not (fun e => decide ((point S e).1 < p.1)) (l := events S)
        (by rw [← hQdef, hQ']; simp)
      simp only [← hQdef, hQ', List.head_cons, decide_eq_false_iff_not, not_lt] at this
      exact this
    rw [hQ'] at he
    rcases List.mem_cons.1 he with rfl | he
    · exact hq₀
    · exact hq₀.trans (fst_le_of_key_le (key_le_of_eq_append (S := S) (P := P ++ [q₀]) (Q := Q')
        (e := q₀) (by rw [hE, hQ']; simp) (by simp) he))
  rw [hE, run_append]
  cases hT : run S P [] with
  | none => rfl
  | some T =>
    exfalso
    obtain ⟨hnd, hmem⟩ := run_mem_iff hE hT
    have hin : ∀ c, (left S c).1 < p.1 → p ∈ segment 𝕜 (left S c) (right S c) → c ∈ T := by
      intro c hlc hpc
      have hr := ((mem_segment_iff_lineY (hv c)).1 hpc).2.1
      refine (hmem c).2 ⟨?_, fun h => ?_⟩
      · have := mem_events (S := S) (c, true)
        rw [hE] at this
        rcases List.mem_append.1 this with h | h
        · exact h
        · exact absurd (hQ _ h) (by simpa [point] using hlc)
      · exact absurd (hP _ h) (by simpa [point] using hr)
    have haT := hin a hla hpa
    have hbT := hin b hlb hpb
    have hsorted := run_pairwise_le_of_lt hv hmin hE hP hQ hT
    have hch := run_isChain hE hT
    obtain ⟨u, w, A, M, B, huw, hTeq⟩ := exists_append_of_mem_of_mem haT hbT hab
    have hpu : p ∈ segment 𝕜 (left S u) (right S u) := by
      rcases huw with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hpw : p ∈ segment 𝕜 (left S w) (right S w) := by
      rcases huw with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have huw' : u ≠ w := by
      rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
    rw [hTeq] at hch hsorted hnd
    cases M with
    | nil =>
      -- neighbours: they were tested
      simp only [List.nil_append] at hch
      have := (List.isChain_append_cons_cons.1 hch).2.1
      exact this ⟨p, hpu, hpw⟩
    | cons c M =>
      -- a segment between them passes through `p`
      have hcT : c ∈ T := by rw [hTeq]; simp
      rw [List.pairwise_append, List.pairwise_cons] at hsorted
      have huc := hsorted.2.1.1 c (by simp)
      have hcw : lineY (left S c) (right S c) p.1 ≤ lineY (left S w) (right S w) p.1 := by
        have h' := hsorted.2.1.2
        rw [List.cons_append, List.pairwise_cons] at h'
        exact h'.1 w (by simp)
      have hyu := ((mem_segment_iff_lineY (hv u)).1 hpu).2.2
      have hyw := ((mem_segment_iff_lineY (hv w)).1 hpw).2.2
      have hpc : p ∈ segment 𝕜 (left S c) (right S c) := by
        obtain ⟨hl, hr⟩ := (hmem c).1 hcT
        refine (mem_segment_iff_lineY (hv c)).2 ⟨?_, ?_, by linarith⟩
        · have := hP _ hl
          simp only [point, ite_true] at this
          exact this.le
        · have hrE := mem_events (S := S) (c, false)
          rw [hE] at hrE
          rcases List.mem_append.1 hrE with h | h
          · exact absurd h hr
          · simpa [point] using hQ _ h
      rw [List.nodup_append, List.nodup_cons] at hnd
      have hcu : c ≠ u := fun h => hnd.2.1.1 (by simp [h])
      have hcw' : c ≠ w := by
        intro h
        have := hnd.2.1.2
        rw [List.cons_append, List.nodup_cons] at this
        exact this.1 (by simp [h])
      exact h3 u w c huw' (Ne.symm hcw') (Ne.symm hcu) p hpu hpw hpc

/-- **Sweep completeness when the leftmost intersection is a left endpoint.** Let $n$ segments in
the plane over a linearly ordered field be given, where $z_1$ is the abscissa of a point $z$ and
segment $i$ has left endpoint $l_i$ and right endpoint $r_i$ with $(l_i)_1 < (r_i)_1$, and
suppose no point lies on three distinct segments. Let $a \ne b$ be segments such that $l_a$ lies
on segment $b$ and every point shared by two distinct segments has abscissa at least $(l_a)_1$.
If the left endpoint of $b$ comes before the left endpoint of $a$ in the sorted list of endpoint
events, then the sweep, run on that list from the empty status list, reports an intersection.

Inserting $a$ places it right next to $b$, so the two are tested. -/
theorem run_eq_none_of_left {a b : Fin n} (hab : a ≠ b)
    (hpb : left S a ∈ segment 𝕜 (left S b) (right S b))
    (hmin : ∀ i j z, i ≠ j → z ∈ segment 𝕜 (left S i) (right S i) →
      z ∈ segment 𝕜 (left S j) (right S j) → (left S a).1 ≤ z.1)
    {P Q : List (Event n)} (hE : events S = P ++ (a, true) :: Q) (hbP : (b, true) ∈ P) :
    run S (events S) [] = none := by
  set p := left S a with hp
  have hka : key S (a, true) = toLex (p.1, toLex (0, p.2)) := by simp [key, point, hp]
  -- events after `(a, true)` lie on or right of `x = p.1`
  have hQ : ∀ e ∈ (a, true) :: Q, p.1 ≤ (point S e).1 := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · simp [point, hp]
    · have := fst_le_of_key_le (key_le_of_eq_append (S := S) (P := P ++ [(a, true)]) (Q := Q)
        (e := (a, true)) (by simp [hE]) (by simp) he)
      simpa [point, hp] using this
  set P₁ := P.takeWhile fun e => decide ((point S e).1 < p.1) with hP₁def
  set P₂ := P.dropWhile fun e => decide ((point S e).1 < p.1) with hP₂def
  have hPsplit : P = P₁ ++ P₂ := List.takeWhile_append_dropWhile.symm
  have hE' : events S = P₁ ++ P₂ ++ (a, true) :: Q := by rw [hE, ← hPsplit]
  have hP₁ : ∀ e ∈ P₁, (point S e).1 < p.1 := fun e he => by
    simpa using List.mem_takeWhile_imp he
  have hP₂ : ∀ e ∈ P₂, e.2 = true ∧ (point S e).1 = p.1 := by
    intro e he
    have hge : p.1 ≤ (point S e).1 := by
      obtain ⟨q₀, Q', hQ'⟩ : ∃ q₀ Q', P₂ = q₀ :: Q' := by
        cases h : P₂ with
        | nil => rw [h] at he; simp at he
        | cons q₀ Q' => exact ⟨q₀, Q', rfl⟩
      have hq₀ : p.1 ≤ (point S q₀).1 := by
        have := List.head_dropWhile_not (fun e => decide ((point S e).1 < p.1)) (l := P)
          (by rw [← hP₂def, hQ']; simp)
        simp only [← hP₂def, hQ', List.head_cons, decide_eq_false_iff_not, not_lt] at this
        exact this
      rw [hQ'] at he
      rcases List.mem_cons.1 he with rfl | he
      · exact hq₀
      · exact hq₀.trans (fst_le_of_key_le (key_le_of_eq_append (S := S) (P := P₁ ++ [q₀])
          (Q := Q' ++ (a, true) :: Q) (e := q₀) (by rw [hE', hQ']; simp) (by simp)
          (by simp [he])))
    have hle := key_le_of_eq_append (S := S) (P := P₁ ++ P₂) (Q := (a, true) :: Q) (e := e)
      (f := (a, true)) hE' (by simp [he]) (by simp)
    rw [hka] at hle
    simp only [key, Prod.Lex.toLex_le_toLex] at hle
    rcases hle with h | ⟨h, h'⟩
    · exact absurd h (not_lt.2 hge)
    · refine ⟨?_, h⟩
      rcases h' with h' | ⟨h', -⟩
      · split_ifs at h' <;> simp at h'
      · revert h'
        cases e.2 <;> simp
  rw [hE, run_append]
  cases hT : run S P [] with
  | none => rfl
  | some T =>
    simp only [Option.bind_some, run]
    suffices step S (a, true) T = none by rw [this]; rfl
    obtain ⟨hnd, hmem⟩ := run_mem_iff hE hT
    have hsorted := run_pairwise_le hv (px := p.1) hmin hE' hP₁ hP₂ hQ
      (by rw [← hPsplit]; exact hT)
    have hnodup := nodup_events (S := S)
    rw [hE, List.nodup_append] at hnodup
    have haT : a ∉ T := fun h => hnodup.2.2 _ ((hmem a).1 h).1 _ (by simp) rfl
    have hbT : b ∈ T := by
      refine (hmem b).2 ⟨hbP, fun h => ?_⟩
      have hle := key_le_of_eq_append hE h (List.mem_cons_self (a := (a, true)) (l := Q))
      rw [hka] at hle
      have hr := ((mem_segment_iff_lineY (hv b)).1 hpb).2.1
      simp only [key, point, Bool.false_eq_true, ite_false, Prod.Lex.toLex_le_toLex] at hle
      rcases hle with h | ⟨h, h'⟩
      · exact absurd h (not_lt.2 hr)
      · simp at h'
    -- the other segments on the list miss `p`
    have huniq : ∀ c ∈ T, c ≠ b → lineY (left S c) (right S c) p.1 ≠ p.2 := by
      intro c hc hcb hyc
      obtain ⟨hl, hr⟩ := (hmem c).1 hc
      have hpc : p ∈ segment 𝕜 (left S c) (right S c) := by
        refine (mem_segment_iff_lineY (hv c)).2 ⟨?_, ?_, hyc.symm⟩
        · have := fst_le_of_key_le (key_le_of_eq_append hE hl
            (List.mem_cons_self (a := (a, true)) (l := Q)))
          simpa [point, hp] using this
        · have hrE := mem_events (S := S) (c, false)
          rw [hE] at hrE
          rcases List.mem_append.1 hrE with h | h
          · exact absurd h hr
          · simpa [point] using hQ _ h
      have hca : c ≠ a := fun h => haT (h ▸ hc)
      exact h3 a b c hab (Ne.symm hcb) (Ne.symm hca) p (left_mem_segment 𝕜 _ _) hpb hpc
    have hhead : (T.dropWhile (below S · (left S a))).head? = some b := by
      refine head?_dropWhile_eq_of_unique (f := fun j => lineY (left S j) (right S j) p.1)
        (y := p.2) _ (fun j _ => ?_) hsorted hbT
        ((mem_segment_iff_lineY (hv b)).1 hpb).2.2.symm huniq
      exact below_iff hv (j := j) (left S a)
    have hmeet : (test S a b).ret = true := test_ret.2 ⟨p, left_mem_segment 𝕜 _ _, hpb⟩
    simp [step, hhead, testOpt, hmeet]

end Cases

section Main

variable {S} (hv : ∀ i, (left S i).1 < (right S i).1)
include hv

/-- **A leftmost intersection point.** Let $\Bbbk$ be a linearly ordered field, let
$s_0, \dots, s_{n-1}$ be closed segments in $\Bbbk^2$, none of them vertical, and write $z_x$ for
the $x$-coordinate of a point $z$. If some $s_i$ and $s_j$ with $i \ne j$ meet, then there are
indices $a \ne b$ and a point $p \in s_a \cap s_b$ such that $p_x \le z_x$ for all indices
$k \ne l$ and every point $z \in s_k \cap s_l$. -/
theorem exists_leftmost_meet (h : ∃ i j, i ≠ j ∧ Meets S i j) :
    ∃ a b p, a ≠ b ∧ p ∈ segment 𝕜 (left S a) (right S a) ∧
      p ∈ segment 𝕜 (left S b) (right S b) ∧
      ∀ i j z, i ≠ j → z ∈ segment 𝕜 (left S i) (right S i) →
        z ∈ segment 𝕜 (left S j) (right S j) → p.1 ≤ z.1 := by
  classical
  set F := Finset.univ.filter fun ij : Fin n × Fin n => ij.1 ≠ ij.2 ∧ Meets S ij.1 ij.2 with hF
  have hm : ∀ ij ∈ F, ∃ m ∈ segment 𝕜 (left S ij.1) (right S ij.1) ∩
      segment 𝕜 (left S ij.2) (right S ij.2), ∀ w ∈ segment 𝕜 (left S ij.1) (right S ij.1) ∩
        segment 𝕜 (left S ij.2) (right S ij.2), m.1 ≤ w.1 := by
    intro ij hij
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    obtain ⟨z, hz⟩ := hij.2
    exact exists_leftmost_mem_inter (hv _) (hv _) hz
  choose! m hm₁ hm₂ using hm
  obtain ⟨i₀, j₀, hij₀, hmeet⟩ := h
  have hne : F.Nonempty := ⟨(i₀, j₀), by simp [hF, hij₀, hmeet]⟩
  obtain ⟨ab, hab, habmin⟩ := F.exists_min_image (fun ij => (m ij).1) hne
  have hab' := hab
  simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hab'
  refine ⟨ab.1, ab.2, m ab, hab'.1, (hm₁ ab hab).1, (hm₁ ab hab).2,
    fun i j z hij hzi hzj => ?_⟩
  have hijF : (i, j) ∈ F := by
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hij, z, hzi, hzj⟩
  exact (habmin (i, j) hijF).trans (hm₂ (i, j) hijF z ⟨hzi, hzj⟩)

/-- **Completeness of the segment-intersection sweep.** Let $n$ segments in the plane over a
linearly ordered field be given, none of them vertical (the left endpoint of each has strictly
smaller abscissa than its right endpoint), and assume, as CLRS does, that no point lies on three
distinct segments. If two distinct segments meet, then the sweep, run on the sorted list of
endpoint events from the empty status list, reports an intersection. -/
theorem run_eq_none_of_meets
    (h3 : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ z, z ∈ segment 𝕜 (left S i) (right S i) →
      z ∈ segment 𝕜 (left S j) (right S j) → z ∉ segment 𝕜 (left S k) (right S k))
    (h : ∃ i j, i ≠ j ∧ Meets S i j) : run S (events S) [] = none := by
  obtain ⟨a, b, p, hab, hpa, hpb, hmin⟩ := exists_leftmost_meet hv h
  have hla := ((mem_segment_iff_lineY (hv a)).1 hpa).1
  have hlb := ((mem_segment_iff_lineY (hv b)).1 hpb).1
  -- a point of a segment above its left `x` is its left endpoint
  have hleft : ∀ c, p ∈ segment 𝕜 (left S c) (right S c) → (left S c).1 = p.1 → p = left S c := by
    intro c hpc hx
    obtain ⟨-, -, hy⟩ := (mem_segment_iff_lineY (hv c)).1 hpc
    rw [← hx, lineY_left] at hy
    exact Prod.ext hx.symm hy
  -- `p` is the left endpoint of `c`, which meets `d`: take the one inserted second
  have hcase : ∀ c d, c ≠ d → p = left S c → p ∈ segment 𝕜 (left S d) (right S d) →
      run S (events S) [] = none := by
    intro c d hcd hpc hpd
    obtain ⟨P, Q, hE⟩ := List.append_of_mem (mem_events (S := S) (c, true))
    by_cases hdP : (d, true) ∈ P
    · exact run_eq_none_of_left hv h3 hcd (by rw [← hpc]; exact hpd) (by rw [← hpc]; exact hmin)
        hE hdP
    · have hdQ : (d, true) ∈ Q := by
        have := mem_events (S := S) (d, true)
        rw [hE] at this
        rcases List.mem_append.1 this with h | h
        · exact absurd h hdP
        · rcases List.mem_cons.1 h with h | h
          · exact absurd (Prod.mk.inj h).1 (Ne.symm hcd)
          · exact h
      obtain ⟨Q₁, Q₂, rfl⟩ := List.append_of_mem hdQ
      have hle := fst_le_of_key_le (key_le_of_eq_append (S := S) (P := P ++ [(c, true)])
        (Q := Q₁ ++ (d, true) :: Q₂) (e := (c, true)) (f := (d, true)) (by simp [hE]) (by simp)
        (by simp))
      simp only [point, ite_true] at hle
      have hld := ((mem_segment_iff_lineY (hv d)).1 hpd).1
      have hpd' : p = left S d := hleft d hpd (le_antisymm hld (hpc ▸ hle))
      have hdc : left S d ∈ segment 𝕜 (left S c) (right S c) := by
        rw [← hpd', hpc]
        exact left_mem_segment 𝕜 _ _
      exact run_eq_none_of_left hv h3 (Ne.symm hcd) hdc (by rw [← hpd']; exact hmin)
        (P := P ++ (c, true) :: Q₁) (Q := Q₂) (by rw [hE]; simp) (by simp)
  rcases hla.lt_or_eq with hla' | hla'
  · rcases hlb.lt_or_eq with hlb' | hlb'
    · exact run_eq_none_of_lt hv h3 hab hpa hpb hmin hla' hlb'
    · exact hcase b a hab.symm (hleft b hpb hlb') hpa
  · exact hcase a b hab (hleft a hpa hla') hpb

end Main

/-! ## Cost -/

section Cost

variable {S}

omit [IsStrictOrderedRing 𝕜] in
theorem time_test (i j : Fin n) : (test S i j).time ≤ 8 := (segmentsIntersect_time _ _ _ _).2

omit [IsStrictOrderedRing 𝕜] in
theorem time_testOpt (i : Fin n) (o : Option (Fin n)) : (testOpt S i o).time ≤ 8 := by
  cases o <;> simp [testOpt, time_test]

omit [IsStrictOrderedRing 𝕜] in
theorem time_testPair (o o' : Option (Fin n)) : (testPair S o o').time ≤ 8 := by
  rcases o with _ | a <;> rcases o' with _ | b <;> simp [testPair, time_test]

/-- **Cost charged to a sweep event.** For $n$ segments, the charge of an event is $n + 16$ if it
is the left endpoint of a segment and $8$ if it is the right endpoint of a segment.

These charges bound the actual costs: a left endpoint scans at most $n$ segments of the status
list and runs two SEGMENTS-INTERSECT tests, and a right endpoint runs one test. -/
def eventCost (n : ℕ) : Event n → ℕ
  | (_, true) => n + 16
  | (_, false) => 8

omit [IsStrictOrderedRing 𝕜] in
theorem sweep_time_le {P Q : List (Event n)} (hE : events S = P ++ Q) {T : List (Fin n)}
    (hT : run S P [] = some T) : (sweep S Q T).time ≤ (Q.map (eventCost n)).sum := by
  induction Q generalizing P T with
  | nil => simp [sweep]
  | cons e Q ih =>
    obtain ⟨i, _ | _⟩ := e
    · have h₁ := time_testPair (S := S) (T.takeWhile (· != i)).getLast?
        (T.dropWhile (· != i)).tail.head?
      by_cases hb : (testPair S (T.takeWhile (· != i)).getLast?
          (T.dropWhile (· != i)).tail.head?).ret = true
      · simp only [sweep, time_bind, hb, ↓reduceIte, time_pure, List.map_cons, eventCost,
          List.sum_cons]
        omega
      · have := ih (P := P ++ [(i, false)])
          (T := T.takeWhile (· != i) ++ (T.dropWhile (· != i)).tail) (by simp [hE])
          (by rw [run_concat, hT]; simp only [Option.bind_some, step, hb, Bool.false_eq_true,
            ↓reduceIte])
        simp only [sweep, time_bind, hb, Bool.false_eq_true, ↓reduceIte, List.map_cons,
          eventCost, List.sum_cons]
        omega
    · have hlen : T.length ≤ n := by
        simpa using (run_mem_iff hE hT).1.length_le_card
      have h₁ := time_testOpt (S := S) i (T.dropWhile (below S · (left S i))).head?
      have h₂ := time_testOpt (S := S) i (T.takeWhile (below S · (left S i))).getLast?
      have hscan : min ((T.takeWhile (below S · (left S i))).length + 1) T.length ≤ n :=
        (min_le_right _ _).trans hlen
      by_cases hb₁ : (testOpt S i (T.dropWhile (below S · (left S i))).head?).ret = true
      · simp only [sweep, time_bind, time_tick, hb₁, ↓reduceIte, time_pure, List.map_cons,
          eventCost, List.sum_cons]
        refine le_trans (Nat.add_le_add hscan le_rfl) ?_
        omega
      · by_cases hb₂ : (testOpt S i (T.takeWhile (below S · (left S i))).getLast?).ret = true
        · simp only [sweep, time_bind, time_tick, hb₁, hb₂, Bool.false_eq_true, ↓reduceIte,
            time_pure, List.map_cons, eventCost, List.sum_cons]
          refine le_trans (Nat.add_le_add hscan le_rfl) ?_
          omega
        · have := ih (P := P ++ [(i, true)])
            (T := T.takeWhile (below S · (left S i)) ++ i :: T.dropWhile (below S · (left S i)))
            (by simp [hE])
            (by
              rw [run_concat, hT]
              simp only [Option.bind_some, step, hb₁, hb₂, Bool.or_false, Bool.false_eq_true,
                ↓reduceIte])
          simp only [sweep, time_bind, time_tick, hb₁, hb₂, Bool.false_eq_true, ↓reduceIte,
            List.map_cons, eventCost, List.sum_cons]
          refine le_trans (Nat.add_le_add hscan le_rfl) ?_
          omega

end Cost

end AnySegments

/-- **ANY-SEGMENTS-INTERSECT.** Let $\Bbbk$ be a linearly ordered field. Given $n$ segments
$s_0, \dots, s_{n-1}$ in $\Bbbk^2$, each given by its two endpoints, write $l_t$, the left endpoint
of $s_t$, for its endpoint with the smaller $x$-coordinate, or for its first given endpoint when
both $x$-coordinates agree, and $r_t$, the right endpoint, for the other one. The procedure sorts
the $2n$ endpoints by $x$-coordinate, left endpoints before right endpoints at equal $x$, then by
$y$-coordinate, with remaining ties in increasing order of segment index. It then sweeps a
vertical line across them, starting with an empty status list of segments, kept from bottom to
top. At the left endpoint $l_i$ of $s_i$, let $P$ be the longest initial part of the status list
consisting of segments $s_t$ with $\mathrm{DIRECTION}(l_t, r_t, l_i) < 0$. Then $s_i$ is tested
with SEGMENTS-INTERSECT first against the segment just after $P$ and then against the last
segment of $P$, when these exist, and is inserted directly after $P$. At the right endpoint of
$s_i$, the segments just before and just after $s_i$ in the status list, when both exist, are
tested against each other and $s_i$ is deleted. The procedure returns true as soon as a test
succeeds and false after the last event. Cost counts one unit per evaluation of DIRECTION or
ON-SEGMENT (CLRS, third edition, Section 33.2).

The status is kept in a list rather than CLRS's red-black tree. -/
def anySegmentsIntersect {n : ℕ} (S : Fin n → (𝕜 × 𝕜) × (𝕜 × 𝕜)) : TimeM ℕ Bool :=
  AnySegments.sweep S (AnySegments.events S) []

open AnySegments in
/-- **Correctness of ANY-SEGMENTS-INTERSECT.** Let $\Bbbk$ be a linearly ordered field and let
$s_0, \dots, s_{n-1}$ be closed segments in $\Bbbk^2$, each given by its two endpoints in either
order. Suppose no segment is vertical (its two endpoints have different $x$-coordinates) and no
point lies on three segments $s_i$, $s_j$, $s_k$ with $i$, $j$, $k$ pairwise distinct. Then
ANY-SEGMENTS-INTERSECT returns true on these segments if and only if there are indices $i \ne j$
such that $s_i$ and $s_j$ intersect (CLRS, third edition, Theorem 33.1). -/
theorem anySegmentsIntersect_ret_eq_true_iff {n : ℕ} (S : Fin n → (𝕜 × 𝕜) × (𝕜 × 𝕜))
    (hv : ∀ i, (S i).1.1 ≠ (S i).2.1)
    (h3 : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      segment 𝕜 (S i).1 (S i).2 ∩ segment 𝕜 (S j).1 (S j).2 ∩ segment 𝕜 (S k).1 (S k).2 = ∅) :
    (anySegmentsIntersect S).ret = true ↔
      ∃ i j, i ≠ j ∧ (segment 𝕜 (S i).1 (S i).2 ∩ segment 𝕜 (S j).1 (S j).2).Nonempty := by
  have hv' : ∀ i, (left S i).1 < (right S i).1 := fun i => left_fst_lt (hv i)
  have hseg := segment_left_right (S := S)
  have h3' : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ z, z ∈ segment 𝕜 (left S i) (right S i) →
      z ∈ segment 𝕜 (left S j) (right S j) → z ∉ segment 𝕜 (left S k) (right S k) := by
    intro i j k hij hjk hik z hi hj hk
    rw [hseg] at hi hj hk
    exact (Set.eq_empty_iff_forall_notMem.1 (h3 i j k hij hjk hik)) z ⟨⟨hi, hj⟩, hk⟩
  rw [anySegmentsIntersect, sweep_ret, Option.isNone_iff_eq_none]
  constructor
  · intro h
    obtain ⟨i, j, hij, hm⟩ := exists_meets_of_run_eq_none (P := []) (Q := events S) rfl rfl h
    exact ⟨i, j, hij, by simpa [Meets, hseg] using hm⟩
  · rintro ⟨i, j, hij, hm⟩
    exact run_eq_none_of_meets hv' h3' ⟨i, j, hij, by simpa [Meets, hseg] using hm⟩

omit [IsStrictOrderedRing 𝕜] in
open AnySegments in
/-- **Running time of ANY-SEGMENTS-INTERSECT.** Let $\Bbbk$ be a field with a linear order. For
every $n$ segments in $\Bbbk^2$, each given by its two endpoints, ANY-SEGMENTS-INTERSECT costs at
most $n^2 + 24n$, so it runs in time $O(n^2)$. Cost counts one unit per evaluation of DIRECTION
or ON-SEGMENT.

The bound comes from at most $n$ DIRECTION evaluations to place each segment in the list-based
status and at most three SEGMENTS-INTERSECT tests per segment. -/
theorem anySegmentsIntersect_time_le {n : ℕ} (S : Fin n → (𝕜 × 𝕜) × (𝕜 × 𝕜)) :
    (anySegmentsIntersect S).time ≤ n * n + 24 * n := by
  have h := sweep_time_le (S := S) (P := []) (Q := events S) rfl rfl
  rw [events, ((List.mergeSort_perm _ _).map _).sum_eq] at h
  simp only [List.map_append, List.map_map, Function.comp_def, eventCost, List.sum_append,
    List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul] at h
  rw [anySegmentsIntersect, events]
  nlinarith

end Cslib.Algorithms.Lean.Geometry
