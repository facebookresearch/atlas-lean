/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Orientation and segment intersection

`DIRECTION`, `ON-SEGMENT` and `SEGMENTS-INTERSECT` from CLRS, third edition, Section 33.1. The
cross product `p × q = x_p y_q - x_q y_p` decides on which side of a directed line a point lies;
two closed segments intersect exactly when each straddles the line through the other, or an
endpoint of one is collinear with the other and inside its bounding box.

Points are pairs over a linearly ordered field (`ℚ` for execution, `ℝ`), and segments are
Mathlib's `segment 𝕜 p q`. The main theorem, `segmentsIntersect_ret_eq_true_iff`, says the test
returns `true` exactly when `segment 𝕜 p₁ p₂ ∩ segment 𝕜 p₃ p₄` is nonempty, including all
degenerate cases (collinear overlapping or disjoint segments, touching endpoints, segments that
are single points).

## Cost model

One unit per `DIRECTION` (a cross product) and one per `ON-SEGMENT` test executed. Comparisons of
the directions with `0` and control flow are free. A test costs between `4` and `8`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

open Cslib.Algorithms.Lean TimeM

universe u

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The cross product `p × q = x_p y_q - x_q y_p` (CLRS equation (33.1)). -/
def cross (p q : 𝕜 × 𝕜) : 𝕜 := p.1 * q.2 - q.1 * p.2

/-- CLRS `DIRECTION(pᵢ, pⱼ, pₖ) = (pₖ - pᵢ) × (pⱼ - pᵢ)`: positive when `pₖ` is clockwise from
`pⱼ` about `pᵢ`, negative when counterclockwise, zero when the three points are collinear. -/
def direction (pi pj pk : 𝕜 × 𝕜) : 𝕜 := cross (pk - pi) (pj - pi)

/-- CLRS `ON-SEGMENT(pᵢ, pⱼ, pₖ)`: `pₖ` lies in the bounding box of `pᵢ` and `pⱼ`. -/
def onSegment (pi pj pk : 𝕜 × 𝕜) : Bool :=
  decide (min pi.1 pj.1 ≤ pk.1 ∧ pk.1 ≤ max pi.1 pj.1 ∧
    min pi.2 pj.2 ≤ pk.2 ∧ pk.2 ≤ max pi.2 pj.2)

/-- `d` and `e` are nonzero with opposite signs. -/
def Straddles (d e : 𝕜) : Prop := 0 < d ∧ e < 0 ∨ d < 0 ∧ 0 < e

instance (d e : 𝕜) : Decidable (Straddles d e) := by unfold Straddles; infer_instance

/-- One collinear-endpoint branch of `SEGMENTS-INTERSECT`: `ON-SEGMENT` runs only when the
direction is zero. -/
def collinearBranch (d : 𝕜) (pi pj pk : 𝕜 × 𝕜) : TimeM ℕ Bool :=
  if d = 0 then do
    ✓
    pure (onSegment pi pj pk)
  else pure false

/-- CLRS `SEGMENTS-INTERSECT(p₁, p₂, p₃, p₄)`: whether segment `p₁p₂` meets segment `p₃p₄`. -/
def segmentsIntersect (p1 p2 p3 p4 : 𝕜 × 𝕜) : TimeM ℕ Bool := do
  ✓[4]
  let d1 := direction p3 p4 p1
  let d2 := direction p3 p4 p2
  let d3 := direction p1 p2 p3
  let d4 := direction p1 p2 p4
  if Straddles d1 d2 ∧ Straddles d3 d4 then pure true
  else do
    let b1 ← collinearBranch d1 p3 p4 p1
    if b1 then pure true else do
    let b2 ← collinearBranch d2 p3 p4 p2
    if b2 then pure true else do
    let b3 ← collinearBranch d3 p1 p2 p3
    if b3 then pure true else
    collinearBranch d4 p1 p2 p4

/-! ## Cost -/

omit [IsStrictOrderedRing 𝕜] in
theorem collinearBranch_time_le (d : 𝕜) (pi pj pk : 𝕜 × 𝕜) :
    (collinearBranch d pi pj pk).time ≤ 1 := by
  unfold collinearBranch
  split_ifs <;> simp

omit [IsStrictOrderedRing 𝕜] in
/-- Four directions and at most four `ON-SEGMENT` tests. -/
theorem segmentsIntersect_time (p1 p2 p3 p4 : 𝕜 × 𝕜) :
    4 ≤ (segmentsIntersect p1 p2 p3 p4).time ∧ (segmentsIntersect p1 p2 p3 p4).time ≤ 8 := by
  have h1 := collinearBranch_time_le (direction p3 p4 p1) p3 p4 p1
  have h2 := collinearBranch_time_le (direction p3 p4 p2) p3 p4 p2
  have h3 := collinearBranch_time_le (direction p1 p2 p3) p1 p2 p3
  have h4 := collinearBranch_time_le (direction p1 p2 p4) p1 p2 p4
  simp only [segmentsIntersect, time_bind, time_tick]
  generalize collinearBranch (direction p3 p4 p1) p3 p4 p1 = c1 at *
  generalize collinearBranch (direction p3 p4 p2) p3 p4 p2 = c2 at *
  generalize collinearBranch (direction p1 p2 p3) p1 p2 p3 = c3 at *
  generalize collinearBranch (direction p1 p2 p4) p1 p2 p4 = c4 at *
  obtain ⟨r1, t1⟩ := c1
  obtain ⟨r2, t2⟩ := c2
  obtain ⟨r3, t3⟩ := c3
  obtain ⟨r4, t4⟩ := c4
  simp only at h1 h2 h3 h4
  split_ifs <;> cases r1 <;> cases r2 <;> cases r3 <;> simp <;> omega

/-! ## Geometry of the tests -/

omit [IsStrictOrderedRing 𝕜] in
theorem collinearBranch_ret (d : 𝕜) (pi pj pk : 𝕜 × 𝕜) :
    (collinearBranch d pi pj pk).ret = (decide (d = 0) && onSegment pi pj pk) := by
  unfold collinearBranch
  split_ifs with h <;> simp [h]

omit [IsStrictOrderedRing 𝕜] in
/-- The test as a Boolean formula. -/
theorem segmentsIntersect_ret (p1 p2 p3 p4 : 𝕜 × 𝕜) :
    (segmentsIntersect p1 p2 p3 p4).ret =
      (decide (Straddles (direction p3 p4 p1) (direction p3 p4 p2) ∧
          Straddles (direction p1 p2 p3) (direction p1 p2 p4)) ||
        (decide (direction p3 p4 p1 = 0) && onSegment p3 p4 p1) ||
        (decide (direction p3 p4 p2 = 0) && onSegment p3 p4 p2) ||
        (decide (direction p1 p2 p3 = 0) && onSegment p1 p2 p3) ||
        (decide (direction p1 p2 p4 = 0) && onSegment p1 p2 p4)) := by
  simp only [segmentsIntersect, ret_bind]
  split_ifs with h
  · simp [h]
  · simp only [ret_bind, collinearBranch_ret]
    by_cases b1 : (decide (direction p3 p4 p1 = 0) && onSegment p3 p4 p1) = true
    · simp [b1]
    · simp only [b1, Bool.false_eq_true, ite_false, ret_bind, collinearBranch_ret]
      by_cases b2 : (decide (direction p3 p4 p2 = 0) && onSegment p3 p4 p2) = true
      · simp [b2]
      · simp only [b2, Bool.false_eq_true, ite_false, ret_bind, collinearBranch_ret]
        by_cases b3 : (decide (direction p1 p2 p3 = 0) && onSegment p1 p2 p3) = true
        · simp [b3]
        · simp only [Bool.not_eq_true] at b1 b2 b3
          simp only [b3, decide_eq_false h, Bool.false_eq_true, ite_false, collinearBranch_ret,
            Bool.false_or]

omit [IsStrictOrderedRing 𝕜] in
private theorem mem_segment_coords {p q r : 𝕜 × 𝕜} :
    r ∈ segment 𝕜 p q ↔ ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
      a * p.1 + b * q.1 = r.1 ∧ a * p.2 + b * q.2 = r.2 := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact ⟨a, b, ha, hb, hab, by simp, by simp⟩
  · rintro ⟨a, b, ha, hb, hab, h1, h2⟩
    exact ⟨a, b, ha, hb, hab, Prod.ext (by simpa using h1) (by simpa using h2)⟩

/-- `r = p + λ (q - p)` with `0 ≤ λ ≤ 1` lies on the segment. -/
private theorem mem_segment_of_param {p q r : 𝕜 × 𝕜} (l : 𝕜) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (h1 : r.1 = p.1 + l * (q.1 - p.1)) (h2 : r.2 = p.2 + l * (q.2 - p.2)) :
    r ∈ segment 𝕜 p q :=
  mem_segment_coords.2 ⟨1 - l, l, by linarith, hl0, by ring, by rw [h1]; ring, by rw [h2]; ring⟩

/-- Points of a segment are in its bounding box. -/
theorem onSegment_of_mem {p q r : 𝕜 × 𝕜} (h : r ∈ segment 𝕜 p q) : onSegment p q r = true := by
  obtain ⟨a, b, ha, hb, hab, h1, h2⟩ := mem_segment_coords.1 h
  have key : ∀ x y z : 𝕜, a * x + b * y = z → min x y ≤ z ∧ z ≤ max x y := by
    intro x y z hz
    subst hz
    constructor
    · calc min x y = a * min x y + b * min x y := by rw [← add_mul, hab, one_mul]
        _ ≤ a * x + b * y := add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)
    · calc a * x + b * y ≤ a * max x y + b * max x y :=
            add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
              (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
        _ = max x y := by rw [← add_mul, hab, one_mul]
  obtain ⟨hx1, hx2⟩ := key _ _ _ h1
  obtain ⟨hy1, hy2⟩ := key _ _ _ h2
  simp [onSegment, hx1, hx2, hy1, hy2]

/-- Points of a segment are collinear with its endpoints. -/
theorem direction_eq_zero_of_mem {p q r : 𝕜 × 𝕜} (h : r ∈ segment 𝕜 p q) :
    direction p q r = 0 := by
  obtain ⟨a, b, ha, hb, hab, h1, h2⟩ := mem_segment_coords.1 h
  have ha' : a = 1 - b := by linarith
  simp only [direction, cross, Prod.fst_sub, Prod.snd_sub, ← h1, ← h2, ha']
  ring

/-- CLRS's use of `ON-SEGMENT`: a point collinear with `p` and `q` and inside their bounding box
lies on the segment. -/
theorem mem_segment_of_direction_eq_zero {p q r : 𝕜 × 𝕜} (hd : direction p q r = 0)
    (hb : onSegment p q r = true) : r ∈ segment 𝕜 p q := by
  simp only [onSegment, decide_eq_true_eq] at hb
  obtain ⟨hx1, hx2, hy1, hy2⟩ := hb
  simp only [direction, cross, Prod.fst_sub, Prod.snd_sub] at hd
  rcases lt_trichotomy p.1 q.1 with hx | hx | hx
  · -- parameter from the x coordinate
    rw [min_eq_left hx.le] at hx1
    rw [max_eq_right hx.le] at hx2
    have hv : q.1 - p.1 ≠ 0 := sub_ne_zero.2 hx.ne'
    refine mem_segment_of_param ((r.1 - p.1) / (q.1 - p.1))
      (div_nonneg (by linarith) (by linarith)) ((div_le_one (by linarith)).2 (by linarith))
      (by rw [div_mul_cancel₀ _ hv]; ring) ?_
    have : r.2 - p.2 = (r.1 - p.1) / (q.1 - p.1) * (q.2 - p.2) := by
      rw [div_mul_eq_mul_div, eq_div_iff hv]
      linear_combination (-1 : 𝕜) * hd
    linarith
  · rcases lt_trichotomy p.2 q.2 with hy | hy | hy
    · rw [min_eq_left hy.le] at hy1
      rw [max_eq_right hy.le] at hy2
      have hv : q.2 - p.2 ≠ 0 := sub_ne_zero.2 hy.ne'
      have hr1 : r.1 = p.1 := by
        rw [← hx, min_self] at hx1; rw [← hx, max_self] at hx2; linarith
      refine mem_segment_of_param ((r.2 - p.2) / (q.2 - p.2))
        (div_nonneg (by linarith) (by linarith)) ((div_le_one (by linarith)).2 (by linarith))
        (by rw [hr1, ← hx]; ring) (by rw [div_mul_cancel₀ _ hv]; ring)
    · have hr1 : r.1 = p.1 := by
        rw [← hx, min_self] at hx1; rw [← hx, max_self] at hx2; linarith
      have hr2 : r.2 = p.2 := by
        rw [← hy, min_self] at hy1; rw [← hy, max_self] at hy2; linarith
      exact mem_segment_of_param 0 le_rfl zero_le_one (by rw [hr1]; ring) (by rw [hr2]; ring)
    · rw [min_eq_right hy.le] at hy1
      rw [max_eq_left hy.le] at hy2
      have hv : q.2 - p.2 ≠ 0 := sub_ne_zero.2 hy.ne
      have hr1 : r.1 = p.1 := by
        rw [← hx, min_self] at hx1; rw [← hx, max_self] at hx2; linarith
      refine mem_segment_of_param ((r.2 - p.2) / (q.2 - p.2))
        (div_nonneg_of_nonpos (by linarith) (by linarith))
        ((div_le_one_of_neg (by linarith)).2 (by linarith))
        (by rw [hr1, ← hx]; ring) (by rw [div_mul_cancel₀ _ hv]; ring)
  · rw [min_eq_right hx.le] at hx1
    rw [max_eq_left hx.le] at hx2
    have hv : q.1 - p.1 ≠ 0 := sub_ne_zero.2 hx.ne
    refine mem_segment_of_param ((r.1 - p.1) / (q.1 - p.1))
      (div_nonneg_of_nonpos (by linarith) (by linarith))
      ((div_le_one_of_neg (by linarith)).2 (by linarith)) (by rw [div_mul_cancel₀ _ hv]; ring) ?_
    have : r.2 - p.2 = (r.1 - p.1) / (q.1 - p.1) * (q.2 - p.2) := by
      rw [div_mul_eq_mul_div, eq_div_iff hv]
      linear_combination (-1 : 𝕜) * hd
    linarith

/-! ## Straddling -/

theorem Straddles.sub_ne_zero {d e : 𝕜} (h : Straddles d e) : d - e ≠ 0 := by
  rcases h with ⟨hd, he⟩ | ⟨hd, he⟩ <;> intro h0 <;> linarith [sub_eq_zero.1 h0]

/-- Where the sign changes between `d` and `e`: `d / (d - e) ∈ [0, 1]`. -/
theorem Straddles.param_mem {d e : 𝕜} (h : Straddles d e) : 0 ≤ d / (d - e) ∧ d / (d - e) ≤ 1 := by
  rcases h with ⟨hd, he⟩ | ⟨hd, he⟩
  · exact ⟨div_nonneg hd.le (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩
  · exact ⟨div_nonneg_of_nonpos hd.le (by linarith),
      (div_le_one_of_neg (by linarith)).2 (by linarith)⟩

private theorem combo_pos {a b d e : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hd : 0 < d)
    (he : 0 < e) : 0 < a * d + b * e := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    linarith
  · nlinarith [mul_pos ha' hd, mul_nonneg hb he.le]

/-- Two nonzero values whose convex combination vanishes have opposite signs. -/
theorem straddles_of_combo {a b d e : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hd : d ≠ 0) (he : e ≠ 0) (h : a * d + b * e = 0) : Straddles d e := by
  rcases lt_or_gt_of_ne hd with hd | hd <;> rcases lt_or_gt_of_ne he with he | he
  · have := combo_pos ha hb hab (neg_pos.2 hd) (neg_pos.2 he)
    linarith
  · exact Or.inr ⟨hd, he⟩
  · exact Or.inl ⟨hd, he⟩
  · have := combo_pos ha hb hab hd he
    linarith

/-- Proper crossing: if each segment straddles the line through the other, they meet. -/
theorem inter_nonempty_of_straddles {p1 p2 p3 p4 : 𝕜 × 𝕜}
    (h12 : Straddles (direction p3 p4 p1) (direction p3 p4 p2))
    (h34 : Straddles (direction p1 p2 p3) (direction p1 p2 p4)) :
    (segment 𝕜 p1 p2 ∩ segment 𝕜 p3 p4).Nonempty := by
  obtain ⟨ht0, ht1⟩ := h12.param_mem
  obtain ⟨hs0, hs1⟩ := h34.param_mem
  have hne34 := h34.sub_ne_zero
  -- both parameters have denominator `±(p₂ - p₁) × (p₄ - p₃)`
  have hAB : direction p3 p4 p1 - direction p3 p4 p2 =
      -(direction p1 p2 p3 - direction p1 p2 p4) := by
    simp only [direction, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  refine ⟨(p1.1 + direction p3 p4 p1 / (direction p3 p4 p1 - direction p3 p4 p2) * (p2.1 - p1.1),
      p1.2 + direction p3 p4 p1 / (direction p3 p4 p1 - direction p3 p4 p2) * (p2.2 - p1.2)),
    mem_segment_of_param _ ht0 ht1 rfl rfl, mem_segment_of_param _ hs0 hs1 ?_ ?_⟩ <;>
  · rw [hAB]
    generalize hB : direction p1 p2 p3 - direction p1 p2 p4 = B at hne34 ⊢
    field_simp
    subst hB
    simp only [direction, cross, Prod.fst_sub, Prod.snd_sub]
    ring

/-! ## Completeness -/

/-- Points on the line through `p` and `q ≠ p` are `p + μ (q - p)`, with `μ` given by a dot
product. -/
theorem eq_param_of_direction_eq_zero {p q r : 𝕜 × 𝕜} (hpq : p ≠ q) (hd : direction p q r = 0) :
    ∃ μ : 𝕜, r.1 = p.1 + μ * (q.1 - p.1) ∧ r.2 = p.2 + μ * (q.2 - p.2) := by
  have hN : (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 ≠ 0 := by
    intro h0
    apply hpq
    have h1 : q.1 - p.1 = 0 := by nlinarith [sq_nonneg (q.1 - p.1), sq_nonneg (q.2 - p.2)]
    have h2 : q.2 - p.2 = 0 := by nlinarith [sq_nonneg (q.1 - p.1), sq_nonneg (q.2 - p.2)]
    exact Prod.ext (by linarith) (by linarith)
  simp only [direction, cross, Prod.fst_sub, Prod.snd_sub] at hd
  refine ⟨((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) /
    ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2), ?_, ?_⟩
  · field_simp
    linear_combination (q.2 - p.2) * hd
  · field_simp
    linear_combination (p.1 - q.1) * hd

/-- Collinear case: if `p₁` and `p₂` lie on the line through `p₃p₄` and the segments meet, some
endpoint lies on the other segment. -/
theorem endpoint_mem_of_collinear {p1 p2 p3 p4 z : 𝕜 × 𝕜} (h1 : direction p3 p4 p1 = 0)
    (h2 : direction p3 p4 p2 = 0) (hA : z ∈ segment 𝕜 p1 p2) (hB : z ∈ segment 𝕜 p3 p4) :
    p1 ∈ segment 𝕜 p3 p4 ∨ p2 ∈ segment 𝕜 p3 p4 ∨ p3 ∈ segment 𝕜 p1 p2 ∨
      p4 ∈ segment 𝕜 p1 p2 := by
  by_cases h34 : p3 = p4
  · subst h34
    rw [segment_same, Set.mem_singleton_iff] at hB
    subst hB
    exact Or.inr (Or.inr (Or.inl hA))
  obtain ⟨μ1, hμ1x, hμ1y⟩ := eq_param_of_direction_eq_zero h34 h1
  obtain ⟨μ2, hμ2x, hμ2y⟩ := eq_param_of_direction_eq_zero h34 h2
  obtain ⟨a, b, ha, hb, hab, hzx, hzy⟩ := mem_segment_coords.1 hA
  obtain ⟨a', b', ha', hb', hab', hzx', hzy'⟩ := mem_segment_coords.1 hB
  -- the parameter of `z` along `p₃p₄`, computed two ways
  have hc : a * μ1 + b * μ2 = b' := by
    have ex : (a * μ1 + b * μ2 - b') * (p4.1 - p3.1) = 0 := by
      obtain rfl : a = 1 - b := by linarith
      obtain rfl : a' = 1 - b' := by linarith
      linear_combination hzx - hzx' - (1 - b) * hμ1x - b * hμ2x
    have ey : (a * μ1 + b * μ2 - b') * (p4.2 - p3.2) = 0 := by
      obtain rfl : a = 1 - b := by linarith
      obtain rfl : a' = 1 - b' := by linarith
      linear_combination hzy - hzy' - (1 - b) * hμ1y - b * hμ2y
    by_cases hv : p4.1 - p3.1 = 0 ∧ p4.2 - p3.2 = 0
    · exact absurd (Prod.ext (by linarith [hv.1]) (by linarith [hv.2])) h34
    · rw [not_and_or] at hv
      rcases hv with hv | hv
      · linarith [(mul_eq_zero.1 ex).resolve_right hv]
      · linarith [(mul_eq_zero.1 ey).resolve_right hv]
  by_cases hμ1 : 0 ≤ μ1 ∧ μ1 ≤ 1
  · exact Or.inl (mem_segment_of_param μ1 hμ1.1 hμ1.2 hμ1x hμ1y)
  by_cases hμ2 : 0 ≤ μ2 ∧ μ2 ≤ 1
  · exact Or.inr (Or.inl (mem_segment_of_param μ2 hμ2.1 hμ2.2 hμ2x hμ2y))
  -- `μ₁` and `μ₂` are on opposite sides of `[0, 1]`, so `p₃` (at `μ = 0`) is between them
  have hst : Straddles μ1 μ2 := by
    rw [not_and_or, not_le, not_le] at hμ1 hμ2
    rcases hμ1 with h1' | h1' <;> rcases hμ2 with h2' | h2'
    · have := combo_pos ha hb hab (neg_pos.2 h1') (neg_pos.2 h2')
      linarith
    · exact Or.inr ⟨h1', by linarith⟩
    · exact Or.inl ⟨by linarith, h2'⟩
    · have := combo_pos ha hb hab (sub_pos.2 h1') (sub_pos.2 h2')
      linarith
  obtain ⟨ht0, ht1⟩ := hst.param_mem
  have hne := hst.sub_ne_zero
  refine Or.inr (Or.inr (Or.inl (mem_segment_of_param _ ht0 ht1 ?_ ?_)))
  · rw [hμ1x, hμ2x]; field_simp; ring
  · rw [hμ1y, hμ2y]; field_simp; ring

/-- If the segments meet, either they cross properly or an endpoint of one lies on the other. -/
theorem straddles_or_endpoint_mem {p1 p2 p3 p4 z : 𝕜 × 𝕜} (hA : z ∈ segment 𝕜 p1 p2)
    (hB : z ∈ segment 𝕜 p3 p4) :
    (Straddles (direction p3 p4 p1) (direction p3 p4 p2) ∧
        Straddles (direction p1 p2 p3) (direction p1 p2 p4)) ∨
      p1 ∈ segment 𝕜 p3 p4 ∨ p2 ∈ segment 𝕜 p3 p4 ∨ p3 ∈ segment 𝕜 p1 p2 ∨
        p4 ∈ segment 𝕜 p1 p2 := by
  obtain ⟨a, b, ha, hb, hab, hzx, hzy⟩ := mem_segment_coords.1 hA
  obtain ⟨a', b', ha', hb', hab', hzx', hzy'⟩ := mem_segment_coords.1 hB
  -- the orientation with respect to each line, interpolated along the other segment
  have e12 : a * direction p3 p4 p1 + b * direction p3 p4 p2 = 0 := by
    simp only [direction, cross, Prod.fst_sub, Prod.snd_sub]
    obtain rfl : a = 1 - b := by linarith
    obtain rfl : a' = 1 - b' := by linarith
    linear_combination (p4.2 - p3.2) * (hzx - hzx') - (p4.1 - p3.1) * (hzy - hzy')
  have e34 : a' * direction p1 p2 p3 + b' * direction p1 p2 p4 = 0 := by
    simp only [direction, cross, Prod.fst_sub, Prod.snd_sub]
    obtain rfl : a = 1 - b := by linarith
    obtain rfl : a' = 1 - b' := by linarith
    linear_combination (p2.2 - p1.2) * (hzx' - hzx) - (p2.1 - p1.1) * (hzy' - hzy)
  have hzeq : ∀ w : 𝕜 × 𝕜, w.1 = z.1 → w.2 = z.2 → w = z := fun w h1 h2 => Prod.ext h1 h2
  by_cases d1 : direction p3 p4 p1 = 0 <;> by_cases d2 : direction p3 p4 p2 = 0
  · exact Or.inr (endpoint_mem_of_collinear d1 d2 hA hB)
  · -- `z = p₁`
    rw [d1, mul_zero, zero_add] at e12
    have hb0 : b = 0 := (mul_eq_zero.1 e12).resolve_right d2
    have ha1 : a = 1 := by linarith
    subst hb0 ha1
    refine Or.inr (Or.inl ?_)
    rw [hzeq p1 (by linarith) (by linarith)]
    exact hB
  · -- `z = p₂`
    rw [d2, mul_zero, add_zero] at e12
    have ha0 : a = 0 := (mul_eq_zero.1 e12).resolve_right d1
    have hb1 : b = 1 := by linarith
    subst ha0 hb1
    refine Or.inr (Or.inr (Or.inl ?_))
    rw [hzeq p2 (by linarith) (by linarith)]
    exact hB
  · by_cases d3 : direction p1 p2 p3 = 0 <;> by_cases d4 : direction p1 p2 p4 = 0
    · rcases endpoint_mem_of_collinear d3 d4 hB hA with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · rw [d3, mul_zero, zero_add] at e34
      have hb0 : b' = 0 := (mul_eq_zero.1 e34).resolve_right d4
      have ha1 : a' = 1 := by linarith
      subst hb0 ha1
      refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      rw [hzeq p3 (by linarith) (by linarith)]
      exact hA
    · rw [d4, mul_zero, add_zero] at e34
      have ha0 : a' = 0 := (mul_eq_zero.1 e34).resolve_right d3
      have hb1 : b' = 1 := by linarith
      subst ha0 hb1
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      rw [hzeq p4 (by linarith) (by linarith)]
      exact hA
    · exact Or.inl ⟨straddles_of_combo ha hb hab d1 d2 e12,
        straddles_of_combo ha' hb' hab' d3 d4 e34⟩

/-! ## Correctness -/

/-- CLRS Section 33.1: `SEGMENTS-INTERSECT(p₁, p₂, p₃, p₄)` returns `true` exactly when the
closed segments `p₁p₂` and `p₃p₄` have a common point. -/
theorem segmentsIntersect_ret_eq_true_iff (p1 p2 p3 p4 : 𝕜 × 𝕜) :
    (segmentsIntersect p1 p2 p3 p4).ret = true ↔
      (segment 𝕜 p1 p2 ∩ segment 𝕜 p3 p4).Nonempty := by
  rw [segmentsIntersect_ret]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((((h | ⟨hd, ho⟩) | ⟨hd, ho⟩) | ⟨hd, ho⟩) | ⟨hd, ho⟩)
    · exact inter_nonempty_of_straddles h.1 h.2
    · exact ⟨p1, left_mem_segment 𝕜 p1 p2, mem_segment_of_direction_eq_zero hd ho⟩
    · exact ⟨p2, right_mem_segment 𝕜 p1 p2, mem_segment_of_direction_eq_zero hd ho⟩
    · exact ⟨p3, mem_segment_of_direction_eq_zero hd ho, left_mem_segment 𝕜 p3 p4⟩
    · exact ⟨p4, mem_segment_of_direction_eq_zero hd ho, right_mem_segment 𝕜 p3 p4⟩
  · rintro ⟨z, hA, hB⟩
    rcases straddles_or_endpoint_mem hA hB with h | h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨direction_eq_zero_of_mem h, onSegment_of_mem h⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨direction_eq_zero_of_mem h, onSegment_of_mem h⟩))
    · exact Or.inl (Or.inr ⟨direction_eq_zero_of_mem h, onSegment_of_mem h⟩)
    · exact Or.inr ⟨direction_eq_zero_of_mem h, onSegment_of_mem h⟩

end Cslib.Algorithms.Lean.Geometry
