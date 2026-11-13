/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import MathlibExt.InformationTheory.LogSum

/-!
# Csiszar-Kullback-Pinsker inequality

For nonnegative probability vectors `p` and `q` on a finite type,
where `q a = 0` implies `p a = 0`,
`(∑ |p a - q a|)² ≤ 2 * ∑ p a * log (p a / q a)`. The proof splits the type by the sign of
`p a - q a`, applies the log-sum inequality on each part, and reduces to the two-point case, which
is proved by calculus. The strictly positive theorem is a corollary.

Source for the support-aware form: Tsybakov, Introduction to Nonparametric
Estimation (2009), Section 2.3.
-/

@[expose] public section

open Finset BigOperators

namespace MathlibExt.InformationTheory.Pinsker

private lemma pos_of_nonneg_ne {a : ℝ} (ha : 0 ≤ a) (hne : a ≠ 0) : 0 < a :=
  lt_of_le_of_ne ha (fun h => hne h.symm)

/-- Log-sum (grouping) inequality over a finset: the unnormalized binary KL
of the aggregates is at most the sum of pointwise terms. This is a reduction
to the shared `Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div` in
`MathlibExt/InformationTheory/LogSum.lean`: filter `t` to the indices where
`y a ≠ 0`, where the shared theorem's strict-positivity hypothesis holds, and
the removed indices contribute `0` to every sum by `hac`. -/
private lemma log_sum_le {α : Type*} [Fintype α] (x y : α → ℝ) (t : Finset α)
    (hx : ∀ a ∈ t, 0 ≤ x a) (hy : ∀ a ∈ t, 0 ≤ y a)
    (hac : ∀ a ∈ t, y a = 0 → x a = 0) :
    (∑ a ∈ t, x a) * Real.log ((∑ a ∈ t, x a) / (∑ a ∈ t, y a))
      ≤ ∑ a ∈ t, x a * Real.log (x a / y a) := by
  classical
  have hsub : ∀ a ∈ t, a ∉ t.filter (fun a => y a ≠ 0) → x a = 0 := by
    intro a ha ha'
    by_contra hxa
    have hya : y a ≠ 0 := by
      intro hy0
      exact hxa (hac a ha hy0)
    exact ha' (Finset.mem_filter.mpr ⟨ha, hya⟩)
  have hsumx : ∑ a ∈ t, x a = ∑ a ∈ t.filter (fun a => y a ≠ 0), x a :=
    (Finset.sum_subset (Finset.filter_subset _ _) (fun a ha ha' => hsub a ha ha')).symm
  have hsumy : ∑ a ∈ t, y a = ∑ a ∈ t.filter (fun a => y a ≠ 0), y a :=
    (Finset.sum_subset (Finset.filter_subset _ _)
      (fun a ha ha' => by
        by_contra hyne
        exact ha' (Finset.mem_filter.mpr ⟨ha, hyne⟩))).symm
  have hsumRHS : ∑ a ∈ t, x a * Real.log (x a / y a) =
      ∑ a ∈ t.filter (fun a => y a ≠ 0), x a * Real.log (x a / y a) :=
    (Finset.sum_subset (Finset.filter_subset _ _)
      (fun a ha ha' => by rw [hsub a ha ha', zero_mul])).symm
  have hmain := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div
    (t.filter (fun a => y a ≠ 0)) x y
    (fun a ha => hx a (Finset.mem_of_mem_filter a ha))
    (fun a ha => lt_of_le_of_ne (hy a (Finset.mem_of_mem_filter a ha))
      (Ne.symm (Finset.mem_filter.mp ha).2))
  rwa [← hsumx, ← hsumy, ← hsumRHS] at hmain

/-- First derivative of the binary-Pinsker auxiliary function
`H(t) = t * log t + (1 - t) * log (1 - t) - 2 * t^2` on `(0, 1)`. -/
private lemma hasDerivAt_H (x : ℝ) (hx0 : x ≠ 0) (hx1 : (1:ℝ) - x ≠ 0) :
    HasDerivAt (fun t => t * Real.log t + (1 - t) * Real.log (1 - t) - 2 * t^2)
      (Real.log x - Real.log (1 - x) - 4 * x) x := by
  have hu : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    have h := (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
    have hval0 : (0:ℝ) - 1 = -1 := by ring
    rw [hval0] at h
    exact h
  have h1 : HasDerivAt (fun t => t * Real.log t) (Real.log x + 1) x :=
    Real.hasDerivAt_mul_log hx0
  have h2 : HasDerivAt (fun t : ℝ => (1 - t) * Real.log (1 - t))
      ((Real.log (1 - x) + 1) * -1) x :=
    (Real.hasDerivAt_mul_log hx1).comp x hu
  have h3 : HasDerivAt (fun t : ℝ => 2 * t^2) (2 * (↑2 * x^(2-1))) x :=
    (hasDerivAt_pow 2 x).const_mul 2
  have hfull := (h1.add h2).sub h3
  have hval : ((Real.log x + 1) + ((Real.log (1 - x) + 1) * -1))
      - 2 * (↑2 * x^(2-1))
      = Real.log x - Real.log (1 - x) - 4 * x := by
    rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
    ring
  rw [hval] at hfull
  exact hfull

/-- Second derivative of the auxiliary function. -/
private lemma hasDerivAt_H' (x : ℝ) (hx0 : x ≠ 0) (hx1 : (1:ℝ) - x ≠ 0) :
    HasDerivAt (fun t => Real.log t - Real.log (1 - t) - 4 * t)
      (x⁻¹ + (1 - x)⁻¹ - 4) x := by
  have hu : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    have h := (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
    have hval0 : (0:ℝ) - 1 = -1 := by ring
    rw [hval0] at h
    exact h
  have k1 : HasDerivAt (fun t => Real.log t) (x⁻¹) x := Real.hasDerivAt_log hx0
  have k2 : HasDerivAt (fun t => Real.log (1 - t)) ((-1) / (1 - x)) x :=
    hu.log hx1
  have k3 : HasDerivAt (fun t : ℝ => 4 * t) (4 * 1) x :=
    (hasDerivAt_id x).const_mul 4
  have hfull := (k1.sub k2).sub k3
  have e : (-1:ℝ) / (1 - x) = -((1 - x)⁻¹) := by
    rw [div_eq_mul_inv]
    ring
  have hval : (x⁻¹ - -1 / (1 - x)) - 4 * 1 = x⁻¹ + (1 - x)⁻¹ - 4 := by
    rw [e]
    ring
  rw [hval] at hfull
  exact hfull

/-- The auxiliary function is convex on `[0, 1]`: its second derivative
`1 / (t * (1 - t)) - 4 = (1 - 2t)^2 / (t * (1 - t))` is nonnegative on `(0, 1)`. -/
private lemma convexOn_H :
    ConvexOn ℝ (Set.Icc 0 1)
      (fun t => t * Real.log t + (1 - t) * Real.log (1 - t) - 2 * t^2) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
  · have h1 : ContinuousOn (fun t => t * Real.log t) (Set.Icc 0 1) :=
      Real.continuous_mul_log.continuousOn
    have h2 : ContinuousOn (fun t => (1 - t) * Real.log (1 - t)) (Set.Icc 0 1) :=
      (Real.continuous_mul_log.comp
        (continuous_const.sub continuous_id)).continuousOn
    have h3 : Continuous (fun t : ℝ => 2 * t^2) := by continuity
    exact (h1.add h2).sub h3.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hx0, hx1⟩ := Set.mem_Ioo.mp hx
    have hx0' : x ≠ 0 := ne_of_gt hx0
    have hx1' : (1:ℝ) - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
    exact (hasDerivAt_H x hx0' hx1').hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hx0, hx1⟩ := Set.mem_Ioo.mp hx
    have hx0' : x ≠ 0 := ne_of_gt hx0
    have hx1' : (1:ℝ) - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
    exact (hasDerivAt_H' x hx0' hx1').hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hx0, hx1⟩ := Set.mem_Ioo.mp hx
    show (0:ℝ) ≤ x⁻¹ + (1 - x)⁻¹ - 4
    have hx1pos : (0:ℝ) < 1 - x := sub_pos.mpr hx1
    have hpos : (0:ℝ) < x * (1 - x) := mul_pos hx0 hx1pos
    have heq : x⁻¹ + (1 - x)⁻¹ - 4 = (1 - 2 * x)^2 / (x * (1 - x)) := by
      field_simp
      ring
    rw [heq]
    exact div_nonneg (sq_nonneg _) hpos.le

/-- Binary Pinsker inequality: for `X, Y ∈ [0, 1]`, `2 * (X - Y)^2` is at most
the binary KL divergence. Proved via convexity of the auxiliary function `H`. -/
private lemma binary_pinsker (X Y : ℝ) (hX0 : 0 ≤ X) (hX1 : X ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) (hac0 : Y = 0 → X = 0) (hac1 : Y = 1 → X = 1) :
    2 * (X - Y)^2
      ≤ X * Real.log (X / Y) + (1 - X) * Real.log ((1 - X) / (1 - Y)) := by
  by_cases hY0' : Y = 0
  · rw [hY0', hac0 hY0']
    simp
  · by_cases hY1' : Y = 1
    · rw [hY1', hac1 hY1']
      simp
    · have hYpos : 0 < Y := pos_of_nonneg_ne hY0 hY0'
      have hYlt : Y < 1 := lt_of_le_of_ne hY1 hY1'
      have hYne1 : (1:ℝ) - Y ≠ 0 := ne_of_gt (sub_pos.mpr hYlt)
      have hXmem : X ∈ Set.Icc 0 1 := ⟨hX0, hX1⟩
      have hYmem : Y ∈ Set.Icc 0 1 := ⟨hY0, hY1⟩
      have hYd : HasDerivAt
          (fun t => t * Real.log t + (1 - t) * Real.log (1 - t) - 2 * t^2)
          (Real.log Y - Real.log (1 - Y) - 4 * Y) Y :=
        hasDerivAt_H Y hY0' hYne1
      have hfo : (Y * Real.log Y + (1 - Y) * Real.log (1 - Y) - 2 * Y^2)
          + (Real.log Y - Real.log (1 - Y) - 4 * Y) * (X - Y)
          ≤ X * Real.log X + (1 - X) * Real.log (1 - X) - 2 * X^2 := by
        rcases lt_trichotomy X Y with hlt | heq | hgt
        · have h := convexOn_H.slope_le_of_hasDerivAt hXmem hYmem hlt hYd
          rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hlt)] at h
          have h' : (Y * Real.log Y + (1 - Y) * Real.log (1 - Y) - 2 * Y^2)
              - (X * Real.log X + (1 - X) * Real.log (1 - X) - 2 * X^2)
              ≤ (Real.log Y - Real.log (1 - Y) - 4 * Y) * (Y - X) := h
          linarith
        · subst heq
          simp
        · have h := convexOn_H.le_slope_of_hasDerivAt hYmem hXmem hgt hYd
          rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hgt)] at h
          have h' : (Real.log Y - Real.log (1 - Y) - 4 * Y) * (X - Y)
              ≤ (X * Real.log X + (1 - X) * Real.log (1 - X) - 2 * X^2)
              - (Y * Real.log Y + (1 - Y) * Real.log (1 - Y) - 2 * Y^2) := h
          linarith
      have e1 : X * Real.log (X / Y) = X * Real.log X - X * Real.log Y := by
        by_cases hx0 : X = 0
        · rw [hx0]
          simp
        · rw [Real.log_div hx0 hY0', mul_sub]
      have e2 : (1 - X) * Real.log ((1 - X) / (1 - Y))
          = (1 - X) * Real.log (1 - X) - (1 - X) * Real.log (1 - Y) := by
        by_cases hx1 : (1:ℝ) - X = 0
        · rw [hx1]
          simp
        · rw [Real.log_div hx1 hYne1, mul_sub]
      rw [e1, e2]
      linear_combination hfo

/-- Csiszar-Kullback-Pinsker for nonnegative finite probability vectors:
`(∑ |x - y|)^2 ≤ 2 * ∑ x log (x / y)`, provided `x` vanishes wherever
`y` does. Zero coordinates are allowed; the support hypothesis rules out
infinite divergence, which the real logarithm cannot represent. -/
theorem csiszar_kullback_pinsker_of_support {α : Type*} [Fintype α] (x y : α → ℝ)
    (hx : ∀ a, 0 ≤ x a) (hy : ∀ a, 0 ≤ y a)
    (hsumx : ∑ a, x a = 1) (hsumy : ∑ a, y a = 1)
    (hac : ∀ a, y a = 0 → x a = 0) :
    (∑ a, |x a - y a|) ^ 2 ≤ 2 * ∑ a, x a * Real.log (x a / y a) := by
  classical
  have hsplit_abs :
      (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), |x a - y a|)
        + (∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), |x a - y a|)
        = ∑ a, |x a - y a| :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsplit :
      (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), (x a - y a))
        + (∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), (x a - y a))
        = ∑ a, (x a - y a) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsplitx :
      (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), x a)
        + (∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), x a)
        = ∑ a, x a :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsplity :
      (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), y a)
        + (∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), y a)
        = ∑ a, y a :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsplitS :
      (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), x a * Real.log (x a / y a))
        + (∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a),
          x a * Real.log (x a / y a))
        = ∑ a, x a * Real.log (x a / y a) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have htot : ∑ a, (x a - y a) = 0 := by
    rw [Finset.sum_sub_distrib, hsumx, hsumy, sub_self]
  have hS1 : (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), |x a - y a|)
      = ∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), (x a - y a) := by
    apply Finset.sum_congr rfl
    intro a ha
    have hle : y a ≤ x a := (Finset.mem_filter.mp ha).2
    exact abs_of_nonneg (sub_nonneg.mpr hle)
  have hS2 : (∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), |x a - y a|)
      = ∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), (y a - x a) := by
    apply Finset.sum_congr rfl
    intro a ha
    have hna : ¬ y a ≤ x a := (Finset.mem_filter.mp ha).2
    have hlt : x a < y a := lt_of_not_ge hna
    rw [abs_of_neg (sub_neg.mpr hlt)]
    ring
  have hS2' : (∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), (y a - x a))
      = ∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), (x a - y a) := by
    have e : (∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), (y a - x a))
        = - ∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), (x a - y a) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [e]
    linarith
  have hTV : (∑ a, |x a - y a|)
      = 2 * ∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), (x a - y a) := by
    have h := hsplit_abs
    rw [hS1, hS2, hS2'] at h
    linarith
  have hXnn : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), x a :=
    Finset.sum_nonneg (fun a _ => hx a)
  have hYnn : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), y a :=
    Finset.sum_nonneg (fun a _ => hy a)
  have hXbar_nn : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), x a :=
    Finset.sum_nonneg (fun a _ => hx a)
  have hYbar_nn : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), y a :=
    Finset.sum_nonneg (fun a _ => hy a)
  have hX1 : (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), x a) ≤ 1 := by
    linarith
  have hY1 : (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), y a) ≤ 1 := by
    linarith
  have hac0 : (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), y a) = 0
      → (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), x a) = 0 := by
    intro hY0
    have hy0 : ∀ a ∈ Finset.univ.filter (fun a => y a ≤ x a), y a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hy a)).mp hY0
    apply Finset.sum_eq_zero
    intro a ha
    exact hac a (hy0 a ha)
  have hac1 : (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), y a) = 1
      → (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), x a) = 1 := by
    intro hY1h
    have hYbar0 : (∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), y a) = 0 := by
      linarith
    have hy0 : ∀ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), y a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hy a)).mp hYbar0
    have hXbar0 : (∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), x a) = 0 :=
      Finset.sum_eq_zero (fun a ha => hac a (hy0 a ha))
    linarith
  have hlog1 := log_sum_le x y (Finset.univ.filter (fun a => y a ≤ x a))
    (fun a _ => hx a) (fun a _ => hy a) (fun a _ => hac a)
  have hlog2 := log_sum_le x y (Finset.univ.filter (fun a => ¬ y a ≤ x a))
    (fun a _ => hx a) (fun a _ => hy a) (fun a _ => hac a)
  have hbin := binary_pinsker _ _ hXnn hX1 hYnn hY1 hac0 hac1
  have eX : (1:ℝ) - (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), x a)
      = ∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), x a := by
    linarith
  have eY : (1:ℝ) - (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), y a)
      = ∑ a ∈ Finset.univ.filter (fun a => ¬ y a ≤ x a), y a := by
    linarith
  rw [eX, eY] at hbin
  have h2 : 2 * ((∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), x a)
      - (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), y a))^2
      ≤ ∑ a, x a * Real.log (x a / y a) := by
    linarith
  have hXYδ : (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), x a)
      - (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), y a)
      = ∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), (x a - y a) :=
    (Finset.sum_sub_distrib x y).symm
  rw [hXYδ] at h2
  rw [hTV]
  have hsq : (2 * ∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a), (x a - y a))^2
      = 2 * (2 * (∑ a ∈ Finset.univ.filter (fun a => y a ≤ x a),
        (x a - y a))^2) := by
    ring
  rw [hsq]
  linarith

/--
Finite strictly-positive Csiszar-Kullback-Pinsker inequality: for finite nonempty `α` and pmfs `p, q
: α → ℝ` with `p a > 0`, `q a > 0` and sums `1`, `(∑ |p a - q a|)² ≤ 2 * ∑ p a * log (p a / q a)`
with natural log, equivalent to `TV(p,q) ≤ √(D_KL/2)`.
Source: M. S. Pinsker, Information and Information Stability of Random Variables and Processes
(1960; English translation 1964), with I. Csiszar, Information-type measures of difference of
probability distributions and indirect observations, Studia Sci. Math. Hungar. 2 (1967), 299-318.
Proves `Wanted` entry `csiszar_kullback_pinsker`, without its `[DecidableEq α]`, which the statement
does not use.
-/
theorem csiszar_kullback_pinsker
    {α : Type*} [Fintype α] [Nonempty α]
    (p q : α → ℝ)
    (hp_pos : ∀ a, 0 < p a)
    (hq_pos : ∀ a, 0 < q a)
    (hp_sum : ∑ a : α, p a = 1)
    (hq_sum : ∑ a : α, q a = 1) :
    (∑ a : α, |p a - q a|) ^ 2 ≤ 2 * ∑ a : α, p a * Real.log (p a / q a) := by
  exact csiszar_kullback_pinsker_of_support p q
    (fun a => (hp_pos a).le) (fun a => (hq_pos a).le) hp_sum hq_sum
    (fun a ha => ((hq_pos a).ne' ha).elim)

end MathlibExt.InformationTheory.Pinsker
