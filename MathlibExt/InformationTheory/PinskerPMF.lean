/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

/-! # Pinsker's inequality for PMFs

For probability mass functions on a finite discrete type, the
squared `L1` distance is at most twice the KL divergence. The
right side is in `ℝ≥0∞`, so the statement stays correct when the
divergence is infinite; a `toReal` version would be false there.
The discreteness hypothesis is essential: with a coarse
sigma-algebra the two measures can coincide while the `L1`
distance is positive. This is roadmap package QCI-30 of the Atlas
TCS canon roadmap.

Source: Tsybakov, Introduction to Nonparametric Estimation
(2009), Section 2.3.
-/

open Finset
open scoped MeasureTheory

private lemma pos_of_nonneg_ne {a : ℝ} (ha : 0 ≤ a) (hne : a ≠ 0) : 0 < a :=
  lt_of_le_of_ne ha (fun h => hne h.symm)

/-- Pointwise Gibbs inequality: `r - s ≤ r * log (r / s)` for `r, s ≥ 0`
with `s = 0 → r = 0`. Follows from `log t ≤ t - 1` applied to `t = 1 / (r / s)`. -/
private lemma gibbs_pointwise (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : s = 0 → r = 0) : r - s ≤ r * Real.log (r / s) := by
  by_cases hr0 : r = 0
  · rw [hr0, zero_mul, zero_sub]
    exact neg_nonpos.mpr hs
  · have hrpos : 0 < r := pos_of_nonneg_ne hr hr0
    have hs0 : s ≠ 0 := fun hs0 => hr0 (h hs0)
    have hspos : 0 < s := pos_of_nonneg_ne hs hs0
    have h1t : (0:ℝ) < 1 / (r / s) := one_div_pos.mpr (div_pos hrpos hspos)
    have hlog := Real.log_le_sub_one_of_pos h1t
    rw [one_div, Real.log_inv] at hlog
    have e : r - s = r * (1 - 1 / (r / s)) := by field_simp
    rw [e, one_div]
    apply mul_le_mul_of_nonneg_left _ hr
    linarith

/-- Log-sum (grouping) inequality over a finset: the unnormalized binary KL
of the aggregates is at most the sum of pointwise terms. -/
private lemma log_sum_le {α : Type*} [Fintype α] (x y : α → ℝ) (t : Finset α)
    (hx : ∀ a ∈ t, 0 ≤ x a) (hy : ∀ a ∈ t, 0 ≤ y a)
    (hac : ∀ a ∈ t, y a = 0 → x a = 0) :
    (∑ a ∈ t, x a) * Real.log ((∑ a ∈ t, x a) / (∑ a ∈ t, y a))
      ≤ ∑ a ∈ t, x a * Real.log (x a / y a) := by
  by_cases hY : (∑ a ∈ t, y a) = 0
  · have hy0 : ∀ a ∈ t, y a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a ha => hy a ha)).mp hY
    have hx0 : ∀ a ∈ t, x a = 0 := fun a ha => hac a ha (hy0 a ha)
    have hX : (∑ a ∈ t, x a) = 0 := Finset.sum_eq_zero hx0
    have hR : (∑ a ∈ t, x a * Real.log (x a / y a)) = 0 :=
      Finset.sum_eq_zero (fun a ha => by rw [hx0 a ha, zero_mul])
    rw [hX, zero_mul]
    exact le_of_eq hR.symm
  · by_cases hX : (∑ a ∈ t, x a) = 0
    · have hx0 : ∀ a ∈ t, x a = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun a ha => hx a ha)).mp hX
      have hR : (∑ a ∈ t, x a * Real.log (x a / y a)) = 0 :=
        Finset.sum_eq_zero (fun a ha => by rw [hx0 a ha, zero_mul])
      rw [hX, zero_mul]
      exact le_of_eq hR.symm
    · have hYnn : 0 ≤ ∑ a ∈ t, y a := Finset.sum_nonneg (fun a ha => hy a ha)
      have hYpos : 0 < ∑ a ∈ t, y a := pos_of_nonneg_ne hYnn hY
      have hXnn : 0 ≤ ∑ a ∈ t, x a := Finset.sum_nonneg (fun a ha => hx a ha)
      have hXpos : 0 < ∑ a ∈ t, x a := pos_of_nonneg_ne hXnn hX
      have hpt : ∀ a ∈ t, (x a / (∑ a ∈ t, x a) - y a / (∑ a ∈ t, y a))
          ≤ (x a / (∑ a ∈ t, x a))
            * Real.log ((x a / (∑ a ∈ t, x a)) / (y a / (∑ a ∈ t, y a))) := by
        intro a ha
        apply gibbs_pointwise
        · exact div_nonneg (hx a ha) hXnn
        · exact div_nonneg (hy a ha) hYnn
        · intro hs0
          have hya : y a = 0 := by
            rcases div_eq_zero_iff.mp hs0 with h | h
            · exact h
            · exact absurd h hY
          have hxa : x a = 0 := hac a ha hya
          simp [hxa]
      have hsum := Finset.sum_le_sum hpt
      have hLHS : (∑ a ∈ t, (x a / (∑ a ∈ t, x a) - y a / (∑ a ∈ t, y a))) = 0 := by
        rw [Finset.sum_sub_distrib]
        have eX : (∑ a ∈ t, x a / (∑ a ∈ t, x a)) = 1 := by
          rw [← Finset.sum_div, div_self hX]
        have eY : (∑ a ∈ t, y a / (∑ a ∈ t, y a)) = 1 := by
          rw [← Finset.sum_div, div_self hY]
        rw [eX, eY, sub_self]
      rw [hLHS] at hsum
      have hpos : (0:ℝ) ≤ (∑ a ∈ t, x a)
          * (∑ a ∈ t, (x a / (∑ a ∈ t, x a))
            * Real.log ((x a / (∑ a ∈ t, x a)) / (y a / (∑ a ∈ t, y a)))) :=
        mul_nonneg hXnn hsum
      have hterm : ∀ a ∈ t, (∑ a ∈ t, x a)
            * ((x a / (∑ a ∈ t, x a))
              * Real.log ((x a / (∑ a ∈ t, x a)) / (y a / (∑ a ∈ t, y a))))
          = x a * Real.log (x a / y a)
            - x a * Real.log ((∑ a ∈ t, x a) / (∑ a ∈ t, y a)) := by
        intro a ha
        have hXx : (∑ a ∈ t, x a) * (x a / (∑ a ∈ t, x a)) = x a := by
          rw [← mul_div_assoc]
          exact mul_div_cancel_left₀ _ hX
        rw [← mul_assoc, hXx]
        by_cases hx0 : x a = 0
        · rw [hx0]
          simp
        · have hxpos : 0 < x a := pos_of_nonneg_ne (hx a ha) hx0
          have hyne : y a ≠ 0 := fun hy0 => hx0 (hac a ha hy0)
          have hsplit : (x a / (∑ a ∈ t, x a)) / (y a / (∑ a ∈ t, y a))
              = (x a / y a) / ((∑ a ∈ t, x a) / (∑ a ∈ t, y a)) := by
            field_simp
          rw [hsplit, Real.log_div (div_ne_zero hx0 hyne) (div_ne_zero hX hY),
            mul_sub]
      have hXm : (∑ a ∈ t, x a * Real.log ((∑ a ∈ t, x a) / (∑ a ∈ t, y a)))
          = (∑ a ∈ t, x a) * Real.log ((∑ a ∈ t, x a) / (∑ a ∈ t, y a)) := by
        rw [Finset.sum_mul]
      rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
        hXm] at hpos
      linarith

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

/-- Real-valued Pinsker inequality for finite sums:
`(∑ |x - y|)^2 ≤ 2 * ∑ x log (x / y)`. -/
private lemma real_pinsker {α : Type*} [Fintype α] (x y : α → ℝ)
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

/-- Pinsker's inequality for probability mass functions on a finite
type, with no positivity hypotheses: the squared `L1` distance is at
most twice the Kullback-Leibler divergence (in nats). The right side
is stated in `ℝ≥0∞`, so it stays correct when the divergence is
infinite (the `ENNReal.toReal` form would be false there). -/
theorem pinsker_pmf {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (p q : PMF α) :
    ENNReal.ofReal ((∑ a, |(p a).toReal - (q a).toReal|) ^ 2) ≤
      2 * InformationTheory.klDiv p.toMeasure q.toMeasure := by
  by_cases hac : p.toMeasure ≪ q.toMeasure
  · have hpq : ∀ a, q a = 0 → p a = 0 := by
      intro a hqa
      have h1 : q.toMeasure {a} = 0 := by
        rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
        exact hqa
      have h2 : p.toMeasure {a} = 0 := hac h1
      rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete] at h2
      exact h2
    have huniv : p.toMeasure Set.univ = q.toMeasure Set.univ := by
      rw [MeasureTheory.measure_univ, MeasureTheory.measure_univ]
    have hrn : (fun a => p a / q a)
        =ᵐ[q.toMeasure] p.toMeasure.rnDeriv q.toMeasure := by
      refine MeasureTheory.Measure.eq_rnDeriv (Measurable.of_discrete)
        (MeasureTheory.Measure.MutuallySingular.zero_left) ?_
      rw [zero_add]
      rw [MeasureTheory.Measure.ext_iff_singleton]
      intro a
      rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        MeasureTheory.withDensity_apply _ MeasurableSet.of_discrete,
        MeasureTheory.lintegral_singleton,
        PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
      show p a = p a / q a * q a
      by_cases hqa : q a = 0
      · rw [hqa, hpq a hqa, ENNReal.zero_div, zero_mul]
      · exact (ENNReal.div_mul_cancel hqa (PMF.apply_ne_top q a)).symm
    have hllr : MeasureTheory.llr p.toMeasure q.toMeasure
        =ᵐ[p.toMeasure] (fun a => Real.log ((p a / q a).toReal)) := by
      filter_upwards [hac.ae_le hrn] with a ha
      have ha' : p a / q a = p.toMeasure.rnDeriv q.toMeasure a := ha
      show Real.log (p.toMeasure.rnDeriv q.toMeasure a).toReal
        = Real.log (p a / q a).toReal
      rw [ha']
    have hKLreal : (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal
        = ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) := by
      rw [InformationTheory.toReal_klDiv_of_measure_eq hac huniv,
        MeasureTheory.integral_congr_ae hllr, PMF.integral_eq_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [smul_eq_mul, ENNReal.toReal_div]
    have hx_nn : ∀ a, 0 ≤ (p a).toReal := fun a => ENNReal.toReal_nonneg
    have hy_nn : ∀ a, 0 ≤ (q a).toReal := fun a => ENNReal.toReal_nonneg
    have hsumx : (∑ a, (p a).toReal) = 1 := by
      have h := PMF.tsum_coe p
      rw [tsum_fintype] at h
      have h2 : (∑ a, p a).toReal = (1:ENNReal).toReal := by rw [h]
      rw [ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a)] at h2
      rw [ENNReal.toReal_one] at h2
      exact h2
    have hsumy : (∑ a, (q a).toReal) = 1 := by
      have h := PMF.tsum_coe q
      rw [tsum_fintype] at h
      have h2 : (∑ a, q a).toReal = (1:ENNReal).toReal := by rw [h]
      rw [ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top q a)] at h2
      rw [ENNReal.toReal_one] at h2
      exact h2
    have hac' : ∀ a, (q a).toReal = 0 → (p a).toReal = 0 := by
      intro a hqa
      have hq0 : q a = 0 := by
        by_contra hne
        have hpos : 0 < (q a).toReal :=
          ENNReal.toReal_pos hne (PMF.apply_ne_top q a)
        rw [hqa] at hpos
        exact absurd hpos (lt_irrefl 0)
      rw [hpq a hq0, ENNReal.toReal_zero]
    have hreal : (∑ a, |(p a).toReal - (q a).toReal|) ^ 2
        ≤ 2 * ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) :=
      real_pinsker _ _ hx_nn hy_nn hsumx hsumy hac'
    by_cases h_int :
      MeasureTheory.Integrable (MeasureTheory.llr p.toMeasure q.toMeasure)
        p.toMeasure
    · have hkl : InformationTheory.klDiv p.toMeasure q.toMeasure
          = ENNReal.ofReal
            (∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) := by
        rw [← ENNReal.ofReal_toReal (InformationTheory.klDiv_ne_top hac h_int),
          hKLreal]
      rw [hkl]
      have h2E : (2:ENNReal) = ENNReal.ofReal 2 := by simp
      have h2nn : (0:ℝ) ≤ 2 := by norm_num
      rw [h2E, ← ENNReal.ofReal_mul h2nn]
      exact ENNReal.ofReal_le_ofReal hreal
    · rw [InformationTheory.klDiv_of_not_integrable h_int,
        ENNReal.mul_top (by simp : (2:ENNReal) ≠ 0)]
      exact le_top
  · rw [InformationTheory.klDiv_of_not_ac hac,
      ENNReal.mul_top (by simp : (2:ENNReal) ≠ 0)]
    exact le_top

