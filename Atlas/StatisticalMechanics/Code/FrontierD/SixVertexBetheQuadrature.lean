/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic










open MeasureTheory

namespace StatMech.FrontierD

noncomputable section



theorem abs_gap_mul_left_sub_intervalIntegral_le
    {f : Real → Real} {C : NNReal} (hf : Continuous f)
    (hlip : LipschitzWith C f) {a b : Real} (hab : a ≤ b) :
    |(b - a) * f a - ∫ x in a..b, f x| ≤
      (C : Real) * (b - a) ^ 2 := by
  have hgap : 0 ≤ b - a := sub_nonneg.mpr hab
  have hrewrite :
      (b - a) * f a - ∫ x in a..b, f x =
        -(∫ x in a..b, (f x - f a)) := by
    rw [intervalIntegral.integral_sub
      (hf.intervalIntegrable a b) intervalIntegrable_const]
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hrewrite, abs_neg]
  have hbound :
      ‖∫ x in a..b, (f x - f a)‖ ≤
        ((C : Real) * (b - a)) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hxa : a ≤ x := hx.1.le
    have hxb : x ≤ b := hx.2
    calc
      ‖f x - f a‖ ≤ (C : Real) * ‖x - a‖ := by
        simpa only [dist_eq_norm] using hlip.norm_sub_le x a
      _ = (C : Real) * (x - a) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxa)]
      _ ≤ (C : Real) * (b - a) := by
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hxb a) C.coe_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hgap] at hbound
  nlinarith


theorem abs_gap_mul_right_sub_intervalIntegral_le
    {f : Real → Real} {C : NNReal} (hf : Continuous f)
    (hlip : LipschitzWith C f) {a b : Real} (hab : a ≤ b) :
    |(b - a) * f b - ∫ x in a..b, f x| ≤
      2 * (C : Real) * (b - a) ^ 2 := by
  have hgap : 0 ≤ b - a := sub_nonneg.mpr hab
  have hleft := abs_gap_mul_left_sub_intervalIntegral_le hf hlip hab
  have hfb : |f b - f a| ≤ (C : Real) * (b - a) := by
    calc
      |f b - f a| = dist (f b) (f a) := by rw [Real.dist_eq]
      _ ≤ (C : Real) * dist b a := hlip.dist_le_mul _ _
      _ = (C : Real) * (b - a) := by
        rw [Real.dist_eq, abs_of_nonneg hgap]
  have hmove : |(b - a) * f b - (b - a) * f a| ≤
      (C : Real) * (b - a) ^ 2 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hgap]
    nlinarith
  calc
    |(b - a) * f b - ∫ x in a..b, f x| ≤
        |(b - a) * f b - (b - a) * f a| +
          |(b - a) * f a - ∫ x in a..b, f x| := by
      exact abs_sub_le _ _ _
    _ ≤ (C : Real) * (b - a) ^ 2 +
        (C : Real) * (b - a) ^ 2 := add_le_add hmove hleft
    _ = 2 * (C : Real) * (b - a) ^ 2 := by ring



theorem abs_leftEndpointSum_sub_intervalIntegral_le
    {f : Real → Real} {C : NNReal} (hf : Continuous f)
    (hlip : LipschitzWith C f) (a : Nat → Real) (n : Nat)
    {mesh : Real} (hordered : ∀ k < n, a k ≤ a (k + 1))
    (hmesh : ∀ k < n, a (k + 1) - a k ≤ mesh) :
    |∑ k ∈ Finset.range n, (a (k + 1) - a k) * f (a k) -
        ∫ x in a 0..a n, f x| ≤
      (C : Real) * mesh * (a n - a 0) := by
  have hsplit :
      (∫ x in a 0..a n, f x) =
        ∑ k ∈ Finset.range n, ∫ x in a k..a (k + 1), f x := by
    exact (intervalIntegral.sum_integral_adjacent_intervals
      (f := f) (n := n) (a := a) (μ := volume)
      (fun k _ => hf.intervalIntegrable (a k) (a (k + 1)))).symm
  rw [hsplit, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ Finset.range n,
        ((a (k + 1) - a k) * f (a k) -
          ∫ x in a k..a (k + 1), f x)| ≤
        ∑ k ∈ Finset.range n,
          |(a (k + 1) - a k) * f (a k) -
            ∫ x in a k..a (k + 1), f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n,
        (C : Real) * mesh * (a (k + 1) - a k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      have hgap : 0 ≤ a (k + 1) - a k :=
        sub_nonneg.mpr (hordered k hklt)
      calc
        |(a (k + 1) - a k) * f (a k) -
            ∫ x in a k..a (k + 1), f x| ≤
            (C : Real) * (a (k + 1) - a k) ^ 2 :=
          abs_gap_mul_left_sub_intervalIntegral_le hf hlip
            (hordered k hklt)
        _ ≤ (C : Real) * mesh * (a (k + 1) - a k) := by
          have hs := mul_le_mul_of_nonneg_right (hmesh k hklt) hgap
          nlinarith [C.coe_nonneg]
    _ = (C : Real) * mesh * (a n - a 0) := by
      rw [← Finset.mul_sum]
      congr 1
      have htel := Finset.sum_range_sub' a n
      rw [Finset.sum_sub_distrib] at htel ⊢
      linarith

end

end StatMech.FrontierD
