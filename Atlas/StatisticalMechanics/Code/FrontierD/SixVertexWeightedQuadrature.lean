/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexRootDensityKernelLipschitz









open MeasureTheory

namespace StatMech.FrontierD

noncomputable section

theorem abs_left_mul_densityIntegral_sub_integral_mul_le
    {f rho : Real → Real} {C : NNReal} {B a b : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hrho : Continuous rho) (hB : 0 <= B)
    (hrhoBound : ∀ x ∈ Set.uIcc a b, |rho x| <= B)
    (hab : a <= b) :
    |f a * (∫ x in a..b, rho x) -
        ∫ x in a..b, f x * rho x| <=
      (C : Real) * B * (b - a) ^ 2 := by
  have hgap : 0 <= b - a := sub_nonneg.mpr hab
  have hrhoInt : IntervalIntegrable rho MeasureTheory.volume a b :=
    hrho.intervalIntegrable a b
  have hmulInt : IntervalIntegrable (fun x => f x * rho x)
      MeasureTheory.volume a b := (hf.mul hrho).intervalIntegrable a b
  have hconstMulInt : IntervalIntegrable (fun x => f a * rho x)
      MeasureTheory.volume a b :=
    (continuous_const.mul hrho).intervalIntegrable a b
  have hrewrite :
      f a * (∫ x in a..b, rho x) -
          ∫ x in a..b, f x * rho x =
        ∫ x in a..b, (f a - f x) * rho x := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_sub hconstMulInt hmulInt]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hrewrite]
  have hbound :
      ‖∫ x in a..b, (f a - f x) * rho x‖ <=
        ((C : Real) * (b - a) * B) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hxa : a <= x := hx.1.le
    have hxb : x <= b := hx.2
    have hfa : |f a - f x| <= (C : Real) * (b - a) := by
      calc
        |f a - f x| = dist (f a) (f x) := by rw [Real.dist_eq]
        _ <= (C : Real) * dist a x := hlip.dist_le_mul a x
        _ = (C : Real) * (x - a) := by
          rw [Real.dist_eq, abs_sub_comm,
            abs_of_nonneg (sub_nonneg.mpr hxa)]
        _ <= (C : Real) * (b - a) := by
          exact mul_le_mul_of_nonneg_left
            (sub_le_sub_right hxb a) C.coe_nonneg
    calc
      ‖(f a - f x) * rho x‖ = |f a - f x| * |rho x| := by
        simp only [Real.norm_eq_abs, abs_mul]
      _ <= ((C : Real) * (b - a)) * B :=
        mul_le_mul hfa (hrhoBound x (by
          rw [Set.uIcc_of_le hab]
          exact ⟨hx.1.le, hx.2⟩)) (abs_nonneg _)
          (mul_nonneg C.coe_nonneg hgap)
      _ = (C : Real) * (b - a) * B := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg hgap] at hbound
  nlinarith




theorem abs_weightedLeftEndpointSum_sub_densityIntegral_le
    {f rho : Real → Real} {C : NNReal} {B mesh : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hrho : Continuous rho) (hB : 0 <= B)
    (a : Nat → Real) (mass : Nat → Real) (n : Nat)
    (hordered : ∀ k < n, a k <= a (k + 1))
    (hmesh : ∀ k < n, a (k + 1) - a k <= mesh)
    (hrhoBound : ∀ x, |rho x| <= B)
    (hmass : ∀ k < n, ∫ x in a k..a (k + 1), rho x = mass k) :
    |∑ k ∈ Finset.range n, mass k * f (a k) -
        ∫ x in a 0..a n, f x * rho x| <=
      (C : Real) * B * mesh * (a n - a 0) := by
  have hsplit :
      (∫ x in a 0..a n, f x * rho x) =
        ∑ k ∈ Finset.range n,
          ∫ x in a k..a (k + 1), f x * rho x := by
    exact (intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x => f x * rho x) (n := n) (a := a)
      (μ := MeasureTheory.volume)
      (fun k _ => (hf.mul hrho).intervalIntegrable
        (a k) (a (k + 1)))).symm
  rw [hsplit, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ Finset.range n,
        (mass k * f (a k) -
          ∫ x in a k..a (k + 1), f x * rho x)| <=
        ∑ k ∈ Finset.range n,
          |mass k * f (a k) -
            ∫ x in a k..a (k + 1), f x * rho x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ k ∈ Finset.range n,
        (C : Real) * B * mesh * (a (k + 1) - a k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      have hgap : 0 <= a (k + 1) - a k :=
        sub_nonneg.mpr (hordered k hklt)
      have hcellBound : ∀ x ∈ Set.uIcc (a k) (a (k + 1)),
          |rho x| <= B := by
        intro x _
        exact hrhoBound x
      calc
        |mass k * f (a k) -
            ∫ x in a k..a (k + 1), f x * rho x| =
            |f (a k) * (∫ x in a k..a (k + 1), rho x) -
              ∫ x in a k..a (k + 1), f x * rho x| := by
          rw [hmass k hklt]
          congr 2
          ring
        _ <= (C : Real) * B * (a (k + 1) - a k) ^ 2 :=
          abs_left_mul_densityIntegral_sub_integral_mul_le
            hf hlip hrho hB hcellBound (hordered k hklt)
        _ <= (C : Real) * B * mesh * (a (k + 1) - a k) := by
          have hCB : 0 <= (C : Real) * B :=
            mul_nonneg C.coe_nonneg hB
          have hs := mul_le_mul_of_nonneg_right (hmesh k hklt) hgap
          nlinarith
    _ = (C : Real) * B * mesh * (a n - a 0) := by
      rw [← Finset.mul_sum]
      congr 1
      have htel := Finset.sum_range_sub' a n
      rw [Finset.sum_sub_distrib] at htel ⊢
      linarith

end

end StatMech.FrontierD
