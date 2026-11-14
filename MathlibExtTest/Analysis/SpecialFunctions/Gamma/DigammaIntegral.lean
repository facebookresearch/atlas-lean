/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaIntegral

/-!
# Tests for the integral representation of the digamma function
-/

@[expose] public section

open Complex

/-- At `z = 1` the integrand vanishes and the formula is Mathlib's `ψ(1) = -γ`. -/
example : digamma 1 = -Real.eulerMascheroniConstant := by
  rw [digamma_eq_integral_sub_eulerMascheroniConstant (by norm_num)]
  simp

/-- At `z = 2` the integrand is `1`, so `ψ(2) = 1 - γ`. -/
example : digamma 2 = 1 - Real.eulerMascheroniConstant := by
  rw [digamma_eq_integral_sub_eulerMascheroniConstant (by norm_num)]
  have h : (∫ t in (0 : ℝ)..1, (1 - ((1 - t : ℝ) : ℂ) ^ ((2 : ℂ) - 1)) / (t : ℂ)) =
      ∫ _ in (0 : ℝ)..1, (1 : ℂ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    rw [show (2 : ℂ) - 1 = 1 by norm_num, cpow_one]
    push_cast
    rw [sub_sub_cancel, div_self ht0]
  rw [h]
  simp

example : IntervalIntegrable (fun t : ℝ => (((1 - t : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1) - 1) / (t : ℂ))
    MeasureTheory.volume 0 1 :=
  intervalIntegrable_ofReal_one_sub_cpow_sub_one_div (by norm_num)
