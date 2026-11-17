/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.VerticalIntegral.PerronKernel
import MathlibExt.Analysis.Complex.VerticalIntegral.CauchyKernel

/-!
# The vertical integral of `y^s / (α s + β)²`

For `c > 0`, `α > 0` and `β ≥ 0`,
`(1 / 2πi) ∫_{(c)} y^s / (α s + β)² ds = α^{-2} y^{-β/α} log y` if `y > 1`, and `0` if
`0 ≤ y ≤ 1`. This is the second-order Perron kernel `y^w / w²` after the substitution
`w = s + β/α`.

## Main statements

* `Complex.hasVerticalIntegral_cpow_div_mul_add_sq`: the value of the vertical integral.
-/

open Complex

@[expose] public section

namespace Complex

/-- For `c > 0`, `α > 0`, `β ≥ 0` and `y ≥ 0`,
`(1 / 2πi) ∫_{(c)} y^s / (α s + β)² ds` equals `α^{-2} y^{-β/α} log y` if `y > 1` and `0`
otherwise. -/
theorem hasVerticalIntegral_cpow_div_mul_add_sq {c α β : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hβ : 0 ≤ β) {y : ℝ} (hy : 0 ≤ y) :
    HasVerticalIntegral c (fun s => (y : ℂ) ^ s / ((α : ℂ) * s + β) ^ 2)
      (if 1 < y then (α : ℂ) ^ (-2 : ℤ) * (y : ℂ) ^ (-(β / α) : ℂ) * Real.log y else 0) := by
  have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  set b : ℝ := β / α with hb
  have hb0 : 0 ≤ b := div_nonneg hβ hα.le
  have hcb : 0 < c - -b := by linarith
  rcases hy.eq_or_lt with hy0 | hy0
  · -- `y = 0`: the integrand vanishes on the line
    subst hy0
    have h1 : ¬ (1 < (0 : ℝ)) := by norm_num
    rw [ite_eq_right h1]
    refine hasVerticalIntegral_zero.congr_line fun t => ?_
    have hne : (c : ℂ) + (t : ℂ) * I ≠ 0 := ofReal_add_mul_I_ne_zero (Or.inl hc.ne')
    simp [zero_cpow hne]
  · have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have key : HasVerticalIntegral (c - -b) (fun w : ℂ => (y : ℂ) ^ w / w ^ 2)
        (if 1 < y then (Real.log y : ℂ) else 0) := by
      split_ifs with h1
      · simpa using hasVerticalIntegral_cpow_div_pow_succ_of_one_le (k := 1) le_rfl hcb h1.le
      · simpa using hasVerticalIntegral_cpow_div_pow_succ_of_le_one
          (k := 1) le_rfl hcb hy0 (not_lt.1 h1)
    have h2 := (key.const_mul ((α : ℂ) ^ (-2 : ℤ) * (y : ℂ) ^ (-(b : ℂ)))).comp_sub_ofReal
    have h3 : HasVerticalIntegral c (fun s => (α : ℂ) ^ (-2 : ℤ) * (y : ℂ) ^ (-(b : ℂ)) *
        ((y : ℂ) ^ (s - ((-b : ℝ) : ℂ)) / (s - ((-b : ℝ) : ℂ)) ^ 2))
        (if 1 < y then (α : ℂ) ^ (-2 : ℤ) * (y : ℂ) ^ (-(β / α) : ℂ) * Real.log y else 0) := by
      convert h2 using 1
      split_ifs <;> push_cast [hb] <;> ring
    refine h3.congr_line fun t => ?_
    set s : ℂ := (c : ℂ) + (t : ℂ) * I
    have hsb : (α : ℂ) * s + β = α * (s + b) := by
      rw [hb]; push_cast; field_simp
    rw [hsb, show s - ((-b : ℝ) : ℂ) = s + b by push_cast; ring,
      cpow_add _ _ hyC, zpow_neg, zpow_two]
    have : (y : ℂ) ^ (b : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; tauto
    rw [cpow_neg]
    field_simp

end Complex
