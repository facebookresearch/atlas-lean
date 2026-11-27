/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.MellinInversePowerOfLinear

/-!
# Inverse Mellin transform of `(s - a)^{-m}`: API checks

Concrete instances with `m = 2`, `a = 0`, `σ = 1`: the inverse Mellin transform of `s^{-2}` is
`log 2` at `x = 1/2` and `0` at `x = 2`, and the defining integrand is integrable.
-/

@[expose] public section

open Complex MeasureTheory MetaMathlibExt

/-- `(1/2πi) ∫_{1-i∞}^{1+i∞} (1/2)^{-s} s^{-2} ds = log 2`. -/
example : mellinInv 1 (fun s : ℂ => (s ^ 2)⁻¹) (1 / 2) = (Real.log 2 : ℂ) := by
  have h := mellinInv_inv_sub_pow_of_le_one (m := 2) (a := 0) (σ := 1) (x := 1 / 2) le_rfl
    one_pos (by norm_num) (by norm_num)
  rw [show (fun s : ℂ => (s ^ 2)⁻¹) = fun s : ℂ => ((s - ((0 : ℝ) : ℂ)) ^ 2)⁻¹ by simp, h]
  rw [one_div, Real.log_inv, abs_neg, abs_of_pos (Real.log_pos one_lt_two)]
  norm_num

/-- `(1/2πi) ∫_{1-i∞}^{1+i∞} 2^{-s} s^{-2} ds = 0`. -/
example : mellinInv 1 (fun s : ℂ => (s ^ 2)⁻¹) 2 = 0 := by
  have h := mellinInv_inv_sub_pow_of_one_le (m := 2) (a := 0) (σ := 1) (x := 2) le_rfl
    one_pos (by norm_num)
  simpa using h

/-- The line `Re s = 3` gives the same value as `Re s = 1`. -/
example : mellinInv 3 (fun s : ℂ => (s ^ 2)⁻¹) (1 / 2) =
    mellinInv 1 (fun s : ℂ => (s ^ 2)⁻¹) (1 / 2) := by
  have h := mellinInv_inv_sub_pow_indep (m := 2) (a := 0) (σ := 3) (σ' := 1) (x := 1 / 2) le_rfl
    (by norm_num) one_pos (by norm_num)
  simpa using h

/-- Absolute convergence of `t ↦ 2^{-1-it} (1 + it)^{-2}`. -/
example : Integrable (fun t : ℝ => ((2 : ℝ) : ℂ) ^ (-((1 : ℝ) + t * I)) *
    (((1 : ℝ) + t * I - ((0 : ℝ) : ℂ)) ^ 2)⁻¹) :=
  integrable_cpow_mul_inv_sub_pow le_rfl one_pos two_pos
