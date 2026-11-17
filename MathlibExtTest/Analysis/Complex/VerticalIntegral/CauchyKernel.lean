/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.VerticalIntegral.CauchyKernel

/-!
# Tests for the Cauchy kernel on a vertical line
-/

@[expose] public section

open Complex
open scoped Real

example : (1 : ℂ) / ((3 : ℝ) + (4 : ℝ) * I) = ((3 / 25 : ℝ) : ℂ) - I * ((4 / 25 : ℝ) : ℂ) := by
  rw [one_div_ofReal_add_mul_I (by norm_num)]
  norm_num

example : ((0 : ℝ) : ℂ) + (1 : ℝ) * I ≠ 0 := ofReal_add_mul_I_ne_zero (Or.inr one_ne_zero)

/-- `∫_{-1}^{1} dt / (1 + t²) = 2 arctan 1 = π / 2`. -/
example : ∫ t in (-1 : ℝ)..1, (1 : ℝ) / (1 ^ 2 + t ^ 2) = π / 2 := by
  rw [integral_div_sq_add_sq_neg_self, div_one, Real.arctan_one]
  ring

/-- Boundary probe: at `σ = 0` the integrand is `0 / t² = 0` and `arctan (R / 0) = 0`. -/
example (R : ℝ) : ∫ t in (-R)..R, (0 : ℝ) / (0 ^ 2 + t ^ 2) = 0 := by
  rw [integral_div_sq_add_sq_neg_self]
  simp

/-- On a symmetric interval the imaginary (logarithmic) part cancels. -/
example (T : ℝ) :
    ∫ t in (-T)..T, (1 : ℂ) / ((1 : ℝ) + t * I) = ((2 * Real.arctan T : ℝ) : ℂ) := by
  rw [integral_one_div_ofReal_add_mul_I one_ne_zero]
  simp only [div_one, Real.arctan_neg, neg_sq, sub_self, ofReal_zero, mul_zero, sub_zero]
  push_cast
  ring

example (t : ℝ) : HasDerivAt (fun u : ℝ => Real.arctan (u / 2)) (2 / (2 ^ 2 + t ^ 2)) t :=
  Real.hasDerivAt_arctan_div two_ne_zero t
