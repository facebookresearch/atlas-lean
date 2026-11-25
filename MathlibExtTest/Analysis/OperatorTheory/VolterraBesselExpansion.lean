/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.OperatorTheory.VolterraBesselExpansion

namespace MetaMathlibExt.VolterraBesselExpansionTest

/-! The expansion of `(XV)^n` for `n = 1, 2, 3`, with the Bessel numbers of `y_0 = 1`,
`y_1 = 1 + x` and `y_2 = 1 + 3x + 3x²` made explicit. -/

/-- `n = 1`: `(XV) f (x) = x (V f)(x)`. -/
example (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    (fun g : ℝ → ℝ => fun y => y * ∫ t in (0 : ℝ)..y, g t)^[1] f x =
      x * (fun g : ℝ → ℝ => fun y => ∫ t in (0 : ℝ)..y, g t)^[1] f x := by
  rw [xMul_volterra_iterate_eq_sum_bessel 1 le_rfl f hf x]
  simp [besselPolynomial_zero]

/-- `n = 2`: `(XV)² f (x) = x² (V² f)(x) - x (V³ f)(x)`. -/
example (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    (fun g : ℝ → ℝ => fun y => y * ∫ t in (0 : ℝ)..y, g t)^[2] f x =
      x ^ 2 * (fun g : ℝ → ℝ => fun y => ∫ t in (0 : ℝ)..y, g t)^[2] f x -
        x * (fun g : ℝ → ℝ => fun y => ∫ t in (0 : ℝ)..y, g t)^[3] f x := by
  rw [xMul_volterra_iterate_eq_sum_bessel 2 (by norm_num) f hf x]
  simp [Finset.sum_range_succ, besselPolynomial_one, Polynomial.coeff_one]
  ring

/-- `n = 3`: `(XV)³ f (x) = x³ (V³ f)(x) - 3x² (V⁴ f)(x) + 3x (V⁵ f)(x)`. -/
example (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    (fun g : ℝ → ℝ => fun y => y * ∫ t in (0 : ℝ)..y, g t)^[3] f x =
      x ^ 3 * (fun g : ℝ → ℝ => fun y => ∫ t in (0 : ℝ)..y, g t)^[3] f x -
        3 * x ^ 2 * (fun g : ℝ → ℝ => fun y => ∫ t in (0 : ℝ)..y, g t)^[4] f x +
        3 * x * (fun g : ℝ → ℝ => fun y => ∫ t in (0 : ℝ)..y, g t)^[5] f x := by
  rw [xMul_volterra_iterate_eq_sum_bessel 3 (by norm_num) f hf x]
  simp [Finset.sum_range_succ, besselPolynomial_two, Polynomial.coeff_one, Polynomial.coeff_X]
  ring

end MetaMathlibExt.VolterraBesselExpansionTest
