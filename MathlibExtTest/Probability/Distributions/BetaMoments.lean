/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.BetaMoments

/-!
# Tests for the moments of the beta law

The uniform law `Beta(1, 1)` (mean `1/2`, `E[X ^ 2] = 1/3`, `E[X (1 - X)] = 1/6`), an asymmetric
law, a small-parameter law, a mixed moment through the general formula, the expected
heterozygosity `E[2 X (1 - X)]` of Wright's stationary law, and the junk value outside the
parameter domain `α, β > 0`.
-/

open MeasureTheory ProbabilityTheory Real

namespace MathlibExtTest.Probability.Distributions.BetaMoments

/-- The uniform law `Beta(1, 1)` has mean `1/2`. -/
example : ∫ x, x ∂betaMeasure 1 1 = 1 / 2 := by
  rw [integral_id_betaMeasure one_pos one_pos]
  norm_num

/-- The uniform law has `E[X ^ 2] = 1/3` and `E[X (1 - X)] = 1/2 - 1/3 = 1/6`. -/
example : ∫ x, x ^ 2 ∂betaMeasure 1 1 = 1 / 3 ∧
    ∫ x, x * (1 - x) ∂betaMeasure 1 1 = 1 / 6 := by
  rw [integral_sq_betaMeasure one_pos one_pos, integral_mul_one_sub_betaMeasure one_pos one_pos]
  norm_num

/-- `Beta(1, 3)`: mean `1/4` and `E[X (1 - X)] = 3 / (4 · 5) = 3/20`. -/
example : ∫ x, x ∂betaMeasure 1 3 = 1 / 4 ∧
    ∫ x, x * (1 - x) ∂betaMeasure 1 3 = 3 / 20 := by
  rw [integral_id_betaMeasure one_pos (by norm_num),
    integral_mul_one_sub_betaMeasure one_pos (by norm_num)]
  norm_num

/-- The general formula at `k = m = 0` is the total mass `1`. -/
example : ∫ x, x ^ 0 * (1 - x) ^ 0 ∂betaMeasure 2 5 = 1 := by
  rw [integral_pow_mul_one_sub_pow_betaMeasure (by norm_num) (by norm_num)]
  simp only [Nat.cast_zero, add_zero]
  exact div_self (beta_pos (by norm_num) (by norm_num)).ne'

/-- Expected heterozygosity of Wright's stationary law `Beta(θ₁, θ₂)` with small mutation rates
`θ₁ = θ₂ = 1/10`: `E[2 X (1 - X)] = 2 θ₁ θ₂ / ((θ₁ + θ₂) (θ₁ + θ₂ + 1)) = 1/12`. -/
example : ∫ x, 2 * (x * (1 - x)) ∂betaMeasure (1 / 10) (1 / 10) = 1 / 12 := by
  rw [integral_const_mul, integral_mul_one_sub_betaMeasure (by norm_num) (by norm_num)]
  norm_num

/-- The beta density at the midpoint of the uniform law is `1`. -/
example : betaPDFReal 1 1 (1 / 2) = 1 := by
  have hB : beta 1 1 = 1 := by simp [beta, one_add_one_eq_two]
  simp [betaPDFReal, hB]
  norm_num

/-- Junk value outside the domain: for `β = 0` the normalizing constant `B(1, 0)` is `0`
(`Γ(0) = 0` in Mathlib), so `betaMeasure 1 0` is the zero measure and its "mean" is `0`, not the
formula's `α / (α + β) = 1`. This is why the moment theorems assume `α, β > 0`. -/
example : ∫ x, x ∂betaMeasure 1 0 = 0 := by
  have hB : beta 1 0 = 0 := by simp [beta]
  have hpdf : betaPDF 1 0 = 0 := by
    funext x
    simp [betaPDF, betaPDFReal, hB]
  simp [betaMeasure, hpdf]

#print axioms integral_pow_mul_one_sub_pow_betaMeasure
#print axioms integral_sq_betaMeasure

end MathlibExtTest.Probability.Distributions.BetaMoments
