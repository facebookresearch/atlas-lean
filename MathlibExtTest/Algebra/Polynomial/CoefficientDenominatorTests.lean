/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.CoefficientDenominator
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MetaMathlibExt

open Polynomial

/-- The zero polynomial has denominator `1`. -/
example : polynomialDenominator (0 : ℚ[X]) = 1 := by
  simp [polynomialDenominator]

/-- A sparse polynomial whose coefficient denominators `2` and `3` have LCM `6`. -/
example : polynomialDenominator (C (1 / 2 : ℚ) * X ^ 3 + C (1 / 3 : ℚ) * X ^ 1) = 6 := by
  rw [polynomialDenominator, support_binomial (by norm_num) (by norm_num) (by norm_num)]
  simp [coeff_X_pow, coeff_X, coeff_C_mul]
  decide

/-- The same sparse polynomial is not integral, detected through
`polynomialDenominator_eq_one_iff` at the coefficient of `X ^ 3`. -/
example : polynomialDenominator (C (1 / 2 : ℚ) * X ^ 3 + C (1 / 3 : ℚ) * X ^ 1) ≠ 1 := by
  rw [Ne, polynomialDenominator_eq_one_iff]
  intro h
  have h3 := h 3
  simp [coeff_X_pow, coeff_C_mul] at h3

/-- An integer polynomial has denominator `1`. -/
example : polynomialDenominator (X ^ 2 + C (3 : ℚ)) = 1 := by
  rw [polynomialDenominator_eq_one_iff]
  intro i
  rcases eq_or_ne i 2 with rfl | h2
  · simp [coeff_X_pow]
  · rcases eq_or_ne i 0 with rfl | h0
    · simp [coeff_X_pow, coeff_C]
    · simp [coeff_X_pow, coeff_C, h2, h0]

end MetaMathlibExt
