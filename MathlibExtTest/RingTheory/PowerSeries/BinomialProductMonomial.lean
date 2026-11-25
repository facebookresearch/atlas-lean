/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.PowerSeries.BinomialProductMonomial

namespace MetaMathlibExt

open PowerSeries

/-- The degree-zero monomial acts as the identity on an arbitrary series. -/
example (A : PowerSeries ℚ) : binomialProduct 1 A = A := by
  simpa using binomialProduct_X_pow 0 A

/-- Multiplication by the outer monomial kills all coefficients below its degree. -/
example (A : PowerSeries ℚ) {n m : ℕ} (h : n < m) :
    coeff n (binomialProduct (X ^ m) A) = 0 := by
  rw [binomialProduct_X_pow, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp [Nat.not_le_of_gt h]

/-- In degree five the quadratic monomial weights the cubic coefficient by ten. -/
example (A : PowerSeries ℚ) :
    coeff 5 (binomialProduct (X ^ 2) A) = 10 * coeff 3 A := by
  rw [binomialProduct_X_pow, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
    ite_eq_left (by decide), coeff_iterate_derivative, coeff_X_pow_mul]
  norm_num [Nat.factorial, Nat.ascFactorial, ← mul_assoc]

end MetaMathlibExt
