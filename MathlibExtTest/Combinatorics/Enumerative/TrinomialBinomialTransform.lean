/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TrinomialBinomialTransform
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

-- The zero row has only a constant term.
example : (∑ k ∈ Finset.range (3 + 1), (trinomialCoefficient 0 k : ℤ) * (3 : ℕ).choose k) = 1 := by
  rw [sum_trinomialCoefficient_mul_choose_eq]
  norm_num [Finset.sum_range_succ, trinomialCoefficient_zero_zero]

-- Column zero gives the alternating row sum.
example : (∑ k ∈ Finset.range (2 * 1 + 1), (trinomialCoefficient 1 k : ℤ) *
    (0 + k).choose k * (-1) ^ k) = 1 := by
  rw [← sum_trinomialCoefficient_mul_choose_eq]
  norm_num [Finset.sum_range_succ, trinomialCoefficient, Polynomial.coeff_add,
    Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]

-- For n = m = 2 the signed terms are 1, -6, 18, -20, 15.
example : (∑ k ∈ Finset.range (2 + 1), (trinomialCoefficient 2 k : ℤ) * (2 : ℕ).choose k) = 8 := by
  rw [sum_trinomialCoefficient_mul_choose_eq]
  norm_num [Finset.sum_range_succ, Nat.choose, trinomialCoefficient]
  ring_nf
  norm_num [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
    Polynomial.coeff_X_pow]

end MetaMathlibExt
