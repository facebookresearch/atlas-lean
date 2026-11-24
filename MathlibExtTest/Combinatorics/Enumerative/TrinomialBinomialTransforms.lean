/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Polynomial.Eval.Coeff
import MathlibExt.Combinatorics.Enumerative.TrinomialBinomialTransforms

open MetaMathlibExt Polynomial

-- With `m = 0` the identity says that the alternating sum of a trinomial row is `1`.
example (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1), (trinomialCoefficient n k : ℤ) * (-1) ^ k = 1 := by
  have h := sum_trinomialCoefficient_mul_choose_eq n 0
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_self, Nat.cast_one,
    mul_one] at h
  rw [← h]
  simp [trinomialCoefficient, coeff_zero_eq_eval_zero]

-- Row one and `m = 3`: the left side is `1 + 3 + 3 = 7`, the right side `1 - 4 + 10`.
example :
    ∑ k ∈ Finset.range (2 * 1 + 1), (trinomialCoefficient 1 k : ℤ) * (3 + k).choose k * (-1) ^ k =
      7 := by
  rw [← sum_trinomialCoefficient_mul_choose_eq]
  simp [Finset.sum_range_succ, trinomialCoefficient, coeff_one, coeff_X, coeff_X_pow]
