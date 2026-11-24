/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TrinomialAlternatingColumn

open MetaMathlibExt

-- At the first allowed column, the alternating sum is the constant coefficient of (1 + X) ^ n.
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient (n - k) n : ℤ) * n.choose k * (-1) ^ k =
      1 := by
  rw [sum_trinomialCoefficient_sub_mul_choose n n le_rfl]
  simp

-- Beyond column 2n the shifted binomial coefficient vanishes.
example (n m : ℕ) (hm : 2 * n < m) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient (n - k) m : ℤ) * n.choose k * (-1) ^ k =
      0 := by
  rw [sum_trinomialCoefficient_sub_mul_choose n m (by omega),
    Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
