/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TrinomialEvenAlternating

open MetaMathlibExt

example :
    ∑ k ∈ Finset.range (0 + 1),
        (trinomialCoefficient (2 * 0 - 2 * k) 0 : ℤ) * (0 : ℕ).choose k * (-1) ^ k = 1 := by
  simpa using sum_trinomialCoefficient_two_mul_sub (n := 0)

example :
    ∑ k ∈ Finset.range (1 + 1),
        (trinomialCoefficient (2 * 1 - 2 * k) 1 : ℤ) * (1 : ℕ).choose k * (-1) ^ k = 2 := by
  simpa using sum_trinomialCoefficient_two_mul_sub (n := 1)

-- At n = 4 the summands for k = 1 and k = 3 both contribute negative terms.
example :
    ∑ k ∈ Finset.range (4 + 1),
        (trinomialCoefficient (2 * 4 - 2 * k) 4 : ℤ) * (4 : ℕ).choose k * (-1) ^ k = 16 := by
  simpa using sum_trinomialCoefficient_two_mul_sub (n := 4)
