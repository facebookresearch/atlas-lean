/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PowerSumRisingStirling

open Finset MetaMathlibExt

-- The empty interval gives zero for every exponent, including zero.
example (m : ℕ) :
    (∑ j ∈ range (m + 1),
      (-1 : ℤ) ^ (m - j) * (j.factorial : ℤ) * ((0 + j).choose (j + 1) : ℤ) *
        (Nat.stirlingSecond m j : ℤ)) = 0 := by
  rw [← sum_pow_eq_sum_stirlingSecond]
  simp

-- At exponent zero the sum counts the n terms.
example (n : ℕ) :
    (∑ j ∈ range (0 + 1),
      (-1 : ℤ) ^ (0 - j) * (j.factorial : ℤ) * ((n + j).choose (j + 1) : ℤ) *
        (Nat.stirlingSecond 0 j : ℤ)) = n := by
  rw [← sum_pow_eq_sum_stirlingSecond]
  simp

-- The square and cube cases exercise cancellation between nonzero coefficients.
example : (∑ k ∈ Icc (1 : ℕ) 3, (k : ℤ) ^ 2) = 14 := by
  rw [sum_pow_eq_sum_stirlingSecond]
  decide

example : (∑ k ∈ Icc (1 : ℕ) 4, (k : ℤ) ^ 3) = 100 := by
  rw [sum_pow_eq_sum_stirlingSecond]
  decide
