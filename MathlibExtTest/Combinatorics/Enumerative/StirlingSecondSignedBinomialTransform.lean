/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingSecondSignedBinomialTransform

open scoped BigOperators
open Finset MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

-- This includes n = m = 0, where the power of zero in the summand has exponent zero.
example (n : ℕ) :
    (∑ k ∈ Icc n n, (Nat.choose n k : ℤ) * (Nat.stirlingSecond k n : ℤ) *
      (n : ℤ) ^ (n - k) * (-1 : ℤ) ^ (k - n)) = 1 := by
  calc
    _ = (Nat.stirlingSecond n n : ℤ) := (stirlingSecond_eq_sum_choose_pow (le_refl n)).symm
    _ = 1 := by simp [Nat.stirlingSecond_self]

-- In column zero with a positive row index, the expansion vanishes.
example (n : ℕ) :
    (∑ k ∈ Icc 0 (n + 1), (Nat.choose (n + 1) k : ℤ) * (Nat.stirlingSecond k 0 : ℤ) *
      (0 : ℤ) ^ (n + 1 - k) * (-1 : ℤ) ^ (k - 0)) = 0 := by
  simpa using (stirlingSecond_eq_sum_choose_pow (Nat.zero_le (n + 1))).symm

-- The middle summand is negative: the three terms are 24, -24, and 7.
example : (Nat.stirlingSecond 4 2 : ℤ) = 7 := by
  calc
    _ = ∑ k ∈ Icc 2 4, (Nat.choose 4 k : ℤ) * (Nat.stirlingSecond k 2 : ℤ) *
          (2 : ℤ) ^ (4 - k) * (-1 : ℤ) ^ (k - 2) :=
      stirlingSecond_eq_sum_choose_pow (by decide : 2 ≤ 4)
    _ = 7 := by decide
