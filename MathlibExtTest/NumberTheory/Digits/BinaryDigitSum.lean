/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BinaryDigitSum

/-! # Tests for binary digit sums -/

open Finset MetaMathlibExt

-- The lower summand can have an empty digit list, including at exponent zero.
example (k : ℕ) : (Nat.digits 2 (2 ^ k)).sum = 1 := by
  simpa using hammingWeight_two_pow_add k 0 (Nat.two_pow_pos k)

-- All three lower bits are set just below the strict upper bound.
example : (Nat.digits 2 15).sum = 4 :=
  hammingWeight_two_pow_add 3 7 (by decide)

-- At exponent zero the range contains just zero, whose digit list is empty.
example : ∑ i ∈ range 1, (Nat.digits 2 i).sum = 0 := by
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  exact two_mul_sum_hammingWeight_range_two_pow 0

-- The binary expansions of the eight numbers below eight contain twelve ones.
example : ∑ i ∈ range 8, (Nat.digits 2 i).sum = 12 := by
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  exact two_mul_sum_hammingWeight_range_two_pow 3
