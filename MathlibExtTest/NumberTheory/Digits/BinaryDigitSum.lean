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

-- Zero is the boundary case of the evenness hypothesis: its successor one has a single one-bit.
example : (Nat.digits 2 1).sum = (Nat.digits 2 0).sum + 1 :=
  hammingWeight_succ_of_even 0 Even.zero

-- Setting the lowest bit of six, `110₂`, gives seven, `111₂`.
example : (Nat.digits 2 7).sum = 3 :=
  hammingWeight_succ_of_even 6 (by decide)

-- One, the least odd number, drops to zero, whose digit list is empty.
example : (Nat.digits 2 0).sum = 0 :=
  hammingWeight_pred_of_odd 1 odd_one

-- Clearing the lowest bit of nine, `1001₂`, leaves eight, `1000₂`.
example : (Nat.digits 2 8).sum = 1 :=
  hammingWeight_pred_of_odd 9 (by decide)

-- The least admissible exponent is two, with `r = 1`: `4 - 1 = 3 = 11₂`.
example : (Nat.digits 2 3).sum = 2 :=
  hammingWeight_two_pow_sub_of_odd 2 1 odd_one (by decide)

-- The largest admissible `r` for `k = 4` is seven, `111₂`: `16 - 7 = 9 = 1001₂`.
example : (Nat.digits 2 9).sum = 2 :=
  hammingWeight_two_pow_sub_of_odd 4 7 (by decide) (by decide)

-- With `r = 1`, the all-ones number `2 ^ k - 1` has `k` one-bits.
example (k : ℕ) (hk : 2 ≤ k) : (Nat.digits 2 (2 ^ k - 1)).sum = k := by
  have hr : 2 * 1 < 2 ^ k := lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right two_pos hk)
  simpa using hammingWeight_two_pow_sub_of_odd k 1 odd_one hr
