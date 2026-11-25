/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlternatingChooseSums

/-! # Tests for alternating binomial sums -/

open Finset MetaMathlibExt

local notation "C" => (Ring.choose : ℤ → ℕ → ℤ)

-- With `m > n` and `j = n`, the negative upper index contributes a nonzero coefficient.
example : (∑ s ∈ Icc 2 5, (-1 : ℤ) ^ (s - 2) * C 2 s * C (s : ℤ) 2) = 1 ∧
    C (-1) 3 = -1 := by
  have hneg : C (-1) 3 = -1 := by
    rw [Ring.choose_neg]
    change Int.negOnePow (3 : ℕ) • C ((3 : ℕ) : ℤ) 3 = -1
    rw [Ring.choose_natCast, Nat.choose_self]
    decide
  refine ⟨((alternating_choose_sum_identities 5 2 1).1 2 (by decide)).1.trans ?_, hneg⟩
  change (-1 : ℤ) ^ 3 * C ((2 : ℕ) : ℤ) 2 * C (-1) 3 = 1
  rw [hneg, Ring.choose_natCast, Nat.choose_self]
  decide

-- Here `k > n`: both sums vanish even though some shifted upper indices are negative.
-- The final summand of the second sum also lies in the `j > k` branch.
example : (∑ j ∈ range 5, (-1 : ℤ) ^ (4 - j) * C 1 j * C (1 - j - 1) (4 - j) *
      C (1 - j) 3) = 0 ∧
    (∑ j ∈ range 5, (-1 : ℤ) ^ (4 - j) * C 1 j * C (1 - j - 1) (4 - j) *
      (if j ≤ 3 then C (1 - j) (3 - j) else 0)) = 0 := by
  have h := (alternating_choose_sum_identities 4 1 3).2
  have hz : C 1 3 = 0 := by
    change C ((1 : ℕ) : ℤ) 3 = 0
    rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by decide : 1 < 3), Nat.cast_zero]
  constructor
  · refine h.1.trans ?_
    change C 1 3 * _ = 0
    rw [hz, zero_mul]
  · refine h.2.trans ?_
    change C 1 3 * _ = 0
    rw [hz, zero_mul]

-- All upper indices in these two sums are nonnegative, and neither sum is zero.
example : (∑ s ∈ Icc 1 2, (-1 : ℤ) ^ (s - 1) * C 5 s * C (s : ℤ) 1) = -15 ∧
    (∑ j ∈ range 3, (-1 : ℤ) ^ (2 - j) * C 5 j * C (5 - j - 1) (2 - j) *
      (if j ≤ 5 then C (5 - j) (5 - j) else 0)) = 1 := by
  have h := alternating_choose_sum_identities 2 5 5
  constructor
  · refine (h.1 1 (by decide)).1.trans ?_
    change (-1 : ℤ) ^ 1 * C 5 1 * C 3 1 = -15
    rw [Ring.choose_one_right, Ring.choose_one_right]
    decide
  · refine h.2.2.trans ?_
    change C ((5 : ℕ) : ℤ) 5 * C ((2 : ℕ) : ℤ) 2 = 1
    rw [Ring.choose_natCast 5 5, Ring.choose_natCast 2 2, Nat.choose_self, Nat.choose_self,
      Nat.cast_one, one_mul]

-- The first range sum can be nonzero when its closed form has a negative upper index.
example : (∑ j ∈ range 3, (-1 : ℤ) ^ (2 - j) * C 5 j * C (5 - j - 1) (2 - j) *
    C (5 - j) 4) = 15 := by
  have h54 : C 5 4 = 5 := by
    change C ((5 : ℕ) : ℤ) 4 = 5
    rw [Ring.choose_natCast]
    decide
  have hneg : C (-2) 2 = 3 := by
    rw [Ring.choose_neg]
    change Int.negOnePow (2 : ℕ) • C ((3 : ℕ) : ℤ) 2 = 3
    rw [Ring.choose_natCast]
    decide
  refine (alternating_choose_sum_identities 2 5 4).2.1.trans ?_
  change C 5 4 * C (-2) 2 = 15
  rw [h54, hneg]
  decide
