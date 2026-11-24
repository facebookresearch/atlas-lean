/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.HockeyStick

/-! # Tests for the generalized hockey stick identity -/

open Finset MathlibExt.Combinatorics.HockeyStickWanted

-- At the first even cutoff with a negative term, its lower index is zero.
example (n : ℕ) :
    (∑ i ∈ range 3, ((2 * i + n).choose i : ℤ)) = ((5 + n).choose 2 : ℤ) - 1 := by
  rw [sum_choose_two_mul_add n 2]
  simp [sum_range_succ, sub_eq_add_neg]

-- At the next odd cutoff there are still two terms, but the negative term has lower index one.
example (n : ℕ) :
    (∑ i ∈ range 4, ((2 * i + n).choose i : ℤ)) = ((7 + n).choose 3 : ℤ) - (6 + n : ℕ) := by
  rw [sum_choose_two_mul_add n 3]
  simp [sum_range_succ, sub_eq_add_neg, Nat.add_comm 7 n, Nat.add_comm 6 n]
