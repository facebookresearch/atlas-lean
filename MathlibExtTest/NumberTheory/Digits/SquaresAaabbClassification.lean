/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.SquaresAaabbClassification
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Tests for squares with two blocks of repeated decimal digits

The classification implies that every such square greater than 7744 is divisible by ten.
-/

namespace MathlibExtTest.NumberTheory.Digits.SquaresAaabbClassification

private theorem large_square_divisible_by_ten (n : ℕ) (hn : IsSquare n)
    (h : ∃ a b r s : ℕ, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ 1 ≤ r ∧ 1 ≤ s ∧
      Nat.digits 10 n = List.replicate s b ++ List.replicate r a)
    (hlarge : 7744 < n) : 10 ∣ n := by
  have hc := MetaMathlibExt.squares_aaabb_classification n hn h
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  all_goals first
    | omega
    | cases i with
      | zero => norm_num at hlarge
      | succ i =>
        have hp : 10 ∣ 10 ^ (2 * (i + 1)) := by
          refine ⟨10 ^ (2 * i + 1), ?_⟩
          rw [(by omega : 2 * (i + 1) = (2 * i + 1) + 1), pow_succ]
          ring
        first
          | exact hp
          | exact dvd_mul_of_dvd_right hp 4
          | exact dvd_mul_of_dvd_right hp 9

example : 10 ∣ 10000 :=
  large_square_divisible_by_ten 10000 ⟨100, rfl⟩
    ⟨1, 0, 1, 4, by decide +kernel⟩ (by decide)

example (n : ℕ) (hn : IsSquare n)
    (h : ∃ a b r s : ℕ, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ 1 ≤ r ∧ 1 ≤ s ∧
      Nat.digits 10 n = List.replicate s b ++ List.replicate r a)
    (hunit : n % 10 ≠ 0) : n ≤ 7744 := by
  by_contra! hlarge
  exact hunit (Nat.mod_eq_zero_of_dvd (large_square_divisible_by_ten n hn h hlarge))

end MathlibExtTest.NumberTheory.Digits.SquaresAaabbClassification
