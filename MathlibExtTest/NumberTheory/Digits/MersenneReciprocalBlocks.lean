/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.MersenneReciprocalBlocks
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for the decimal-block recurrence for Mersenne reciprocals -/

open MetaMathlibExt

-- `1/7 = 0.(142857)`: with `r = s = 1`, the direct recurrence doubles,
-- adds the final carry, and wraps back to the first block.
example : (28 : ℤ) = 2 * 14 ∧ (57 : ℤ) = 2 * 28 + 1 ∧
    (14 : ℤ) = 2 * 57 - 100 ∧ (14 : ℤ) + 28 + 57 = 99 := by
  have hord : orderOf (10 : ZMod (2 ^ 3 - 1)) = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  have h := mersenne_reciprocal_block_recurrence 3 (by norm_num)
    (by rw [hord]; decide) 1 1 (by decide) (by decide) (by rw [hord]; decide) (by decide)
  rw [hord] at h
  exact ⟨h.2.1 rfl 1 (by decide), h.2.1 rfl 2 (by decide),
    h.2.1 rfl 3 (by decide), h.2.2⟩

-- `1/31 = 0.(032258064516129)`: `r = 3` and `s = 2` reorder the blocks
-- as `032, 064, 129, 258, 516`. The carry occurs at `k = p - r = 2`.
example : (64 : ℤ) = 2 * 32 ∧ (129 : ℤ) = 2 * 64 + 1 ∧ (258 : ℤ) = 2 * 129 ∧
    (516 : ℤ) = 2 * 258 ∧ (32 : ℤ) = 2 * 516 - 1000 ∧ (32 : ℤ) + 258 + 64 + 516 + 129 = 999 := by
  have hord : orderOf (10 : ZMod (2 ^ 5 - 1)) = 15 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  have h := mersenne_reciprocal_block_recurrence 5 (by norm_num)
    (by rw [hord]; decide) 3 2 (by decide) (by decide) (by rw [hord]; decide) (by decide)
  rw [hord] at h
  exact ⟨h.1 1 (by decide), h.1 2 (by decide), h.1 3 (by decide),
    h.1 4 (by decide), h.1 5 (by decide), h.2.2⟩
