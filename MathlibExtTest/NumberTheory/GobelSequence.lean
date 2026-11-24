/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelSequence
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- At k = 0 the exponent in the recurrence truncates to zero.
example : gobelSequence 0 7 0 = 0 ∧ gobelSequence 0 7 2 = 7 := by
  norm_num [gobelSequence]

example : ratResidue 5 (1 / 2) = 3 := by decide +kernel

-- Start from exact equality at index 3 and propagate to the last index below 5.
example : 2 ≤ padicValRat 5 (4 * gobelSequence 2 2 4 - 15) := by
  have h := gobelSequence_mul_index_congr 5 (by decide) 2 2 2 3 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inl (by norm_num [gobelSequence])) 4 (by decide) (by decide)
  norm_num at h
  exact h.resolve_left (by norm_num [gobelSequence])

-- A zero residue can start from a nonzero multiple of the full prime power.
example : 2 ≤ padicValRat 3 (2 * gobelSequence 2 9 2) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hstart : 2 ≤ padicValRat 3 (((3 : ℕ) : ℚ) ^ 2) := by
    rw [padicValRat.pow, padicValRat.self (by decide : 1 < 3)]
    decide
  have h := gobelSequence_mul_index_congr 3 (by decide) 2 9 2 1 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inr (by norm_num [gobelSequence] at hstart ⊢; exact hstart)) 2 (by decide) (by decide)
  norm_num at h
  exact h.resolve_left (by norm_num [gobelSequence])
