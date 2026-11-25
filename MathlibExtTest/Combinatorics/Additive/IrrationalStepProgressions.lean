/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.IrrationalStepProgressions
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- At a half-integer start, take index zero for the start and index one for its double.
example : (1 / 2 : ℝ) ∉ Set.range ((↑) : ℕ → ℝ) ∧
    1 + Real.sqrt 2 ∉ Set.range ((↑) : ℕ → ℝ) := by
  have hx : (1 / 2 : ℝ) ∉ Set.range ((↑) : ℕ → ℝ) := by
    rintro ⟨n, hn⟩
    have heq : 2 * n = 1 := by
      exact_mod_cast (show 2 * (n : ℝ) = 1 by rw [hn]; norm_num)
    omega
  have h := add_mul_not_mem_nat_of_rat_of_irrational _ _ ⟨1 / 2, by norm_num⟩ hx
    irrational_sqrt_two 0 1 le_rfl
  norm_num at h ⊢
  exact h

-- At index zero the doubled start is a nonnegative integer.
example : 2 * (1 / 2 : ℝ) + 0 * Real.sqrt 2 ∈ Set.range ((↑) : ℕ → ℝ) :=
  ⟨1, by norm_num⟩

-- The smallest allowed interval, progression length, and gap. Here `2 + 2 = 0 + 4`
-- belongs to two different types of sums, so simply adding their cardinalities is not exact.
example : ¬ IsMSTDSet (realIntervalSet 3 ∪ realAPSet 4 2 (Real.sqrt 2)) :=
  not_isMSTDSet_intervalAP_irrational_diff 3 2 4 (Real.sqrt 2) (by decide) (by decide)
    irrational_sqrt_two (Real.sqrt_pos.2 (by norm_num)) (by decide)

-- With a larger gap the two constant terms in the count are separated.
example : ¬ IsMSTDSet (realIntervalSet 4 ∪ realAPSet 8 3 (Real.sqrt 2)) :=
  not_isMSTDSet_intervalAP_irrational_diff 4 3 8 (Real.sqrt 2) (by decide) (by decide)
    irrational_sqrt_two (Real.sqrt_pos.2 (by norm_num)) (by decide)
