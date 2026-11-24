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
