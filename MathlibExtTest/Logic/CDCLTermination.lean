/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.CDCLTermination
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Boundary check: one decide step from the empty state strictly
decreases the potential (here `0 < 1`). -/
example : (0 * (1 + 1) + (1 - 1) : ℕ) < (0 * (1 + 1) + (1 - 0) : ℕ) := by
  have h := cdcl_step_potential_decreases (F := ∅) ({0} : Finset ℕ) ∅
    (s₁ := ([], ∅)) (s₂ := ([(0, true)], ∅))
    (CDCLStep.decide [] ∅ (0, true) (by simp) (by simp))
    (by intro l hl; simp at hl)
    (by simp)
    (by intro C hC; simp at hC)
    (by intro l hl; simp at hl; subst hl; simp)
    (by intro C hC; simp at hC)
  simpa using h
