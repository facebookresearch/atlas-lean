/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosProblem845
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Tests for the ratio bound in Erdős Problem 845 -/

namespace MathlibExt.NumberTheory.ErdosProblem845Wanted

private abbrev termValue (x : ℕ × ℕ) : ℕ := 2 ^ x.1 * 3 ^ x.2

private def sums (C : ℝ) : Set ℕ :=
  { ∑ x ∈ B, termValue x | (B : Finset (ℕ × ℕ)) (h : B.Nonempty)
    (_ : B.sup termValue ≤ C * B.inf' h termValue) }

-- The non-strict comparison includes the representation 5 = 2 + 3 at the endpoint 3/2.
example : 5 ∈ sums (3 / 2) := by
  refine ⟨{(1, 0), (0, 1)}, by decide, ?_, by decide⟩
  norm_num [Finset.sup_insert, Finset.inf'_insert, termValue]

-- Nonempty sums of positive terms force every counterexample to have ratio bound at least one.
example : ∃ C : ℝ, 1 ≤ C ∧ ¬ (sums C).HasDensity 0 := by
  by_contra! hall
  apply conjecture_refuted
  intro C hC
  change (sums C).HasDensity 0
  by_cases h : 1 ≤ C
  · exact hall C h
  have hempty : sums C = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨B, hB, hratio, rfl⟩
    obtain ⟨x, hx⟩ := hB
    have hpos : 0 < B.inf' ⟨x, hx⟩ termValue := by
      change 1 ≤ B.inf' _ _
      apply Finset.le_inf'
      intro y _
      change 0 < 2 ^ y.1 * 3 ^ y.2
      positivity
    have hle := (Finset.inf'_le termValue hx).trans (Finset.le_sup hx (f := termValue))
    have hlt : C * (B.inf' ⟨x, hx⟩ termValue : ℕ) < B.inf' ⟨x, hx⟩ termValue := by
      exact mul_lt_of_lt_one_left (by exact_mod_cast hpos) (lt_of_not_ge h)
    exact hlt.not_ge (le_trans (by exact_mod_cast hle) hratio)
  rw [hempty]
  exact Set.HasDensity.empty

end MathlibExt.NumberTheory.ErdosProblem845Wanted
