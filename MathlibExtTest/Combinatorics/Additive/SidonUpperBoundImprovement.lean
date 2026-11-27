/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonUpperBoundImprovement
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! # Tests for the maximum size of a Sidon subset of an interval -/

namespace MathlibExtTest.SidonUpperBoundImprovement

open Finset MathlibExt.Combinatorics.SidonUpperBoundImprovementGreenProblem31Wanted

-- The empty interval contributes the attainable size zero.
example : maxSidonSubsetSize 0 = 0 := by
  have hsizes : {k | ∃ A : Finset ℕ, A ⊆ Icc 1 0 ∧ (A : Set ℕ).IsSidon ∧ A.card = k} =
      {0} := by
    ext k
    simp [subset_empty, Set.IsSidon, eq_comm]
  rw [maxSidonSubsetSize, hsizes, csSup_singleton]

-- The full interval has a repeated sum, but its endpoints form a Sidon pair.
example : maxSidonSubsetSize 3 = 2 := by
  unfold maxSidonSubsetSize
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨0, ∅, empty_subset _, by simp [Set.IsSidon], card_empty⟩
    · rintro k ⟨A, hsub, hA, rfl⟩
      by_contra! hcard
      have hfull : A = Icc 1 3 := eq_of_subset_of_card_le hsub (by
        have h : (Icc 1 3 : Finset ℕ).card = 3 := by decide
        omega)
      subst A
      have hcollision := hA 1 (by decide) 3 (by decide) 2 (by decide) 2 (by decide) rfl
      simp at hcollision
  · refine le_csSup ⟨3, ?_⟩ ?_
    · rintro k ⟨A, hA, _, rfl⟩
      exact (card_le_card hA).trans (by decide)
    · refine ⟨{1, 3}, ?_, ?_, by decide⟩
      · intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl <;> decide
      · intro a ha b hb c hc d hd h
        simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb hc hd
        omega

example : ∃ c : ℝ, c < 1 ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (maxSidonSubsetSize N : ℝ) ≤ Real.sqrt N + c * (N : ℝ) ^ ((1 : ℝ) / 4) :=
  sidonUpperBoundImproved_holds

end MathlibExtTest.SidonUpperBoundImprovement
