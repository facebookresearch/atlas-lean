/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.StronglyMaximalMatchingAMR29Problem0084
import Mathlib.SetTheory.Cardinal.Basic

namespace MathlibExt.Combinatorics.StronglyMaximalMatchingAMR29Problem0084Wanted.Tests

-- The empty set is a matching of every hypergraph.
example (E : Set (Finset ℕ)) : IsMatching E ∅ := by
  exact ⟨Set.empty_subset E, by simp⟩

-- Two disjoint singleton edges form a matching, and taking both is strongly maximal:
-- every other matching is contained in it, so it loses nothing.
example : IsStronglyMaximal ({{0}, {1}} : Set (Finset ℕ)) {{0}, {1}} := by
  refine ⟨⟨by simp, ?_⟩, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Finset.disjoint_singleton_left.mpr (by decide)
    · exact (Finset.disjoint_singleton_left.mpr (by decide)).symm
    · exact absurd rfl hab
  · intro M' hM'
    have hempty : M' \ {{0}, {1}} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      exact hx.2 (hM'.1 hx.1)
    rw [hempty]
    simp

-- Overlapping edges do not form a matching.
example : ¬ IsMatching ({{0}, {0, 1}} : Set (Finset ℕ)) {{0}, {0, 1}} := by
  intro h
  have hp := h.2
  have hdis : Disjoint ({0} : Finset ℕ) ({0, 1} : Finset ℕ) :=
    hp (show ({0} : Finset ℕ) ∈ ({{0}, {0, 1}} : Set (Finset ℕ)) by simp)
      (show ({0, 1} : Finset ℕ) ∈ ({{0}, {0, 1}} : Set (Finset ℕ)) by simp)
      (by decide)
  exact Finset.disjoint_left.mp hdis (by decide : (0 : ℕ) ∈ ({0} : Finset ℕ))
    (by decide : (0 : ℕ) ∈ ({0, 1} : Finset ℕ))

-- The empty hypergraph has the empty strongly maximal matching.
example : IsStronglyMaximal (∅ : Set (Finset ℕ)) ∅ := by
  refine ⟨⟨by simp, by simp⟩, fun X h ↦ ?_⟩
  have hX : X = ∅ := Set.eq_empty_of_subset_empty h.1
  rw [hX]

-- The proved refutation, restated: bounded edge size does not guarantee a strongly
-- maximal matching.
example : ¬ boundedEdgesStronglyMaximalMatching :=
  boundedEdgesStronglyMaximalMatching_refuted

end MathlibExt.Combinatorics.StronglyMaximalMatchingAMR29Problem0084Wanted.Tests
