/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.PartitionRegularUltrafilter

/-! # Tests for partition regular families and ultrafilters -/

open Filter MetaMathlibExt

-- On the empty type the zero-color coloring rules out a witness for every family.
example (𝓕 : Set (Set Empty)) : ¬ ∃ U : Ultrafilter Empty, ∀ A ∈ U, ∃ F ∈ 𝓕, F ⊆ A := by
  intro h
  obtain ⟨_, _, k, _⟩ := (weaklyPartitionRegular_iff_exists_ultrafilter 𝓕).2 h 0 Empty.elim
  exact Fin.elim0 k

-- On an inhabited type even the family consisting solely of the empty set has a witness.
example {S : Type*} (s : S) :
    ∃ U : Ultrafilter S, ∀ A ∈ U, ∃ F ∈ ({∅} : Set (Set S)), F ⊆ A := by
  apply (weaklyPartitionRegular_iff_exists_ultrafilter _).1
  exact fun _ c => ⟨∅, rfl, c s, fun _ hx => hx.elim⟩

-- Extending the cofinite filter gives an infinite monochromatic set in every coloring of ℕ.
example (r : ℕ) (c : ℕ → Fin r) : ∃ F : Set ℕ, F.Infinite ∧ ∃ k, ∀ x ∈ F, c x = k := by
  apply (weaklyPartitionRegular_iff_exists_ultrafilter {F : Set ℕ | F.Infinite}).2 _ r c
  exact ⟨hyperfilter ℕ, fun A hA => ⟨A, fun hf => hf.notMem_hyperfilter hA, Set.Subset.rfl⟩⟩
