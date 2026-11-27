/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ExponentFourBoundedGenerationKourovka13Problem10

open MathlibExt.GroupTheory.ExponentFourBoundedGenerationKourovka13Problem10Wanted

-- At bound zero the only subgroup tested is the trivial subgroup.
example {G : Type} [Group G] (S : Finset G) (hS : S.card ≤ 0) :
    ∀ g ∈ Subgroup.closure (S : Set G), g ^ 4 = 1 := by
  have h : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
  simp [h]

-- For every constant bound one can extract a generating set passing all local tests
-- and a specific element at which the identity fails.
example (m : ℕ) : ∃ (k : ℕ) (G : Type) (_ : Group G) (A : Set G),
    Subgroup.derivedSeries G k = ⊥ ∧ Subgroup.closure A = ⊤ ∧
    (∀ S : Finset G, (S : Set G) ⊆ A → S.card ≤ m →
      ∀ g ∈ Subgroup.closure (S : Set G), g ^ 4 = 1) ∧ ∃ g : G, g ^ 4 ≠ 1 := by
  classical
  by_contra! h
  apply exponentFourDetectedOnBoundedSubsets_refuted
  refine ⟨fun _ ↦ m, ?_⟩
  intro k G inst hd A hA hS
  exact h k G inst A hd hA hS
