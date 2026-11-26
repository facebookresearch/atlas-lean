/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.NilpotentFormationLatticeDistributiveKourovka10Problem56

open MathlibExt.GroupTheory.NilpotentFormationLatticeDistributiveKourovka10Problem56Wanted

-- Generating from a single formation recovers it.
example (A : GroupClass) (hA : IsFormation A) (G : Type) [Group G] [Finite G] :
    formationJoin A A G ↔ A G :=
  ⟨fun h ↦ h A hA (fun _ _ _ hG ↦ hG) (fun _ _ _ hG ↦ hG),
   fun h _ _ incl _ ↦ incl G h⟩

-- The refutation gives a witness in the left side of the law, since the reverse
-- inclusion holds in every formation lattice.
example : ∃ A B C : GroupClass, IsNilpotentClassFourFormation A ∧
    IsNilpotentClassFourFormation B ∧ IsNilpotentClassFourFormation C ∧
    ∃ (G : Type) (_ : Group G) (_ : Finite G),
      A G ∧ formationJoin B C G ∧ ¬ formationJoin (meet A B) (meet A C) G := by
  by_contra h
  apply nilpotentClassFourFormationsDistributive_refuted
  intro A B C hA hB hC G _ _
  constructor
  · rintro ⟨ha, hjoin⟩
    by_contra hr
    exact h ⟨A, B, C, hA, hB, hC, G, inferInstance, inferInstance, ha, hjoin, hr⟩
  · intro hr
    refine ⟨hr A hA.1 (fun _ _ _ h ↦ h.1) (fun _ _ _ h ↦ h.1), ?_⟩
    intro Z hZ inclB inclC
    exact hr Z hZ (fun H _ _ h ↦ inclB H h.2) (fun H _ _ h ↦ inclC H h.2)
