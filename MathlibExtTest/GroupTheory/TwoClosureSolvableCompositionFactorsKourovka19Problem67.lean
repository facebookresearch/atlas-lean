/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import MathlibExt.GroupTheory.TwoClosureSolvableCompositionFactorsKourovka19Problem67

open MathlibExt.GroupTheory.TwoClosureSolvableCompositionFactorsKourovka19Problem67Wanted

-- Fixing the orbits of the trivial group forces every point to be fixed.
example : twoClosure (⊥ : Subgroup (Equiv.Perm (Fin 4))) = ⊥ := by
  rw [twoClosure, Subgroup.closure_eq_bot_iff]
  intro σ hσ
  change ∀ a b, ∃ g ∈ (⊥ : Subgroup (Equiv.Perm (Fin 4))), g a = σ a ∧ g b = σ b at hσ
  apply Set.mem_singleton_iff.mpr
  apply Equiv.ext
  intro a
  obtain ⟨g, hg, ha, -⟩ := hσ a a
  rw [Subgroup.mem_bot.mp hg] at ha
  exact ha.symm

-- The degree-four alternating group has both of the symmetric group's pair orbits.
example : twoClosure (alternatingGroup (Fin 4)) = ⊤ := by
  have htrans : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 4)) (Fin 4) 2 := by
    simpa using alternatingGroup.isMultiplyPretransitive (Fin 4)
  refine top_unique fun σ _ ↦ Subgroup.subset_closure ?_
  change ∀ a b, ∃ g ∈ alternatingGroup (Fin 4), g a = σ a ∧ g b = σ b
  intro a b
  rcases eq_or_ne a b with rfl | hab
  · have : MulAction.IsPretransitive (alternatingGroup (Fin 4)) (Fin 4) :=
      MulAction.isPretransitive_of_is_two_pretransitive
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 4)) a (σ a)
    exact ⟨g.val, g.property, hg, hg⟩
  · obtain ⟨g, ha, hb⟩ := MulAction.is_two_pretransitive_iff.mp htrans hab (σ.injective.ne hab)
    exact ⟨g.val, g.property, ha, hb⟩
