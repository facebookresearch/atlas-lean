/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.TorsionFreeQuasivarietyPresentationKourovka18Problem17
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

open MathlibExt.GroupTheory.TorsionFreeQuasivarietyPresentationKourovka18Problem17Wanted

private theorem noRelations (n : ℕ) :
    torsionFreeRelations (∅ : Set (FreeGroup (Fin n))) = ⊥ := by
  refine le_antisymm (sInf_le ?_) bot_le
  refine ⟨inferInstance, Set.empty_subset _, ?_⟩
  intro x k hk hx
  exact (pow_eq_one_iff_left hk.ne').1 hx

-- With an empty set of relations, the free group on two generators presents itself.
example : IsTorsionFreeFinitelyPresented (FreeGroup (Fin 2)) := by
  refine ⟨2, ∅, MonoidHom.id _, Function.surjective_id, ?_⟩
  simp [noRelations]

-- Imposing only the square of the generator kills the generator in the torsion-free closure.
example : torsionFreeRelations ({(FreeGroup.of (0 : Fin 1)) ^ 2} : Set _) = ⊤ := by
  apply top_unique
  rw [← FreeGroup.closure_range_of (Fin 1), Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change FreeGroup.of (0 : Fin 1) ∈ torsionFreeRelations _
  rw [torsionFreeRelations, Subgroup.mem_sInf]
  intro N hN
  exact hN.2.2 _ 2 (by decide) (hN.2.1 (Set.mem_singleton _))
