/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.FreeEvaluation
import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily

/-!
# Whole original generator arrows under the actual presentation equivalence

The original index and original base arrow remain correlated. The complete
natural free comparison identifies the mapped family up to Arrow isomorphism,
which is the existing iso-saturated `MorphismProperty.map` operation.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC uS

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]

/-- The full original free family maps to exactly the canonical free family
closed under complete Arrow isomorphisms. -/
theorem originalGenerators_map_eq
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (L : S → PointedCGWH.{u, v} ⥤ C) (R : S → C ⥤ PointedCGWH.{u, v})
    (adj : ∀ s, L s ⊣ R s)
    (hR : ∀ s, transportedEvaluation e (j s) ≅ R s)
    (P : MorphismProperty PointedCGWH.{u, v}) :
    (MorphismProperty.adjointFamilyGenerators L P).map e.functor =
      (generators (A := A) P).isoClosure := by
  apply le_antisymm
  · rw [MorphismProperty.map_le_iff]
    intro X Y f hFamily
    rw [MorphismProperty.adjointFamilyGenerators_eq_iSup_strictMap] at hFamily
    obtain ⟨s, hs⟩ := (MorphismProperty.iSup_iff _ f).mp hFamily
    cases hs with
    | map hf =>
      apply (originalFreeGeneratorArrowClass_iff e (j s) (L s) (R s) (adj s) (hR s)
        (generators (A := A) P).isoClosure _).mpr
      exact (generators (A := A) P).le_isoClosure _
        (MorphismProperty.map_mem_adjointFamilyGenerators
          (fun a : A => EnrichedFunctorCat.Free.functor a) P (j s) _ hf)
  · rw [MorphismProperty.isoClosure_le_iff]
    intro X Y f hFamily
    change MorphismProperty.adjointFamilyGenerators
      (fun a : A => EnrichedFunctorCat.Free.functor a) P f at hFamily
    rw [MorphismProperty.adjointFamilyGenerators_eq_iSup_strictMap] at hFamily
    obtain ⟨a, ha⟩ := (MorphismProperty.iSup_iff _ f).mp hFamily
    cases ha with
    | map hf =>
      obtain ⟨s, rfl⟩ := hj a
      apply (originalFreeGeneratorArrowClass_iff e (j s) (L s) (R s) (adj s) (hR s)
        ((MorphismProperty.adjointFamilyGenerators L P).map e.functor) _).mp
      exact (MorphismProperty.adjointFamilyGenerators L P).map_mem_map e.functor _
        (MorphismProperty.map_mem_adjointFamilyGenerators L P s _ hf)

/-- The original correlated free labels retain the full canonical lifting class. -/
theorem originalGenerators_mapped_rlp_eq
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (L : S → PointedCGWH.{u, v} ⥤ C) (R : S → C ⥤ PointedCGWH.{u, v})
    (adj : ∀ s, L s ⊣ R s)
    (hR : ∀ s, transportedEvaluation e (j s) ≅ R s)
    (P : MorphismProperty PointedCGWH.{u, v}) :
    ((MorphismProperty.adjointFamilyGenerators L P).map e.functor).rlp =
      (generators (A := A) P).rlp := by
  rw [originalGenerators_map_eq e j hj L R adj hR P]
  apply le_antisymm
  · intro X Y f hf U V i hi
    exact hf i ((generators (A := A) P).le_isoClosure i hi)
  · intro X Y f hf U V i hi
    obtain ⟨U', V', i', hi', ⟨q⟩⟩ := hi
    exact (HasLiftingProperty.iff_of_arrow_iso_left q f).mp (hf i' hi')

end HomotopicalAlgebra.EnrichedProjective.NativePresentation
