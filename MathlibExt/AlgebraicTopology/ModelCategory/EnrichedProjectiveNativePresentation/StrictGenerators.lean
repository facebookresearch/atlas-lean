/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.StrictFree

/-!
# Whole original generator families in the actual strict source presentation

The same original source label and pointed generating arrow remain
correlated under the actual source equivalence. Its whole free comparison
identifies precisely the strict native family up to full Arrow isomorphism.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC uS

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed ZeroObject CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]

/-- All original correlated free labels map onto precisely the whole strict native family. -/
theorem strictSourceGenerators_map_eq
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (L : S → PointedCGWH.{u, v} ⥤ C) (R : S → C ⥤ PointedCGWH.{u, v})
    (adj : ∀ s, L s ⊣ R s)
    (hR : ∀ s, transportedEvaluation e (j s) ≅ R s)
    (P : MorphismProperty PointedCGWH.{u, v}) :
    (MorphismProperty.adjointFamilyGenerators L P).map (strictSourceEquivalence e).functor =
      (MorphismProperty.adjointFamilyGenerators
        (BasedNativePresentation.strictFreeAt (A := A)) P).isoClosure := by
  apply le_antisymm
  · rw [MorphismProperty.map_le_iff]
    intro X Y f hFamily
    rw [MorphismProperty.adjointFamilyGenerators_eq_iSup_strictMap] at hFamily
    obtain ⟨s, hs⟩ := (MorphismProperty.iSup_iff _ f).mp hFamily
    cases hs with
    | map hf =>
      apply (strictSourceFreeArrowClass_iff e (j s) (L s) (R s) (adj s) (hR s)
        (MorphismProperty.adjointFamilyGenerators
          (BasedNativePresentation.strictFreeAt (A := A)) P).isoClosure _).mpr
      exact (MorphismProperty.adjointFamilyGenerators
        (BasedNativePresentation.strictFreeAt (A := A)) P).le_isoClosure _
          (MorphismProperty.map_mem_adjointFamilyGenerators
            (BasedNativePresentation.strictFreeAt (A := A)) P (j s) _ hf)
  · rw [MorphismProperty.isoClosure_le_iff]
    intro X Y f hFamily
    rw [MorphismProperty.adjointFamilyGenerators_eq_iSup_strictMap] at hFamily
    obtain ⟨a, ha⟩ := (MorphismProperty.iSup_iff _ f).mp hFamily
    cases ha with
    | map hf =>
      obtain ⟨s, rfl⟩ := hj a
      apply (strictSourceFreeArrowClass_iff e (j s) (L s) (R s) (adj s) (hR s)
        ((MorphismProperty.adjointFamilyGenerators L P).map
          (strictSourceEquivalence e).functor) _).mp
      exact (MorphismProperty.adjointFamilyGenerators L P).map_mem_map
        (strictSourceEquivalence e).functor _
          (MorphismProperty.map_mem_adjointFamilyGenerators L P s _ hf)

/-- The full mapped original generator lifting class is the strict native lifting class. -/
theorem strictSourceGenerators_mapped_rlp_eq
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (L : S → PointedCGWH.{u, v} ⥤ C) (R : S → C ⥤ PointedCGWH.{u, v})
    (adj : ∀ s, L s ⊣ R s)
    (hR : ∀ s, transportedEvaluation e (j s) ≅ R s)
    (P : MorphismProperty PointedCGWH.{u, v}) :
    ((MorphismProperty.adjointFamilyGenerators L P).map
      (strictSourceEquivalence e).functor).rlp =
        (MorphismProperty.adjointFamilyGenerators
          (BasedNativePresentation.strictFreeAt (A := A)) P).rlp := by
  rw [strictSourceGenerators_map_eq e j hj L R adj hR P]
  apply le_antisymm
  · intro X Y f hf U V i hi
    exact hf i ((MorphismProperty.adjointFamilyGenerators
      (BasedNativePresentation.strictFreeAt (A := A)) P).le_isoClosure i hi)
  · intro X Y f hf U V i hi
    obtain ⟨U', V', i', hi', ⟨q⟩⟩ := hi
    exact (HasLiftingProperty.iff_of_arrow_iso_left q f).mp (hf i' hi')

end HomotopicalAlgebra.EnrichedProjective.NativePresentation
