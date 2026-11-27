/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Equivalence
import MathlibExt.CategoryTheory.SmallObject.IsoEligibility

/-!
# Literal indexed Free families through actual functor isomorphisms

The original source labels and base arrows remain literal. Whole natural
isomorphisms compare their arrows with the target family sent by the given
inverse. The original cardinal transfer and small-family isomorphism theorem
provide all six eligibility fields without choosing another cardinal.
-/

set_option autoImplicit false
noncomputable section
universe w uV vV uC vC uD vD uS uA
open CategoryTheory Limits Opposite HomotopicalAlgebra

namespace CategoryTheory.MorphismProperty

variable {V : Type uV} [Category.{vV} V]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {S : Type uS} {A : Type uA}

/-- Actual whole functor isomorphisms retain the original labelled inverse-family arrows. -/
theorem adjointFamilyGenerators_le_strictMap_isoClosure
    (e : C ≌ D) (K : S → V ⥤ C) (L : A → V ⥤ D) (j : S → A)
    (q : ∀ s, K s ≅ L (j s) ⋙ e.inverse) (P : MorphismProperty V) :
    adjointFamilyGenerators K P ≤
      ((adjointFamilyGenerators L P).strictMap e.inverse).isoClosure := by
  rintro X Y f ⟨pair⟩
  refine ⟨_, _, e.inverse.map ((L (j pair.1)).map pair.2.1.hom), ?_, ?_⟩
  · exact map_mem_strictMap _ _ _
      (map_mem_adjointFamilyGenerators L P (j pair.1) pair.2.1.hom pair.2.2)
  · exact ⟨(Arrow.isoOfNatIso (q pair.1) (Arrow.mk pair.2.1.hom)).symm⟩

/-- Surjective actual labels identify both complete original isomorphism saturations. -/
theorem adjointFamilyGenerators_isoClosure_eq_strictMap
    (e : C ≌ D) (K : S → V ⥤ C) (L : A → V ⥤ D) (j : S → A)
    (hj : Function.Surjective j) (q : ∀ s, K s ≅ L (j s) ⋙ e.inverse)
    (P : MorphismProperty V) :
    (adjointFamilyGenerators K P).isoClosure =
      ((adjointFamilyGenerators L P).strictMap e.inverse).isoClosure := by
  apply le_antisymm
  · exact (isoClosure_le_iff _ _).mpr
      (adjointFamilyGenerators_le_strictMap_isoClosure e K L j q P)
  · rintro X Y f ⟨X', Y', g, hg, ⟨iso⟩⟩
    cases hg with
    | map hTarget =>
      rcases hTarget with ⟨pair⟩
      obtain ⟨s, hs⟩ := hj pair.1
      have qs : K s ≅ L pair.1 ⋙ e.inverse := hs ▸ q s
      refine ⟨_, _, (K s).map pair.2.1.hom, ?_, ?_⟩
      · exact map_mem_adjointFamilyGenerators K P s pair.2.1.hom pair.2.2
      · exact ⟨Arrow.isoOfNatIso qs (Arrow.mk pair.2.1.hom) ≪≫ iso⟩

/-- Both complete right lifting classes retain the actual surjective source comparison. -/
theorem adjointFamilyGenerators_rlp_eq_strictMap
    (e : C ≌ D) (K : S → V ⥤ C) (L : A → V ⥤ D) (j : S → A)
    (hj : Function.Surjective j) (q : ∀ s, K s ≅ L (j s) ⋙ e.inverse)
    (P : MorphismProperty V) :
    (adjointFamilyGenerators K P).rlp =
      ((adjointFamilyGenerators L P).strictMap e.inverse).rlp := by
  have h := adjointFamilyGenerators_isoClosure_eq_strictMap e K L j hj q P
  ext X Y f
  constructor
  · intro hf U W i hi
    have hi' : (adjointFamilyGenerators K P).isoClosure i :=
      h.symm ▸ ((adjointFamilyGenerators L P).strictMap e.inverse).le_isoClosure i hi
    obtain ⟨U', W', i', hi', ⟨iso⟩⟩ := hi'
    exact (HasLiftingProperty.iff_of_arrow_iso_left iso f).mp (hf i' hi')
  · intro hf U W i hi
    have hi' : ((adjointFamilyGenerators L P).strictMap e.inverse).isoClosure i :=
      h ▸ (adjointFamilyGenerators K P).le_isoClosure i hi
    obtain ⟨U', W', i', hi', ⟨iso⟩⟩ := hi'
    exact (HasLiftingProperty.iff_of_arrow_iso_left iso f).mp (hf i' hi')

/-- All six source fields follow at the original cardinal from actual small source labels. -/
theorem adjointFamilyGenerators_isCardinalForSmallObjectArgument_of_equivalence
    (e : C ≌ D) (K : S → V ⥤ C) (L : A → V ⥤ D) (j : S → A)
    (q : ∀ s, K s ≅ L (j s) ⋙ e.inverse) (P : MorphismProperty V)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [Small.{w} S] [P.IsSmall.{w}]
    (hQ : (adjointFamilyGenerators L P).IsCardinalForSmallObjectArgument κ) :
    (adjointFamilyGenerators K P).IsCardinalForSmallObjectArgument κ := by
  have hInverse :
      ((adjointFamilyGenerators L P).strictMap e.inverse).IsCardinalForSmallObjectArgument κ :=
    CofibrantGenerationData.Equivalence.family_eligible e
      (adjointFamilyGenerators L P) κ hQ
  let _ : IsCardinalForSmallObjectArgument
      ((adjointFamilyGenerators L P).strictMap e.inverse) κ := hInverse
  let _ : (adjointFamilyGenerators K P).IsSmall.{w} :=
    adjointFamilyGenerators_isSmall K P
  let _ : LocallySmall.{w} C := hInverse.locallySmall
  let _ : HasPushouts C := hInverse.hasPushouts
  let _ : HasCoproducts.{w} C := hInverse.hasCoproducts
  let _ : HasIterationOfShape κ.ord.ToType C := hInverse.hasIterationOfShape
  exact isCardinalForSmallObjectArgument_of_isoClosure
    (adjointFamilyGenerators K P) ((adjointFamilyGenerators L P).strictMap e.inverse) κ
    (adjointFamilyGenerators_le_strictMap_isoClosure e K L j q P)

end CategoryTheory.MorphismProperty
