/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalSmithModel
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.IndexQuillenEquivalence
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.EssentialIndex

/-!
# Actual original index and Quillen comparisons

The original coefficient generation and essential-index data construct all
models here. Restriction and its particular native right Kan adjunction are
retained, as are the original projective-to-injective identity and both maps
of an original index equivalence. The source is HTT, author April 9, 2017,
Remarks A.2.8.5–6, printed page 832/PDF page 850.
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uE vE uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.Functor

namespace HomotopicalAlgebra.FunctorInjective

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {kappa : Cardinal.{w}} [Fact kappa.IsRegular] [OrderBot kappa.ord.ToType]
  (d : CofibrantGenerationData C kappa) (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP]
  (sD : Functor.EssentialIndexData.{w} D C) (sE : Functor.EssentialIndexData.{w} E C)

/-- The existing original-index projective factory uses the actual selected small index. -/
@[instance_reducible]
def originalProjectiveModelCategory : ModelCategory (D ⥤ C) := by
  letI : LocallySmall.{w} sD.index := locallySmall_self sD.index
  exact FunctorProjective.EssentialIndex.modelCategory (κ := kappa) sD.equivalence d

/-- Original restriction preserves both constructed injective left classes. -/
theorem originalRestriction_preserves_left_classes (u : D ⥤ E) :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP sD
    letI : ModelCategory (E ⥤ C) := originalSmithModelCategory d kappaLP sE
    PreservesCofibrations ((whiskeringLeft D E C).obj u) ∧
      PreservesTrivialCofibrations ((whiskeringLeft D E C).obj u) := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP sD
  let _ : ModelCategory (E ⥤ C) := originalSmithModelCategory d kappaLP sE
  exact KanExtensions.preserves_left_classes_of_eqs
    (originalInjectiveModel_cofibrations d kappaLP sD)
    (originalInjectiveModel_cofibrations d kappaLP sE)
    (originalInjectiveModel_trivialCofibrations d kappaLP sD)
    (originalInjectiveModel_trivialCofibrations d kappaLP sE) u

/-- The actual particular native Ran adjunction is Quillen for the constructed models. -/
theorem originalRan_isQuillen (u : D ⥤ E)
    [∀ F : D ⥤ C, u.HasRightKanExtension F] :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP sD
    letI : ModelCategory (E ⥤ C) := originalSmithModelCategory d kappaLP sE
    (u.ranAdjunction C).IsQuillenAdjunction := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP sD
  let _ : ModelCategory (E ⥤ C) := originalSmithModelCategory d kappaLP sE
  exact KanExtensions.isQuillen_of_pointwise_left_classes u
    (originalInjectiveModel_cofibrations d kappaLP sD)
    (originalInjectiveModel_cofibrations d kappaLP sE)
    (originalInjectiveModel_trivialCofibrations d kappaLP sD)
    (originalInjectiveModel_trivialCofibrations d kappaLP sE)

/-- The actual original projective left class lies in the actual injective left class.
The proof uses the original bounded-right lifting tests, without an assumed comparison. -/
theorem originalProjectiveCofibrations_le_injective :
    (originalProjectiveModelCategory d sD).categoryWithCofibrations.cofibrations ≤
      (originalSmithModelCategory d kappaLP sD).categoryWithCofibrations.cofibrations := by
  let _ : LocallySmall.{w} sD.index := locallySmall_self sD.index
  have hP : (originalProjectiveModelCategory d sD).categoryWithCofibrations.cofibrations =
      ((trivialFibrations C).functorCategory D).llp :=
    FunctorProjective.EssentialIndex.cofibrations_eq (κ := kappa) sD.equivalence d
  have hI : (originalSmithModelCategory d kappaLP sD).categoryWithCofibrations.cofibrations =
        (boundedConstruction d kappaLP sD).family.generators.rlp.llp :=
    originalSmithModel_cofibrations d kappaLP sD
  rw [hP, hI]
  exact antitone_llp (boundedRight_le_objectwise_trivialFibrations d kappaLP sD
    (boundedConstruction d kappaLP sD))

/-- The same-carrier identity is left Quillen from the actually constructed projective
model to the actually constructed injective model; both dictionaries are internal. -/
theorem originalProjectiveToInjective_isQuillen :
    @Adjunction.IsQuillenAdjunction (D ⥤ C) _ (D ⥤ C) _
      (originalProjectiveModelCategory d sD)
      (originalSmithModelCategory d kappaLP sD) (𝟭 (D ⥤ C)) (𝟭 (D ⥤ C))
      (Adjunction.id (C := D ⥤ C)) := by
  let P := originalProjectiveModelCategory d sD
  let I := originalSmithModelCategory d kappaLP sD
  refine @Adjunction.IsQuillenAdjunction.mk (D ⥤ C) _ (D ⥤ C) _
    (originalProjectiveModelCategory d sD) (originalSmithModelCategory d kappaLP sD)
    (𝟭 (D ⥤ C)) (𝟭 (D ⥤ C)) (Adjunction.id (C := D ⥤ C)) ?_ ?_
  · exact originalProjectiveCofibrations_le_injective d kappaLP sD
  · intro F G f hf
    refine ⟨originalProjectiveCofibrations_le_injective d kappaLP sD f hf.1, ?_⟩
    let _ : LocallySmall.{w} sD.index := locallySmall_self sD.index
    have hP : P.categoryWithWeakEquivalences.weakEquivalences =
          (weakEquivalences C).functorCategory D :=
      FunctorProjective.EssentialIndex.weakEquivalences_eq (κ := kappa) sD.equivalence d
    have hI : I.categoryWithWeakEquivalences.weakEquivalences =
          (weakEquivalences C).functorCategory D :=
      originalSmithModel_weakEquivalences d kappaLP sD
    change I.categoryWithWeakEquivalences.weakEquivalences f
    have hWeak : P.categoryWithWeakEquivalences.weakEquivalences f := hf.2
    rw [hI]
    rw [hP] at hWeak
    exact hWeak

/-- The original identity is a Quillen equivalence between the constructed projective
and injective models, whose weak equivalences are the same objectwise maps. -/
theorem originalProjectiveToInjective_isQuillenEquivalence :
    @Adjunction.IsQuillenEquivalence (D ⥤ C) _ (D ⥤ C) _
      (originalProjectiveModelCategory d sD)
      (originalSmithModelCategory d kappaLP sD) (𝟭 (D ⥤ C)) (𝟭 (D ⥤ C))
      (Adjunction.id (C := D ⥤ C)) := by
  refine @Adjunction.IsQuillenEquivalence.mk (D ⥤ C) _ (D ⥤ C) _
    (originalProjectiveModelCategory d sD) (originalSmithModelCategory d kappaLP sD)
    (𝟭 (D ⥤ C)) (𝟭 (D ⥤ C)) (Adjunction.id (C := D ⥤ C))
    (originalProjectiveToInjective_isQuillen d kappaLP sD) ?_
  intro F G _ _ f
  let _ : LocallySmall.{w} sD.index := locallySmall_self sD.index
  have hP :
      (originalProjectiveModelCategory d sD).categoryWithWeakEquivalences.weakEquivalences =
        (weakEquivalences C).functorCategory D :=
    FunctorProjective.EssentialIndex.weakEquivalences_eq (κ := kappa) sD.equivalence d
  have hI :
      (originalSmithModelCategory d kappaLP sD).categoryWithWeakEquivalences.weakEquivalences =
        (weakEquivalences C).functorCategory D :=
    originalSmithModel_weakEquivalences d kappaLP sD
  have hAdjunct : (Adjunction.id (C := D ⥤ C)).homEquiv F G f = f := by
    simp [Adjunction.homEquiv]
  change
    (originalSmithModelCategory d kappaLP sD).categoryWithWeakEquivalences.weakEquivalences f ↔
      (originalProjectiveModelCategory d sD).categoryWithWeakEquivalences.weakEquivalences
        ((Adjunction.id (C := D ⥤ C)).homEquiv F G f)
  rw [hAdjunct, hI, hP]

section Equivalence

/-- The actual original inverse supplies the extension object on an index equivalence. -/
def originalIndexRightExtension (e : D ≌ E) (F : D ⥤ C) : E ⥤ C := e.inverse ⋙ F

/-- The extension comparison retains the original associator and original unit inverse. -/
def originalIndexRightExtensionIso (e : D ≌ E) (F : D ⥤ C) :
    e.functor ⋙ originalIndexRightExtension e F ≅ F :=
  (Functor.associator e.functor e.inverse F).symm ≪≫
    isoWhiskerRight e.unitIso.symm F ≪≫ F.leftUnitor

omit [ModelCategory C] in
/-- Every forward extension component is the image of the original unit inverse. -/
theorem originalIndexRightExtensionIso_hom_app (e : D ≌ E) (F : D ⥤ C) (a : D) :
    (originalIndexRightExtensionIso e F).hom.app a = F.map (e.unitIso.inv.app a) := by
  change 𝟙 _ ≫ (F.map (e.unitIso.inv.app a) ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

omit [ModelCategory C] in
/-- Every inverse extension component is the image of the same original unit. -/
theorem originalIndexRightExtensionIso_inv_app (e : D ≌ E) (F : D ⥤ C) (a : D) :
    (originalIndexRightExtensionIso e F).inv.app a = F.map (e.unitIso.hom.app a) := by
  change (𝟙 _ ≫ F.map (e.unitIso.hom.app a)) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

omit [ModelCategory C] in
/-- Native right Kan existence follows from that actual original inverse comparison. -/
theorem originalIndex_hasRightKanExtension (e : D ≌ E) (F : D ⥤ C) :
    e.functor.HasRightKanExtension F := by
  let _ : (originalIndexRightExtension e F).IsRightKanExtension
      (originalIndexRightExtensionIso e F).hom := inferInstance
  exact Functor.HasRightKanExtension.mk (originalIndexRightExtension e F)
    (originalIndexRightExtensionIso e F).hom

omit [ModelCategory C] in
/-- The unit of the actual native Ran along the original equivalence is an isomorphism. -/
theorem originalIndexRan_unit_isIso (e : D ≌ E) (F : E ⥤ C) :
    letI (G : D ⥤ C) : e.functor.HasRightKanExtension G :=
      originalIndex_hasRightKanExtension e G
    IsIso ((e.functor.ranAdjunction C).unit.app F) := by
  let _ (G : D ⥤ C) : e.functor.HasRightKanExtension G :=
    originalIndex_hasRightKanExtension e G
  infer_instance

omit [ModelCategory C] in
/-- The counit of that same native adjunction is an isomorphism on every original functor. -/
theorem originalIndexRan_counit_isIso (e : D ≌ E) (F : D ⥤ C) :
    letI (G : D ⥤ C) : e.functor.HasRightKanExtension G :=
      originalIndex_hasRightKanExtension e G
    IsIso ((e.functor.ranAdjunction C).counit.app F) := by
  let _ (G : D ⥤ C) : e.functor.HasRightKanExtension G :=
    originalIndex_hasRightKanExtension e G
  infer_instance

/-- The original equivalence gives QE of the actual native Ran with models produced internally. -/
theorem originalIndex_isQuillenEquivalence (e : D ≌ E) :
    letI (F : D ⥤ C) : e.functor.HasRightKanExtension F :=
      originalIndex_hasRightKanExtension e F
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP sD
    letI : ModelCategory (E ⥤ C) := originalSmithModelCategory d kappaLP sE
    (e.functor.ranAdjunction C).IsQuillenEquivalence := by
  let _ (F : D ⥤ C) : e.functor.HasRightKanExtension F :=
    originalIndex_hasRightKanExtension e F
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP sD
  let _ : ModelCategory (E ⥤ C) := originalSmithModelCategory d kappaLP sE
  exact IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes e
    (originalSmithModel_weakEquivalences d kappaLP sD)
    (originalSmithModel_weakEquivalences d kappaLP sE)
    (originalInjectiveModel_cofibrations d kappaLP sD)
    (originalInjectiveModel_cofibrations d kappaLP sE)
    (originalInjectiveModel_trivialCofibrations d kappaLP sD)
    (originalInjectiveModel_trivialCofibrations d kappaLP sE)

end Equivalence

end HomotopicalAlgebra.FunctorInjective
