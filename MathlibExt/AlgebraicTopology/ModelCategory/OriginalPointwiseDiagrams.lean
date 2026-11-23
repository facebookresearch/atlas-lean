/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.PointwiseFunctorClosed
import MathlibExt.CategoryTheory.Monoidal.PushoutProductFunctor
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Data
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Factorization
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalSmithModel
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalIndexQuillenComparisons
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductGeneratorCriterion
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
# Pointwise tensor models on the original ordinary diagrams

The original projective and combinatorial injective factories supply the
model dictionaries and full functorial factors. The pointwise internal Hom
is the existing under-category end construction. Generator products and
the original initial-unit factor supply projective monoidal model laws;
objectwise coefficient laws supply the injective laws.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe w uJ vJ uC vC

open CategoryTheory Limits MorphismProperty MonoidalCategory
open HomotopicalAlgebra
open scoped MonoidalClosed

namespace HomotopicalAlgebra.OriginalPointwiseDiagrams

section EvaluationTensor

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [HasPushouts C] [∀ a b : J, HasProductsOfShape (a ⟶ b) C]

/-- Ordinary evaluation is strictly monoidal for the actual pointwise tensor. -/
@[instance_reducible]
def evaluationMonoidal (j : J) : ((evaluation J C).obj j).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

set_option backward.isDefEq.respectTransparency false in
/-- The evaluated original pushout-product is compared through the existing whole-arrow map. -/
def evaluationPushoutProductIso {F G K L : J ⥤ C} (i : F ⟶ G) (q : K ⟶ L) (j : J) :
    Arrow.mk ((Arrow.mk i □ Arrow.mk q).hom.app j) ≅
      Arrow.mk ((Arrow.mk (i.app j) □ Arrow.mk (q.app j)).hom) := by
  letI := evaluationMonoidal (C := C) j
  exact Functor.mapArrowPushoutProductIso ((evaluation J C).obj j) i q

/-- Pointwise PP retains every original component pushout-product arrow. -/
theorem pointwise_pushoutProduct_le (P Q R : MorphismProperty C) [R.RespectsIso]
    (h : PushoutProductLe P Q R) :
    PushoutProductLe (P.functorCategory J) (Q.functorCategory J) (R.functorCategory J) := by
  intro F G K L i q hi hq j
  exact (R.arrow_mk_iso_iff (evaluationPushoutProductIso i q j)).mpr
    (h (i.app j) (q.app j) (hi j) (hq j))

end EvaluationTensor

section OriginalInjective

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} J C)
  [∀ a b : J, HasProductsOfShape (a ⟶ b) C]

include d κLP s in
omit [SymmetricCategory C] [MonoidalClosed C] in
/-- A cofibrant coefficient unit gives true unit cofibrancy in the constructed injective model. -/
theorem injective_isCofibrant_unit [IsCofibrant (𝟙_ C)] :
    letI : ModelCategory (J ⥤ C) := FunctorInjective.originalSmithModelCategory d κLP s
    IsCofibrant (𝟙_ (J ⥤ C)) := by
  let _ : ModelCategory (J ⥤ C) := FunctorInjective.originalSmithModelCategory d κLP s
  apply (isCofibrant_iff (𝟙_ (J ⥤ C))).mpr
  apply (cofibration_iff _).mpr
  rw [FunctorInjective.originalInjectiveModel_cofibrations d κLP s]
  intro j
  let E := (evaluation J C).obj j
  let hAll : PreservesColimitsOfSize.{0, 0} E :=
    (evaluationAdjunctionLeft C j).leftAdjoint_preservesColimits
  let hEmpty : PreservesColimitsOfShape (Discrete PEmpty) E := hAll.preservesColimitsOfShape
  let _ : PreservesColimit (Functor.empty (J ⥤ C)) E := hEmpty.preservesColimit
  let _ : IsCofibrant (E.obj (𝟙_ (J ⥤ C))) := by
    change IsCofibrant (𝟙_ C)
    infer_instance
  have hInitial : IsInitial (E.obj (⊥_ (J ⥤ C))) :=
    IsInitial.isInitialObj E _ initialIsInitial
  change cofibrations C (E.map (initial.to (𝟙_ (J ⥤ C))))
  exact (cofibration_iff _).mp
    ((isCofibrant_iff_of_isInitial (E.map (initial.to (𝟙_ (J ⥤ C)))) hInitial).mp inferInstance)

/-- The constructed injective model satisfies PP by the original coefficient laws. -/
theorem injective_pushoutProductAxiom [IsClosedSymmetricMonoidalModelCategory C] :
    letI : ModelCategory (J ⥤ C) := FunctorInjective.originalSmithModelCategory d κLP s
    MonoidalPushoutProductAxiom (J ⥤ C) := by
  let _ : ModelCategory (J ⥤ C) := FunctorInjective.originalSmithModelCategory d κLP s
  refine ⟨?_, ?_, ?_⟩
  · rw [FunctorInjective.originalInjectiveModel_cofibrations d κLP s]
    exact pointwise_pushoutProduct_le _ _ _
      (IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct (C := C))
  · rw [FunctorInjective.originalInjectiveModel_cofibrations d κLP s,
      FunctorInjective.originalInjectiveModel_trivialCofibrations d κLP s]
    exact pointwise_pushoutProduct_le _ _ _
      (IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left (C := C))
  · rw [FunctorInjective.originalInjectiveModel_cofibrations d κLP s,
      FunctorInjective.originalInjectiveModel_trivialCofibrations d κLP s]
    exact pointwise_pushoutProduct_le _ _ _
      (IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right (C := C))

variable
  [∀ F G : J ⥤ C, Enriched.FunctorCategory.HasEnrichedHom C F G]
  [∀ F G : J ⥤ C, Enriched.FunctorCategory.HasFunctorEnrichedHom C F G]

/-- The pointwise injective monoidal model uses the same original Smith initial-unit factor. -/
theorem injective_monoidalModel [IsClosedSymmetricMonoidalModelCategory C]
    [IsCofibrant (𝟙_ C)] :
    letI : ModelCategory (J ⥤ C) := FunctorInjective.originalSmithModelCategory d κLP s
    letI := CategoryTheory.Monoidal.PointwiseFunctorClosed.monoidalClosed (J := J) (V := C)
    IsClosedSymmetricMonoidalModelCategory (J ⥤ C) := by
  let _ : ModelCategory (J ⥤ C) := FunctorInjective.originalSmithModelCategory d κLP s
  let _ := CategoryTheory.Monoidal.PointwiseFunctorClosed.monoidalClosed (J := J) (V := C)
  let _ : IsCofibrant (𝟙_ (J ⥤ C)) := injective_isCofibrant_unit d κLP s
  exact (injective_pushoutProductAxiom d κLP s).monoidalModelOfUnitFactor
    ((FunctorInjective.originalSmithCofibrantFactorizationData d κLP s).factorizationData
      (initial.to (𝟙_ (J ⥤ C))))

/-- The injective unit witness is the original Smith factor object and map as actual data. -/
def injectiveUnitWitness [IsClosedSymmetricMonoidalModelCategory C] [IsCofibrant (𝟙_ C)] :
    letI : ModelCategory (J ⥤ C) := FunctorInjective.originalSmithModelCategory d κLP s
    letI := CategoryTheory.Monoidal.PointwiseFunctorClosed.monoidalClosed (J := J) (V := C)
    MonoidalUnitAxiomWitness (J ⥤ C) := by
  letI : ModelCategory (J ⥤ C) := FunctorInjective.originalSmithModelCategory d κLP s
  letI := CategoryTheory.Monoidal.PointwiseFunctorClosed.monoidalClosed (J := J) (V := C)
  let _ : IsCofibrant (𝟙_ (J ⥤ C)) := injective_isCofibrant_unit d κLP s
  exact (injective_pushoutProductAxiom d κLP s).unitAxiomWitnessOfFunctorialFactorization
    (FunctorInjective.originalSmithCofibrantFactorizationData d κLP s)

/-- The original injective unit factor's middle object is unchanged. -/
theorem injective_unitWitness_Q [IsClosedSymmetricMonoidalModelCategory C] [IsCofibrant (𝟙_ C)] :
    letI : ModelCategory (J ⥤ C) := FunctorInjective.originalSmithModelCategory d κLP s
    letI := CategoryTheory.Monoidal.PointwiseFunctorClosed.monoidalClosed (J := J) (V := C)
    (injectiveUnitWitness d κLP s).Q =
      (FunctorInjective.originalSmithCofibrantFactorizationData d κLP s).Z.obj
        (Arrow.mk (initial.to (𝟙_ (J ⥤ C)))) := rfl

/-- The actual original Smith right factor remains the unit replacement map. -/
theorem injective_unitWitness_q [IsClosedSymmetricMonoidalModelCategory C] [IsCofibrant (𝟙_ C)] :
    letI : ModelCategory (J ⥤ C) := FunctorInjective.originalSmithModelCategory d κLP s
    letI := CategoryTheory.Monoidal.PointwiseFunctorClosed.monoidalClosed (J := J) (V := C)
    (injectiveUnitWitness d κLP s).q =
      (FunctorInjective.originalSmithCofibrantFactorizationData d κLP s).p.app
        (Arrow.mk (initial.to (𝟙_ (J ⥤ C)))) := rfl

end OriginalInjective

section OriginalProjective

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} J] [LocallySmall.{w} J]
  (d : CofibrantGenerationData C κ)
  [∀ F G : J ⥤ C, Enriched.FunctorCategory.HasEnrichedHom C F G]
  [∀ F G : J ⥤ C, Enriched.FunctorCategory.HasFunctorEnrichedHom C F G]

/-- Source generator cofibration products construct all projective pointwise monoidal laws. -/
theorem projective_monoidalModel
    (hII : PushoutProductLe (FunctorProjective.freeGenerators (D := J) d d.I)
      (FunctorProjective.freeGenerators (D := J) d d.I)
      (FunctorProjective.freeGenerators (D := J) d d.I).rlp.llp)
    (hJI : PushoutProductLe (FunctorProjective.freeGenerators (D := J) d d.J)
      (FunctorProjective.freeGenerators (D := J) d d.I)
      (FunctorProjective.freeGenerators (D := J) d d.J).rlp.llp)
    (hUnit : (FunctorProjective.freeGenerators (D := J) d d.I).rlp.llp
      (initial.to (𝟙_ (J ⥤ C)))) :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI := CategoryTheory.Monoidal.PointwiseFunctorClosed.monoidalClosed (J := J) (V := C)
    IsClosedSymmetricMonoidalModelCategory (J ⥤ C) := by
  let _ : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let _ := CategoryTheory.Monoidal.PointwiseFunctorClosed.monoidalClosed (J := J) (V := C)
  let G := FunctorProjective.generationData (D := J) d
  let _ : IsCofibrant (𝟙_ (J ⥤ C)) := by
    apply (isCofibrant_iff (𝟙_ (J ⥤ C))).mpr
    apply (cofibration_iff _).mpr
    rw [← FunctorProjective.freeI_left_eq d]
    exact hUnit
  apply G.monoidalModelOfGeneratorProducts
  · change PushoutProductLe (FunctorProjective.freeGenerators (D := J) d d.I)
      (FunctorProjective.freeGenerators (D := J) d d.I) (cofibrations (J ⥤ C))
    rw [← FunctorProjective.freeI_left_eq d]
    exact hII
  · change PushoutProductLe (FunctorProjective.freeGenerators (D := J) d d.J)
      (FunctorProjective.freeGenerators (D := J) d d.I) (trivialCofibrations (J ⥤ C))
    rw [← FunctorProjective.freeJ_left_eq d]
    exact hJI
  · exact (FunctorProjective.cofibrantFactorizationData (D := J) d).factorizationData
      (initial.to (𝟙_ (J ⥤ C)))

end OriginalProjective

end HomotopicalAlgebra.OriginalPointwiseDiagrams
