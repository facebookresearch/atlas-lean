/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceSmash
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceRightModuleFreeUnit
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CofibrantFree
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.CanonicalProjectiveModels

/-!
# The actual orthogonal tensor unit and its original free-zero presentation

The selected relative sphere tensor unit is identified with the original
regular right sphere module by the actual free-unit maps. Reconstruction
through the original source equivalence and its original free/evaluation
adjunction gives the native free-zero spectrum with pointed unit coefficient.
The same original native projective model proves that this actual tensor
unit is cofibrant. The stable pushout-product and model unit axioms are
separate statements.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite HomotopicalAlgebra
open CategoryTheory.Spectra CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed CategoryTheory.MonObj CGWH.modelCategory



namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashUnit.Primitive

universe uC vC
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  (S : C) [MonObj S] [IsCommMonObj S] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The selected actual module unit uses the original free-unit inverse and regular unitor. -/
def sourceUnitIso :
    letI := RightModuleFree.tensorMonoidal S
    𝟙_ (CommutativeModuleConversion.RightModule S) ≅ RightModuleFree.regularObject S := by
  letI := RightModuleFree.tensorMonoidal S
  exact (RightModuleFree.freeTensorUnitIso S).symm ≪≫ RightModuleFree.freeUnitRegularIso S

/-- The complete forward source carrier is the original unit-carrier identification. -/
theorem sourceUnitIso_hom :
    letI := RightModuleFree.tensorMonoidal S
    (sourceUnitIso S).hom.hom =
      eqToHom (show (𝟙_ (CommutativeModuleConversion.RightModule S)).X = S from rfl) := by
  let := RightModuleFree.tensorMonoidal S
  change (RightModuleFree.freeTensorUnitIso S).inv.hom ≫
    (RightModuleFree.freeUnitRegularIso S).hom.hom = 𝟙 S
  rw [RightModuleFree.freeTensorUnitIso_inv, RightModuleFree.freeUnitRegularIso_hom,
    Iso.inv_hom_id]
  rfl

/-- The complete inverse source carrier is the inverse of that same original identification. -/
theorem sourceUnitIso_inv :
    letI := RightModuleFree.tensorMonoidal S
    (sourceUnitIso S).inv.hom =
      eqToHom (show S = (𝟙_ (CommutativeModuleConversion.RightModule S)).X from rfl) := by
  let := RightModuleFree.tensorMonoidal S
  change (RightModuleFree.freeUnitRegularIso S).inv.hom ≫
    (RightModuleFree.freeTensorUnitIso S).hom.hom = 𝟙 S
  rw [RightModuleFree.freeUnitRegularIso_inv, RightModuleFree.freeTensorUnitIso_hom,
    Iso.inv_hom_id]
  rfl

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashUnit.Primitive

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashUnit.ModuleStage

universe uV vV uI uJ
open EnrichedFunctorCat
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {J : Type uJ} [EnrichedCategory V J]
  (E : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
  (n : I) (a : J)
  (q : Free.object n (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I))
  (h : E.functor ⋙ EnrichedFunctorCat.evaluation a ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)

/-- The complete actual transported unit and original target free object. -/
def UnitIsoType :=
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  𝟙_ (EnrichedFunctorCat V J) ≅ Free.object a (𝟙_ V)

/-- Both actual source-unit maps and the original adjunction reconstruct the native unit. -/
def ofCoefficientUnit : UnitIsoType S E a := by
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  exact E.functor.mapIso (Primitive.sourceUnitIso S) ≪≫
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Unit.regularUnitOperatorIso S E n a q h

/-- The complete forward native map retains the source-unit map and actual free comparison. -/
theorem ofCoefficientUnit_hom :
    letI := RightModuleFree.tensorMonoidal S
    letI := Monoidal.transport E
    (ofCoefficientUnit S E n a q h).hom =
      E.functor.map (Primitive.sourceUnitIso S).hom ≫
        (CategoryTheory.Enriched.RightModuleFreeEvaluation.Unit.regularUnitOperatorIso
          S E n a q h).hom := by
  let := RightModuleFree.tensorMonoidal S
  let := Monoidal.transport E
  rfl

/-- The complete inverse native map retains the original inverse comparison and source unit. -/
theorem ofCoefficientUnit_inv :
    letI := RightModuleFree.tensorMonoidal S
    letI := Monoidal.transport E
    (ofCoefficientUnit S E n a q h).inv =
      (CategoryTheory.Enriched.RightModuleFreeEvaluation.Unit.regularUnitOperatorIso
        S E n a q h).inv ≫
        E.functor.map (Primitive.sourceUnitIso S).inv := by
  let := RightModuleFree.tensorMonoidal S
  let := Monoidal.transport E
  rfl

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashUnit.ModuleStage

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashUnit.TypedSource
universe uV vV uI vI uJ
open EnrichedFunctorCat
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]
  (source : Enriched.ModuleMappingR.SelectedSource V I)

/-- The complete original source unit is compared to the regular selected coefficient module. -/
def SourceUnitIsoType : Type _ :=
  letI := source.dayMonoidal
  letI := source.daySymmetric
  letI := source.coefficientMonObj
  letI := source.coefficientIsComm
  letI := source.dayCoequalizers
  letI := source.dayTensorLeftPreserves
  letI := source.dayTensorRightPreserves
  letI := source.moduleMonoidal
  𝟙_ source.Module ≅ RightModuleFree.regularObject source.coefficient

/-- Both original free-unit and Day unitor maps give the entire selected source unit Iso. -/
def sourceUnitIso : SourceUnitIsoType source := by
  letI := source.dayMonoidal
  letI := source.daySymmetric
  letI := source.coefficientMonObj
  letI := source.coefficientIsComm
  letI := source.dayCoequalizers
  letI := source.dayTensorLeftPreserves
  letI := source.dayTensorRightPreserves
  letI := source.moduleMonoidal
  exact Primitive.sourceUnitIso source.coefficient

/-- The entire original source unit forward carrier map. -/
def SourceUnitHomFormula : Prop :=
  letI := source.dayMonoidal
  letI := source.daySymmetric
  letI := source.coefficientMonObj
  letI := source.coefficientIsComm
  letI := source.dayCoequalizers
  letI := source.dayTensorLeftPreserves
  letI := source.dayTensorRightPreserves
  letI := source.moduleMonoidal
  (sourceUnitIso source).hom.hom =
    eqToHom (show (𝟙_ source.Module).X = source.coefficient from rfl)

/-- The full selected source unit forward carrier readback follows from the original theorem. -/
theorem sourceUnit_hom : SourceUnitHomFormula source := by
  let := source.dayMonoidal
  let := source.daySymmetric
  let := source.coefficientMonObj
  let := source.coefficientIsComm
  let := source.dayCoequalizers
  let := source.dayTensorLeftPreserves
  let := source.dayTensorRightPreserves
  let := source.moduleMonoidal
  exact Primitive.sourceUnitIso_hom source.coefficient

/-- The entire inverse of the same original source carrier identification. -/
def SourceUnitInvFormula : Prop :=
  letI := source.dayMonoidal
  letI := source.daySymmetric
  letI := source.coefficientMonObj
  letI := source.coefficientIsComm
  letI := source.dayCoequalizers
  letI := source.dayTensorLeftPreserves
  letI := source.dayTensorRightPreserves
  letI := source.moduleMonoidal
  (sourceUnitIso source).inv.hom =
    eqToHom (show source.coefficient = (𝟙_ source.Module).X from rfl)

/-- The full selected source unit inverse carrier readback uses the same original maps. -/
theorem sourceUnit_inv : SourceUnitInvFormula source := by
  let := source.dayMonoidal
  let := source.daySymmetric
  let := source.coefficientMonObj
  let := source.coefficientIsComm
  let := source.dayCoequalizers
  let := source.dayTensorLeftPreserves
  let := source.dayTensorRightPreserves
  let := source.moduleMonoidal
  exact Primitive.sourceUnitIso_inv source.coefficient

/-- The original complete source equivalence, zero coefficient Iso and evaluation comparison. -/
structure UnitComparison (source : Enriched.ModuleMappingR.SelectedSource V I)
    (J : Type uJ) [EnrichedCategory V J] where
  /-- Both original source and target functors and all their equivalence maps. -/
  equivalence : source.Module ≌ EnrichedFunctorCat V J
  /-- The original source index used by the free-unit comparison. -/
  sourceIndex : I
  /-- The original target index of the native free unit. -/
  targetIndex : J
  /-- The complete original free coefficient Iso. -/
  coefficientUnitIso : letI := source.dayMonoidal
    Free.object sourceIndex (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I)
  /-- The original complete free/evaluation comparison along the same E. -/
  evaluationComparison : letI := source.dayMonoidal
    letI := source.coefficientMonObj
    equivalence.functor ⋙ EnrichedFunctorCat.evaluation targetIndex ≅
      CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation
        source.coefficient sourceIndex

variable {source} {J : Type uJ} [EnrichedCategory V J]
  (comparison : UnitComparison source J)

/-- The full original unit Iso type under the selected whole source tensor and E. -/
def UnitIsoType : Type _ :=
  letI := source.moduleMonoidal
  letI := Monoidal.transport comparison.equivalence
  𝟙_ (EnrichedFunctorCat V J) ≅ Free.object comparison.targetIndex (𝟙_ V)

/-- The complete original unit Iso is reconstructed by the original source and free maps. -/
def unitIso : UnitIsoType comparison := by
  letI := source.dayMonoidal
  letI := source.daySymmetric
  letI := source.coefficientMonObj
  letI := source.coefficientIsComm
  letI := source.dayCoequalizers
  letI := source.dayTensorLeftPreserves
  letI := source.dayTensorRightPreserves
  letI := source.moduleMonoidal
  exact ModuleStage.ofCoefficientUnit source.coefficient comparison.equivalence
    comparison.sourceIndex comparison.targetIndex comparison.coefficientUnitIso
    comparison.evaluationComparison

/-- The whole forward unit map retains the original source and complete free comparison factors. -/
def UnitHomFormula : Prop :=
  letI := source.dayMonoidal
  letI := source.daySymmetric
  letI := source.coefficientMonObj
  letI := source.coefficientIsComm
  letI := source.dayCoequalizers
  letI := source.dayTensorLeftPreserves
  letI := source.dayTensorRightPreserves
  letI := source.moduleMonoidal
  letI := Monoidal.transport comparison.equivalence
  (unitIso comparison).hom =
    comparison.equivalence.functor.map (sourceUnitIso source).hom ≫
      (CategoryTheory.Enriched.RightModuleFreeEvaluation.Unit.regularUnitOperatorIso
        source.coefficient comparison.equivalence comparison.sourceIndex comparison.targetIndex
        comparison.coefficientUnitIso comparison.evaluationComparison).hom

/-- The full forward map readback is the unchanged original source theorem. -/
theorem unitIso_hom : UnitHomFormula comparison := by
  let := source.dayMonoidal
  let := source.daySymmetric
  let := source.coefficientMonObj
  let := source.coefficientIsComm
  let := source.dayCoequalizers
  let := source.dayTensorLeftPreserves
  let := source.dayTensorRightPreserves
  let := source.moduleMonoidal
  let := Monoidal.transport comparison.equivalence
  exact ModuleStage.ofCoefficientUnit_hom source.coefficient comparison.equivalence
    comparison.sourceIndex comparison.targetIndex comparison.coefficientUnitIso
    comparison.evaluationComparison

/-- The full inverse map retains the original inverse free comparison and source-unit inverse. -/
def UnitInvFormula : Prop :=
  letI := source.dayMonoidal
  letI := source.daySymmetric
  letI := source.coefficientMonObj
  letI := source.coefficientIsComm
  letI := source.dayCoequalizers
  letI := source.dayTensorLeftPreserves
  letI := source.dayTensorRightPreserves
  letI := source.moduleMonoidal
  letI := Monoidal.transport comparison.equivalence
  (unitIso comparison).inv =
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Unit.regularUnitOperatorIso
      source.coefficient comparison.equivalence comparison.sourceIndex comparison.targetIndex
      comparison.coefficientUnitIso comparison.evaluationComparison).inv ≫
        comparison.equivalence.functor.map (sourceUnitIso source).inv

/-- The full inverse map readback is the same original complete source theorem. -/
theorem unitIso_inv : UnitInvFormula comparison := by
  let := source.dayMonoidal
  let := source.daySymmetric
  let := source.coefficientMonObj
  let := source.coefficientIsComm
  let := source.dayCoequalizers
  let := source.dayTensorLeftPreserves
  let := source.dayTensorRightPreserves
  let := source.moduleMonoidal
  let := Monoidal.transport comparison.equivalence
  exact ModuleStage.ofCoefficientUnit_inv source.coefficient comparison.equivalence
    comparison.sourceIndex comparison.targetIndex comparison.coefficientUnitIso
    comparison.evaluationComparison

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashUnit.TypedSource

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashUnit.OriginalUnitCofibrancy

universe uC vC
variable {C : Type uC} [Category.{vC} C]

/-- The complete unit cofibrancy property at the supplied original tensor and model data. -/
def CofibrantFormula (tensor : MonoidalCategory C) (nativeModel : ModelCategory C) : Prop :=
  letI := tensor
  letI := nativeModel
  IsCofibrant (𝟙_ C)

/-- The original inverse unit isomorphism transports the supplied free-unit cofibrancy. -/
theorem ofUnitIso (tensor : MonoidalCategory C) (nativeModel : ModelCategory C)
    (F : C) (e : letI := tensor; 𝟙_ C ≅ F)
    (hF : letI := nativeModel; IsCofibrant F) : CofibrantFormula tensor nativeModel := by
  let := tensor
  let := nativeModel
  let _ : IsCofibrant F := hF
  exact isCofibrant_of_cofibration e.inv

/-- The full initial-map property for the entire supplied original generator class. -/
def OriginalILeftFormula (tensor : MonoidalCategory C) (initialData : HasInitial C)
    (I : MorphismProperty C) : Prop :=
  letI := tensor
  letI := initialData
  I.rlp.llp (initial.to (𝟙_ C))

/-- The whole original cofibration-class equality places the actual unit map in I right-left. -/
theorem initialUnitMem (tensor : MonoidalCategory C) (nativeModel : ModelCategory C)
    (F : C) (e : letI := tensor; 𝟙_ C ≅ F)
    (hF : letI := nativeModel; IsCofibrant F)
    (initialData : HasInitial C) (I : MorphismProperty C)
    (hClass : letI := nativeModel; cofibrations C = I.rlp.llp) :
    OriginalILeftFormula tensor initialData I := by
  let := tensor
  let := nativeModel
  let := initialData
  let _ : IsCofibrant (𝟙_ C) := ofUnitIso tensor nativeModel F e hF
  have h := mem_cofibrations (initial.to (𝟙_ C))
  rw [hClass] at h
  exact h

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashUnit.OriginalUnitCofibrancy

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashUnit

/-- Use the original ordinary orthogonal index for the actual unit comparison. -/
local instance : Category.{v} OrthogonalIndex := SphereSmashStructure.indexCategory.{u, v}
/-- Use the original direct-sum tensor on the source index. -/
local instance : MonoidalCategory OrthogonalIndex :=
  SphereSmashStructure.indexMonoidalCategory.{u, v}
/-- Retain the original continuous ordinary/enriched index compatibility. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  SphereSmashStructure.indexEnrichedOrdinaryCategory.{u, v}
/-- Use the original source-index block symmetry. -/
local instance : SymmetricCategory OrthogonalIndex :=
  SphereSmashStructure.indexSymmetricCategory.{u, v}
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction

/-- The actual sphere coefficient diagram category on the original orthogonal index. -/
abbrev ISpace := EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex
/-- Use the original Day tensor on complete orthogonal coefficient diagrams. -/
local instance : MonoidalCategory ISpace.{u, v} := SphereSmashStructure.dayMonoidalCategory.{u, v}
/-- Keep the original complete Day symmetry. -/
local instance : SymmetricCategory ISpace.{u, v} := SphereSmashStructure.daySymmetricCategory.{u, v}
/-- Use the original representation-sphere Day monoid. -/
local instance : MonObj sphereISpace.{u, v} := SphereSmashStructure.sphereMonoid.{u, v}
/-- The original sphere Day multiplication is commutative. -/
local instance : IsCommMonObj sphereISpace.{u, v} :=
  SphereSmashStructure.sphereCommutativeMonoid.{u, v}
/-- The native coefficient diagrams have their original coequalizers. -/
local instance : HasCoequalizers ISpace.{u, v} := SphereSmashStructure.hasCoequalizers.{u, v}

/-- The actual pointed source has all original small product and equalizer data. -/
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

/-- The genuine Day adjunction preserves the first tensor coefficient. -/
theorem nativeTensorLeftPreserves :
    (SphereSmash.sourceData.{u, v}).DayTensorLeftPreservationType :=
  (SphereSmash.sourceData.{u, v}).dayTensorLeftPreserves
attribute [local instance] nativeTensorLeftPreserves

/-- The same adjunction preserves the second tensor coefficient. -/
theorem nativeTensorRightPreserves :
    (SphereSmash.sourceData.{u, v}).DayTensorRightPreservationType :=
  (SphereSmash.sourceData.{u, v}).dayTensorRightPreserves
attribute [local instance] nativeTensorRightPreserves

/-- Use the actual selected relative sphere-module tensor. -/
local instance : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmashStructure.monoidalCategory.{u, v}
/-- Use the original complete E transport on the canonical spectrum carrier. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The original native zero-free spectrum with the actual pointed smash-unit coefficient. -/
abbrev freeZeroUnit :=
  EnrichedFunctorCat.Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
    (𝟙_ PointedCGWH.{u, v})

/-- The actual original source unit comparison, with the original zero indices and full maps. -/
def unitComparison :
    TypedSource.UnitComparison SphereSmash.sourceData.{u, v} OrthogonalOperatorIndex.{u, v} where
  equivalence := CanonicalSourceSmash.sourceEquivalence.{u, v}
  sourceIndex := 0
  targetIndex := OrthogonalOperatorIndex.ofIndex.{u, v} 0
  coefficientUnitIso := CanonicalSourceRightModuleFreeUnit.freeUnitISpaceIso.{u, v}
  evaluationComparison := CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} 0

/-- The actual canonical sphere tensor unit is the original native zero-free unit spectrum. -/
abbrev unitIso : TypedSource.UnitIsoType unitComparison.{u, v} :=
  TypedSource.unitIso unitComparison.{u, v}

/-- The whole actual unit forward map retains the original source and adjunction factors. -/
theorem unitIso_hom : TypedSource.UnitHomFormula unitComparison.{u, v} :=
  TypedSource.unitIso_hom unitComparison.{u, v}

/-- The whole actual unit inverse retains those same original inverse factors. -/
theorem unitIso_inv : TypedSource.UnitInvFormula unitComparison.{u, v} :=
  TypedSource.unitIso_inv unitComparison.{u, v}

/-- The entire original freely enriched boundary family on the canonical operator carrier. -/
abbrev originalLevelI : MorphismProperty CanonicalSourceSmash.Carrier.{u, v} :=
  EnrichedProjective.generators (A := OrthogonalOperatorIndex.{u, v})
    PointedCGWH.realizedBoundaryInclusions.{u, v}

/-- The original projective Free/evaluation Quillen adjunction proves native free-zero
cofibrancy. -/
theorem freeZeroUnit_isCofibrant :
    letI : ModelCategory CanonicalSourceSmash.Carrier.{u, v} :=
      PointedCGWH.Spectra.Orthogonal.levelModel
    IsCofibrant freeZeroUnit.{u, v} := by
  let _ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
    EnrichedProjective.Native.Construction.generatorOrderBot
  exact EnrichedProjective.Native.freeAt_unit_isCofibrant
    (OrthogonalOperatorIndex.ofIndex.{u, v} 0)

/-- The actual canonical sphere tensor unit is cofibrant in that same original level model. -/
theorem isCofibrant_tensorUnit :
    OriginalUnitCofibrancy.CofibrantFormula CanonicalSourceSmash.monoidalCategory.{u, v}
      PointedCGWH.Spectra.Orthogonal.levelModel.{u, v} :=
  OriginalUnitCofibrancy.ofUnitIso CanonicalSourceSmash.monoidalCategory.{u, v}
    PointedCGWH.Spectra.Orthogonal.levelModel.{u, v}
    freeZeroUnit.{u, v} unitIso.{u, v} freeZeroUnit_isCofibrant.{u, v}

/-- The actual unit initial map is in the full original I right-left orthogonal class. -/
theorem tensorUnit_mem_originalILeft :
    OriginalUnitCofibrancy.OriginalILeftFormula CanonicalSourceSmash.monoidalCategory.{u, v}
      (inferInstance : HasInitial CanonicalSourceSmash.Carrier.{u, v}) originalLevelI.{u, v} :=
  OriginalUnitCofibrancy.initialUnitMem CanonicalSourceSmash.monoidalCategory.{u, v}
    PointedCGWH.Spectra.Orthogonal.levelModel.{u, v}
    freeZeroUnit.{u, v} unitIso.{u, v} freeZeroUnit_isCofibrant.{u, v}
    (inferInstance : HasInitial CanonicalSourceSmash.Carrier.{u, v}) originalLevelI.{u, v}
    PointedCGWH.Spectra.Orthogonal.levelModel_cofibrations.{u, v}

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashUnit
