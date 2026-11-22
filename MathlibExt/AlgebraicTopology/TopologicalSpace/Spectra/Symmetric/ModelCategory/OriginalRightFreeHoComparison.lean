/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.LeftRightDerivedCarrierHomComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.StandardDerivedFreeComparison

/-!
# Both original RIGHT Free choices in the actual model Ho category

Project the entire chosen converted-left and literal standard-right Free
functors through the given original RIGHT model projection. Their chosen
source comparison, full Arrow maps and both inverse maps remain unchanged.
The actual sphere inverse and canonical derived inverse transport that same
comparison, retaining the complete original carrier and derived Hom maps.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

namespace PointedCGWH.Spectra.Symmetric.RightPresentationModel

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
@[instance_reducible]
private def sourceLeftModel : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

@[instance_reducible]
private def sourceRightModel : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}

attribute [local instance] sourceLeftModel sourceRightModel
  Native.modelCategory

open LeftRightNativeModel

/-- The full original converted LEFT Free followed by the actual RIGHT model projection. -/
abbrev convertedFreeHo (n : I) : PointedCGWH.{u, v} ⥤
  (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) :=
  freeAt n ⋙ (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

/-- The literal original standard RIGHT Free keeps its full original coefficient functor. -/
abbrev standardFreeHo (n : I) : PointedCGWH.{u, v} ⥤
  (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) :=
  standardFreeAt n ⋙ (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

/-- The actual original source Free comparison projected as an entire natural isomorphism. -/
def convertedStandardFreeHoIso (n : I) : convertedFreeHo.{u, v} n ≅ standardFreeHo.{u, v} n :=
  Functor.isoWhiskerRight (convertedStandardFreeIso n)
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

theorem convertedStandardFreeHoIso_hom (n : I) (X : PointedCGWH.{u, v}) :
    (convertedStandardFreeHoIso n).hom.app X =
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).map
        ((convertedStandardFreeIso n).hom.app X) := rfl

theorem convertedStandardFreeHoIso_inv (n : I) (X : PointedCGWH.{u, v}) :
    (convertedStandardFreeHoIso n).inv.app X =
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).map
        ((convertedStandardFreeIso n).inv.app X) := rfl

theorem convertedStandardFreeHo_hom_naturality (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (convertedFreeHo n).map f ≫ (convertedStandardFreeHoIso n).hom.app Y =
      (convertedStandardFreeHoIso n).hom.app X ≫ (standardFreeHo n).map f :=
  (convertedStandardFreeHoIso n).hom.naturality f

theorem convertedStandardFreeHo_inv_naturality (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (standardFreeHo n).map f ≫ (convertedStandardFreeHoIso n).inv.app Y =
      (convertedStandardFreeHoIso n).inv.app X ≫ (convertedFreeHo n).map f :=
  (convertedStandardFreeHoIso n).inv.naturality f

/-- Every full original coefficient Arrow retains both chosen Free maps after projection. -/
def convertedStandardFreeHoArrowIso (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CategoryTheory.Arrow.mk ((convertedFreeHo n).map f) ≅
      CategoryTheory.Arrow.mk ((standardFreeHo n).map f) :=
  (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).mapArrow.mapIso
    (convertedStandardFreeArrowIso n f)

theorem convertedStandardFreeHo_hom_inv (n : I) (X : PointedCGWH.{u, v}) :
    (convertedStandardFreeHoIso n).hom.app X ≫ (convertedStandardFreeHoIso n).inv.app X = 𝟙 _ :=
  (convertedStandardFreeHoIso n).hom_inv_id_app X

theorem convertedStandardFreeHo_inv_hom (n : I) (X : PointedCGWH.{u, v}) :
    (convertedStandardFreeHoIso n).inv.app X ≫ (convertedStandardFreeHoIso n).hom.app X = 𝟙 _ :=
  (convertedStandardFreeHoIso n).inv_hom_id_app X

/-- Transport both whole original Free functors by the actual strict inverse sphere Ho lift. -/
def convertedStandardFreeCarrierInverseIso (n : I) :
    convertedFreeHo.{u, v} n ⋙ originalSphereHoEquivalence.{u, v}.inverse ≅
      standardFreeHo.{u, v} n ⋙ originalSphereHoEquivalence.{u, v}.inverse :=
  Functor.isoWhiskerRight (convertedStandardFreeHoIso n) originalSphereHoEquivalence.inverse

/-- Transport the same chosen source Free comparison through the actual canonical inverse. -/
def convertedStandardFreeDerivedInverseIso (n : I) :
    convertedFreeHo.{u, v} n ⋙ toRightDerivedAdjunctionData.{u, v}.rightDerived ≅
      standardFreeHo.{u, v} n ⋙ toRightDerivedAdjunctionData.{u, v}.rightDerived :=
  Functor.isoWhiskerRight (convertedStandardFreeHoIso n) toRightDerivedAdjunctionData.rightDerived

/-- The original converted Free carrier inverse keeps the given whole canonical comparison. -/
def convertedFreeCarrierDerivedInverseIso (n : I) :
    convertedFreeHo.{u, v} n ⋙ originalSphereHoEquivalence.{u, v}.inverse ≅
      convertedFreeHo.{u, v} n ⋙ toRightDerivedAdjunctionData.{u, v}.rightDerived :=
  Functor.isoWhiskerLeft (convertedFreeHo n) toRightCarrierRightComparison

/-- The standard original RIGHT Free retains its own full canonical inverse comparison. -/
def standardFreeCarrierDerivedInverseIso (n : I) :
    standardFreeHo.{u, v} n ⋙ originalSphereHoEquivalence.{u, v}.inverse ≅
      standardFreeHo.{u, v} n ⋙ toRightDerivedAdjunctionData.{u, v}.rightDerived :=
  Functor.isoWhiskerLeft (standardFreeHo n) toRightCarrierRightComparison

/-- The whole chosen Free comparison commutes with the actual carrier-to-derived inverse map. -/
theorem originalFreeCarrierDerivedInverse_square (n : I) :
    (convertedStandardFreeCarrierInverseIso n).hom ≫
        (standardFreeCarrierDerivedInverseIso n).hom =
      (convertedFreeCarrierDerivedInverseIso n).hom ≫
        (convertedStandardFreeDerivedInverseIso n).hom := by
  ext X
  exact toRightCarrierRightComparison.hom.naturality ((convertedStandardFreeHoIso n).hom.app X)

/-- The standard original Free has its complete forward-derived adjunct function. -/
theorem standardFree_forwardHom (n : I) (A : originalLeftHo.{u, v})
    (X : PointedCGWH.{u, v}) :
    toRightDerivedAdjunctionData.adjunction.homEquiv A ((standardFreeHo n).obj X) =
      toRightCarrierHomEquiv A ((standardFreeHo n).obj X) :=
  toRightDerived_carrierHomEquiv A _

/-- The converted-left original Free keeps its distinct full forward-derived adjunct function. -/
theorem convertedFree_forwardHom (n : I) (A : originalLeftHo.{u, v})
    (X : PointedCGWH.{u, v}) :
    toRightDerivedAdjunctionData.adjunction.homEquiv A ((convertedFreeHo n).obj X) =
      toRightCarrierHomEquiv A ((convertedFreeHo n).obj X) :=
  toRightDerived_carrierHomEquiv A _

/-- Naturality of the entire original Hom function through the chosen projected Free map. -/
theorem originalFree_forwardHom_square (n : I) (A : originalLeftHo.{u, v})
    (X : PointedCGWH.{u, v})
    (f : toRightDerivedAdjunctionData.leftDerived.obj A ⟶ (convertedFreeHo n).obj X) :
    toRightCarrierHomEquiv A ((standardFreeHo n).obj X)
        (f ≫ (convertedStandardFreeHoIso n).hom.app X) =
      toRightCarrierHomEquiv A ((convertedFreeHo n).obj X) f ≫
        toRightDerivedAdjunctionData.rightDerived.map ((convertedStandardFreeHoIso n).hom.app X) :=
  toRightCarrierHom_rightNaturality f _

/-- Every full inverse adjunct respects the same actual original chosen Free comparison. -/
theorem originalFree_inverseHom_square (n : I) (A : originalLeftHo.{u, v})
    (X : PointedCGWH.{u, v})
    (g : A ⟶ toRightDerivedAdjunctionData.rightDerived.obj ((convertedFreeHo n).obj X)) :
    (toRightCarrierHomEquiv A ((standardFreeHo n).obj X)).symm
        (g ≫ toRightDerivedAdjunctionData.rightDerived.map
          ((convertedStandardFreeHoIso n).hom.app X)) =
      (toRightCarrierHomEquiv A ((convertedFreeHo n).obj X)).symm g ≫
        (convertedStandardFreeHoIso n).hom.app X :=
  toRightCarrierHom_inverseRightNaturality g _

end PointedCGWH.Spectra.Symmetric.RightPresentationModel

namespace PointedCGWH.Spectra.Symmetric.RightPresentationModel.Canonical

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel

open LeftRightNativeModel.Canonical

/-- The full original converted LEFT Free followed by the actual RIGHT model projection. -/
abbrev convertedFreeHo (n : I) : PointedCGWH.{u, v} ⥤ PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v} :=
  freeAt n ⋙ PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection

/-- The literal original standard RIGHT Free keeps its full original coefficient functor. -/
abbrev standardFreeHo (n : I) : PointedCGWH.{u, v} ⥤ PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v} :=
  standardFreeAt n ⋙ PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection

/-- The actual original source Free comparison projected as an entire natural isomorphism. -/
def convertedStandardFreeHoIso (n : I) : convertedFreeHo.{u, v} n ≅ standardFreeHo.{u, v} n :=
  Functor.isoWhiskerRight (convertedStandardFreeIso n) PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection

theorem convertedStandardFreeHoIso_hom (n : I) (X : PointedCGWH.{u, v}) :
    (convertedStandardFreeHoIso n).hom.app X =
      PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.map ((convertedStandardFreeIso n).hom.app X) := rfl

theorem convertedStandardFreeHoIso_inv (n : I) (X : PointedCGWH.{u, v}) :
    (convertedStandardFreeHoIso n).inv.app X =
      PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.map ((convertedStandardFreeIso n).inv.app X) := rfl

theorem convertedStandardFreeHo_hom_naturality (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (convertedFreeHo n).map f ≫ (convertedStandardFreeHoIso n).hom.app Y =
      (convertedStandardFreeHoIso n).hom.app X ≫ (standardFreeHo n).map f :=
  (convertedStandardFreeHoIso n).hom.naturality f

theorem convertedStandardFreeHo_inv_naturality (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (standardFreeHo n).map f ≫ (convertedStandardFreeHoIso n).inv.app Y =
      (convertedStandardFreeHoIso n).inv.app X ≫ (convertedFreeHo n).map f :=
  (convertedStandardFreeHoIso n).inv.naturality f

/-- Every full original coefficient Arrow retains both chosen Free maps after projection. -/
def convertedStandardFreeHoArrowIso (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CategoryTheory.Arrow.mk ((convertedFreeHo n).map f) ≅
      CategoryTheory.Arrow.mk ((standardFreeHo n).map f) :=
  PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.mapArrow.mapIso (convertedStandardFreeArrowIso n f)

theorem convertedStandardFreeHo_hom_inv (n : I) (X : PointedCGWH.{u, v}) :
    (convertedStandardFreeHoIso n).hom.app X ≫ (convertedStandardFreeHoIso n).inv.app X = 𝟙 _ :=
  (convertedStandardFreeHoIso n).hom_inv_id_app X

theorem convertedStandardFreeHo_inv_hom (n : I) (X : PointedCGWH.{u, v}) :
    (convertedStandardFreeHoIso n).inv.app X ≫ (convertedStandardFreeHoIso n).hom.app X = 𝟙 _ :=
  (convertedStandardFreeHoIso n).inv_hom_id_app X

/-- Transport both whole original Free functors by the actual strict inverse sphere Ho lift. -/
def convertedStandardFreeCarrierInverseIso (n : I) :
    convertedFreeHo.{u, v} n ⋙ originalSphereHoEquivalence.{u, v}.inverse ≅
      standardFreeHo.{u, v} n ⋙ originalSphereHoEquivalence.{u, v}.inverse :=
  Functor.isoWhiskerRight (convertedStandardFreeHoIso n) originalSphereHoEquivalence.inverse

/-- Transport the same chosen source Free comparison through the actual canonical inverse. -/
def convertedStandardFreeDerivedInverseIso (n : I) :
    convertedFreeHo.{u, v} n ⋙ toRightDerivedAdjunctionData.{u, v}.rightDerived ≅
      standardFreeHo.{u, v} n ⋙ toRightDerivedAdjunctionData.{u, v}.rightDerived :=
  Functor.isoWhiskerRight (convertedStandardFreeHoIso n) toRightDerivedAdjunctionData.rightDerived

/-- The original converted Free carrier inverse keeps the given whole canonical comparison. -/
def convertedFreeCarrierDerivedInverseIso (n : I) :
    convertedFreeHo.{u, v} n ⋙ originalSphereHoEquivalence.{u, v}.inverse ≅
      convertedFreeHo.{u, v} n ⋙ toRightDerivedAdjunctionData.{u, v}.rightDerived :=
  Functor.isoWhiskerLeft (convertedFreeHo n) toRightCarrierRightComparison

/-- The standard original RIGHT Free retains its own full canonical inverse comparison. -/
def standardFreeCarrierDerivedInverseIso (n : I) :
    standardFreeHo.{u, v} n ⋙ originalSphereHoEquivalence.{u, v}.inverse ≅
      standardFreeHo.{u, v} n ⋙ toRightDerivedAdjunctionData.{u, v}.rightDerived :=
  Functor.isoWhiskerLeft (standardFreeHo n) toRightCarrierRightComparison

/-- The whole chosen Free comparison commutes with the actual carrier-to-derived inverse map. -/
theorem originalFreeCarrierDerivedInverse_square (n : I) :
    (convertedStandardFreeCarrierInverseIso n).hom ≫
        (standardFreeCarrierDerivedInverseIso n).hom =
      (convertedFreeCarrierDerivedInverseIso n).hom ≫
        (convertedStandardFreeDerivedInverseIso n).hom := by
  ext X
  exact toRightCarrierRightComparison.hom.naturality ((convertedStandardFreeHoIso n).hom.app X)

/-- The standard original Free has its complete forward-derived adjunct function. -/
theorem standardFree_forwardHom (n : I) (A : originalLeftHo.{u, v})
    (X : PointedCGWH.{u, v}) :
    toRightDerivedAdjunctionData.adjunction.homEquiv A ((standardFreeHo n).obj X) =
      toRightCarrierHomEquiv A ((standardFreeHo n).obj X) :=
  toRightDerived_carrierHomEquiv A _

/-- The converted-left original Free keeps its distinct full forward-derived adjunct function. -/
theorem convertedFree_forwardHom (n : I) (A : originalLeftHo.{u, v})
    (X : PointedCGWH.{u, v}) :
    toRightDerivedAdjunctionData.adjunction.homEquiv A ((convertedFreeHo n).obj X) =
      toRightCarrierHomEquiv A ((convertedFreeHo n).obj X) :=
  toRightDerived_carrierHomEquiv A _

/-- Naturality of the entire original Hom function through the chosen projected Free map. -/
theorem originalFree_forwardHom_square (n : I) (A : originalLeftHo.{u, v})
    (X : PointedCGWH.{u, v})
    (f : toRightDerivedAdjunctionData.leftDerived.obj A ⟶ (convertedFreeHo n).obj X) :
    toRightCarrierHomEquiv A ((standardFreeHo n).obj X)
        (f ≫ (convertedStandardFreeHoIso n).hom.app X) =
      toRightCarrierHomEquiv A ((convertedFreeHo n).obj X) f ≫
        toRightDerivedAdjunctionData.rightDerived.map ((convertedStandardFreeHoIso n).hom.app X) :=
  toRightCarrierHom_rightNaturality f _

/-- Every full inverse adjunct respects the same actual original chosen Free comparison. -/
theorem originalFree_inverseHom_square (n : I) (A : originalLeftHo.{u, v})
    (X : PointedCGWH.{u, v})
    (g : A ⟶ toRightDerivedAdjunctionData.rightDerived.obj ((convertedFreeHo n).obj X)) :
    (toRightCarrierHomEquiv A ((standardFreeHo n).obj X)).symm
        (g ≫ toRightDerivedAdjunctionData.rightDerived.map
          ((convertedStandardFreeHoIso n).hom.app X)) =
      (toRightCarrierHomEquiv A ((convertedFreeHo n).obj X)).symm g ≫
        (convertedStandardFreeHoIso n).hom.app X :=
  toRightCarrierHom_inverseRightNaturality g _


/-- Native evaluation retains the same complete original degree label. -/
def evaluation (n : I) : Spectrum.{u, v} ⥤ PointedCGWH.{u, v} :=
  EnrichedFunctorCat.evaluation (symmetricOperatorObj.{u, v} n)

/-- The actual inverse right presentation retains the original standard evaluation. -/
def inverseStandardEvaluationIso (n : I) :
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.inverse ⋙
      RightPresentationModel.standardEvaluation.{u, v} n ≅ evaluation.{u, v} n :=
  Functor.isoWhiskerLeft SymmetricRightModulePresentation.rightModuleOperatorEquivalence.inverse
      (RightPresentationModel.standardEvaluationIso n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight SymmetricRightModulePresentation.rightModuleOperatorEquivalence.counitIso
        (evaluation n) ≪≫ Functor.leftUnitor (evaluation n)

/-- Converted-left evaluation keeps its distinct original source interface. -/
def inverseConvertedEvaluationIso (n : I) :
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.inverse ⋙
      RightPresentationModel.evaluation.{u, v} n ≅ evaluation.{u, v} n :=
  eqToIso (congrArg (fun F =>
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.inverse ⋙ F)
      (RightPresentationModel.standardConvertedEvaluation_eq n).symm) ≪≫
    inverseStandardEvaluationIso n

/-- The standard native free/evaluation adjunction is the full original adjunction
composed with the actual operator equivalence and its given evaluation comparison. -/
def standardFreeAdjunction (n : I) : standardFreeAt.{u, v} n ⊣ evaluation.{u, v} n :=
  ((RightPresentationModel.standardFreeAdjunction n).comp
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.toAdjunction).ofNatIsoRight
      (inverseStandardEvaluationIso n)

/-- The converted native free/evaluation adjunction retains its own original unit and counit. -/
def freeAtEvaluationAdjunction (n : I) : freeAt.{u, v} n ⊣ evaluation.{u, v} n :=
  ((RightPresentationModel.freeAtEvaluationAdjunction n).comp
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.toAdjunction).ofNatIsoRight
      (inverseConvertedEvaluationIso n)

/-- Every standard native adjunct is the whole original composed adjunct and given comparison. -/
theorem standardFreeAdjunction_homEquiv (n : I) (X : PointedCGWH.{u, v}) (F : Spectrum.{u, v})
    (f : (standardFreeAt n).obj X ⟶ F) :
    (standardFreeAdjunction n).homEquiv X F f =
      ((RightPresentationModel.standardFreeAdjunction n).comp
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.toAdjunction).homEquiv X F f ≫
          (inverseStandardEvaluationIso n).hom.app F :=
  Adjunction.homEquiv_ofNatIsoRight_apply
    ((RightPresentationModel.standardFreeAdjunction n).comp
      SymmetricRightModulePresentation.rightModuleOperatorEquivalence.toAdjunction)
    (inverseStandardEvaluationIso n) f

/-- Every converted native adjunct keeps the distinct complete original composed adjunct. -/
theorem freeAtEvaluationAdjunction_homEquiv (n : I) (X : PointedCGWH.{u, v}) (F : Spectrum.{u, v})
    (f : (freeAt n).obj X ⟶ F) :
    (freeAtEvaluationAdjunction n).homEquiv X F f =
      ((RightPresentationModel.freeAtEvaluationAdjunction n).comp
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.toAdjunction).homEquiv X F f ≫
          (inverseConvertedEvaluationIso n).hom.app F :=
  Adjunction.homEquiv_ofNatIsoRight_apply
    ((RightPresentationModel.freeAtEvaluationAdjunction n).comp
      SymmetricRightModulePresentation.rightModuleOperatorEquivalence.toAdjunction)
    (inverseConvertedEvaluationIso n) f

/-- The original standard native adjunction is Quillen for the canonical level model. -/
theorem standardFreeAdjunction_isQuillen (n : I) :
    (standardFreeAdjunction.{u, v} n).IsQuillenAdjunction := by
  let adj := EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v})
    (symmetricOperatorObj.{u, v} n)
  let _ : adj.IsQuillenAdjunction := PointedCGWH.Spectra.Symmetric.freeAtEvaluation_isQuillenAdjunction
    (symmetricOperatorObj n)
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (fun _ _ f hf => (inferInstance : adj.IsQuillenAdjunction).preservesFibrations f hf)
    (fun _ _ f hf => (inferInstance : adj.IsQuillenAdjunction).preservesTrivialFibrations f hf)

/-- The distinct converted native adjunction is Quillen for that same constructed model. -/
theorem freeAtEvaluation_isQuillenAdjunction (n : I) :
    (freeAtEvaluationAdjunction.{u, v} n).IsQuillenAdjunction := by
  let adj := EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v})
    (symmetricOperatorObj.{u, v} n)
  let _ : adj.IsQuillenAdjunction := PointedCGWH.Spectra.Symmetric.freeAtEvaluation_isQuillenAdjunction
    (symmetricOperatorObj n)
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (fun _ _ f hf => (inferInstance : adj.IsQuillenAdjunction).preservesFibrations f hf)
    (fun _ _ f hf => (inferInstance : adj.IsQuillenAdjunction).preservesTrivialFibrations f hf)

end PointedCGWH.Spectra.Symmetric.RightPresentationModel.Canonical
