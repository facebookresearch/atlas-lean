/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.StandardRightMigration
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.LeftRightConversion

/-!
# The chosen converted-left and standard-right free comparison

The actual original converted LEFT free and literal standard RIGHT free remain separate functors.
Their comparison is the existing chosen internal-module free comparison, composed with the exact
ordinary free diagram and Day wrapper. All original generator labels and whole Arrow maps are kept.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory MorphismProperty
open scoped MonoidalClosed CGWH.modelCategory CGWH.limits

namespace PointedCGWH.Spectra.Symmetric.RightPresentationModel

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual original converted LEFT free has the same full ordinary/Day diagram stage. -/
theorem convertedFree_diagram_stage (n : I) :
    freeAt.{u, v} n = SymmetricStandardRightFreeEvaluation.diagramFreeFunctor.{u, v} n ⋙
      RightModuleFree.convertedLeftFree sphereSequence.{u, v} := by
  change SymmetricRightFreeEvaluation.originalFreeFunctor.{u, v} n = _
  rw [SymmetricRightFreeEvaluation.originalFreeFunctor_eq,
    SymmetricStandardRightFreeEvaluation.diagramFreeFunctor_eq,
    RightModuleFree.convertedLeftFree_eq]
  rfl

/-- The literal original standard RIGHT free keeps its whole diagram and standard tensor stage. -/
theorem standardFree_diagram_stage (n : I) :
    standardFreeAt.{u, v} n = SymmetricStandardRightFreeEvaluation.diagramFreeFunctor.{u, v} n ⋙
      RightModuleFree.functor sphereSequence.{u, v} := rfl

/-- Compare the two actual free choices using the original chosen internal-module comparison. -/
def convertedStandardFreeIso (n : I) : freeAt.{u, v} n ≅ standardFreeAt.{u, v} n :=
  eqToIso (convertedFree_diagram_stage n) ≪≫
    Functor.isoWhiskerLeft (SymmetricStandardRightFreeEvaluation.diagramFreeFunctor.{u, v} n)
      (RightModuleFree.freeComparison sphereSequence.{u, v}) ≪≫
        (eqToIso (standardFree_diagram_stage n)).symm

/-- Both entire free object maps compare through the same original ordinary diagram coefficient. -/
theorem convertedStandardFreeIso_hom_naturality (n : I) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) :
    (freeAt n).map f ≫ (convertedStandardFreeIso n).hom.app Y =
      (convertedStandardFreeIso n).hom.app X ≫ (standardFreeAt n).map f :=
  (convertedStandardFreeIso n).hom.naturality f

/-- The actual inverse recovers every complete original standard free coefficient map. -/
theorem convertedStandardFreeIso_inv_naturality (n : I) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) :
    (standardFreeAt n).map f ≫ (convertedStandardFreeIso n).inv.app Y =
      (convertedStandardFreeIso n).inv.app X ≫ (freeAt n).map f :=
  (convertedStandardFreeIso n).inv.naturality f

/-- Every full original free Arrow compares with its correlated coefficient and degree label. -/
def convertedStandardFreeArrowIso (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CategoryTheory.Arrow.mk ((freeAt n).map f) ≅
      CategoryTheory.Arrow.mk ((standardFreeAt n).map f) :=
  CategoryTheory.Arrow.isoOfNatIso (convertedStandardFreeIso n) (CategoryTheory.Arrow.mk f)

/-- An arbitrary iso-invariant source class compares on the whole original free arrows. -/
theorem convertedStandardFreeArrowClass_iff (n : I) (P : MorphismProperty
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    [P.RespectsIso] {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    P ((freeAt n).map f) ↔ P ((standardFreeAt n).map f) :=
  P.arrow_mk_iso_iff (convertedStandardFreeArrowIso n f)

/-- Every original level retains the complete comparison of converted and standard free maps. -/
theorem convertedStandardFreeIso_level_naturality (n k : I) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) :
    ((freeAt n).map f).hom.natTrans.app k ≫
        ((convertedStandardFreeIso n).hom.app Y).hom.natTrans.app k =
      ((convertedStandardFreeIso n).hom.app X).hom.natTrans.app k ≫
        ((standardFreeAt n).map f).hom.natTrans.app k := by
  exact congrArg (fun g => (evaluation k).map g)
    (convertedStandardFreeIso_hom_naturality n f)

/-- The inverse restores the full original free carrier at every original degree. -/
theorem convertedStandardFreeIso_level_hom_inv (n k : I) (X : PointedCGWH.{u, v}) :
    ((convertedStandardFreeIso n).hom.app X).hom.natTrans.app k ≫
      ((convertedStandardFreeIso n).inv.app X).hom.natTrans.app k = 𝟙 _ := by
  exact congrArg (fun g => (evaluation k).map g) ((convertedStandardFreeIso n).hom_inv_id_app X)

/-- Both inverse level maps recover the literal original standard RIGHT free carrier. -/
theorem convertedStandardFreeIso_level_inv_hom (n k : I) (X : PointedCGWH.{u, v}) :
    ((convertedStandardFreeIso n).inv.app X).hom.natTrans.app k ≫
      ((convertedStandardFreeIso n).hom.app X).hom.natTrans.app k = 𝟙 _ := by
  exact congrArg (fun g => (evaluation k).map g) ((convertedStandardFreeIso n).inv_hom_id_app X)

/-- Literal converted and standard evaluations are the same full original sequence functor. -/
theorem standardConvertedEvaluation_eq (n : I) :
    standardEvaluation.{u, v} n = evaluation.{u, v} n := rfl

/-- Right lifting for any whole original base family is independent of the actual free choice. -/
theorem convertedStandardGenerators_rlp_eq (P : MorphismProperty PointedCGWH.{u, v}) :
    (MorphismProperty.adjointFamilyGenerators freeAt.{u, v} P).rlp =
      (MorphismProperty.adjointFamilyGenerators standardFreeAt.{u, v} P).rlp := by
  ext X Y f
  rw [MorphismProperty.adjointFamilyGenerators_rlp_iff freeAt evaluation
      freeAtEvaluationAdjunction P,
    MorphismProperty.adjointFamilyGenerators_rlp_iff standardFreeAt standardEvaluation
      standardFreeAdjunction P]
  simp only [standardConvertedEvaluation_eq]

/-- The original boundary family retains all labels and the same full lifting class. -/
theorem convertedStandardBoundaryGenerators_rlp_eq :
    boundaryGenerators.{u, v}.rlp = standardBoundaryGenerators.{u, v}.rlp :=
  convertedStandardGenerators_rlp_eq realizedBoundaryInclusions.{u, v}

/-- The original horn family keeps every label and the identical full right lifting class. -/
theorem convertedStandardHornGenerators_rlp_eq :
    hornGenerators.{u, v}.rlp = standardHornGenerators.{u, v}.rlp :=
  convertedStandardGenerators_rlp_eq realizedHornInclusions.{u, v}

/-- The full original boundary-generated left class is unchanged by the chosen free comparison. -/
theorem convertedStandardBoundaryGenerators_rlp_llp_eq :
    boundaryGenerators.{u, v}.rlp.llp = standardBoundaryGenerators.{u, v}.rlp.llp :=
  congrArg MorphismProperty.llp convertedStandardBoundaryGenerators_rlp_eq

/-- The full original horn-generated left class retains the same chosen coefficient labels. -/
theorem convertedStandardHornGenerators_rlp_llp_eq :
    hornGenerators.{u, v}.rlp.llp = standardHornGenerators.{u, v}.rlp.llp :=
  congrArg MorphismProperty.llp convertedStandardHornGenerators_rlp_eq

end PointedCGWH.Spectra.Symmetric.RightPresentationModel

namespace PointedCGWH.Spectra.Symmetric.RightPresentationModel.Canonical

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction
  PointedCGWH.Spectra.Symmetric.levelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual original converted-left free functor with canonical spectrum endpoints. -/
def freeAt (n : I) : PointedCGWH.{u, v} ⥤ Spectrum.{u, v} :=
  RightPresentationModel.freeAt.{u, v} n ⋙ SymmetricRightModulePresentation.rightModuleToOperator

/-- The distinct actual standard-right free functor with those same canonical endpoints. -/
def standardFreeAt (n : I) : PointedCGWH.{u, v} ⥤ Spectrum.{u, v} :=
  RightPresentationModel.standardFreeAt.{u, v} n ⋙
    SymmetricRightModulePresentation.rightModuleToOperator

/-- The native comparison retains the original chosen whole source free comparison. -/
def convertedStandardFreeIso (n : I) : freeAt.{u, v} n ≅ standardFreeAt.{u, v} n :=
  Functor.isoWhiskerRight (RightPresentationModel.convertedStandardFreeIso n)
    SymmetricRightModulePresentation.rightModuleToOperator

/-- Every complete original coefficient arrow retains its two native free maps. -/
def convertedStandardFreeArrowIso (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CategoryTheory.Arrow.mk ((freeAt n).map f) ≅ CategoryTheory.Arrow.mk ((standardFreeAt n).map f) :=
  SymmetricRightModulePresentation.rightModuleToOperator.mapArrow.mapIso
    (RightPresentationModel.convertedStandardFreeArrowIso n f)

/-- The full chosen standard free comparison reaches the original enriched native free. -/
def mappedStandardFreeIso (n : I) : standardFreeAt.{u, v} n ≅
    EnrichedFunctorCat.Free.functor (symmetricOperatorObj.{u, v} n) :=
  RightPresentationModel.mappedStandardFreeIso n

/-- Converted-left free reaches native free through its own original chosen comparison. -/
def mappedConvertedFreeIso (n : I) : freeAt.{u, v} n ≅
    EnrichedFunctorCat.Free.functor (symmetricOperatorObj.{u, v} n) :=
  convertedStandardFreeIso n ≪≫ mappedStandardFreeIso n

/-- The native standard free map is exactly the original whole mapped source map. -/
theorem standardFreeAt_map (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (standardFreeAt n).map f = SymmetricRightModulePresentation.rightModuleToOperator.map
      ((RightPresentationModel.standardFreeAt n).map f) := rfl

/-- The native converted free map retains its distinct complete original source map. -/
theorem freeAt_map (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (freeAt n).map f = SymmetricRightModulePresentation.rightModuleToOperator.map
      ((RightPresentationModel.freeAt n).map f) := rfl

theorem convertedStandardFreeArrowClass_iff (n : I) (P : MorphismProperty Spectrum.{u, v})
    [P.RespectsIso] {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    P ((freeAt n).map f) ↔ P ((standardFreeAt n).map f) :=
  P.arrow_mk_iso_iff (convertedStandardFreeArrowIso n f)

theorem convertedStandardFreeIso_hom_naturality (n : I) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) :
    (freeAt n).map f ≫ (convertedStandardFreeIso n).hom.app Y =
      (convertedStandardFreeIso n).hom.app X ≫ (standardFreeAt n).map f :=
  (convertedStandardFreeIso n).hom.naturality f

theorem convertedStandardFreeIso_inv_naturality (n : I) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) :
    (standardFreeAt n).map f ≫ (convertedStandardFreeIso n).inv.app Y =
      (convertedStandardFreeIso n).inv.app X ≫ (freeAt n).map f :=
  (convertedStandardFreeIso n).inv.naturality f

end PointedCGWH.Spectra.Symmetric.RightPresentationModel.Canonical
