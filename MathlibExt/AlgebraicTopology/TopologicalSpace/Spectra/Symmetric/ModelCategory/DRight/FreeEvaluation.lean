/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.Basic
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.MappedFreeHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Generators

/-!
# Original standard RIGHT free/evaluation maps on the actual original D_R source

All values use the actual original standard Mod.free adjunction and the
proved whole source equivalence. The complete Hom, unit/counit, generator
Arrow and correlated I/J comparisons retain the original source endpoints.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed ZeroObject CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual source free functor through the exact original module/source inverse. -/
def nativeFreeFunctor (n : I) : PointedCGWH.{u, v} ⥤ Carrier.{u, v} :=
  EnrichedProjective.NativePresentation.transportedFree presentation
    (PointedCGWH.SymmetricDRight.obj n)

/-- The actual source adjunction on the whole original standard RIGHT evaluation. -/
def migratedAdjunction (n : I) : nativeFreeFunctor.{u, v} n ⊣
    PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} n :=
  EnrichedProjective.NativePresentation.originalEvaluationAdjunction presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n) (evaluationIso n)

/-- The original standard RIGHT free is naturally the actual full native source free. -/
def freeComparison (n : I) :
    PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} n ≅
      nativeFreeFunctor.{u, v} n :=
  EnrichedProjective.NativePresentation.originalFreeIso presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n) (evaluationIso n)

/-- The complete original free functor maps to the actual full native source free functor. -/
def mappedFreeComparison (n : I) :
    PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} n ⋙
      presentation.functor ≅ EnrichedFunctorCat.Free.functor
        (PointedCGWH.SymmetricDRight.obj n) :=
  EnrichedProjective.NativePresentation.mappedOriginalFreeIso presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n) (evaluationIso n)

/-- Every original whole free morphism retains the actual forward source adjunct. -/
theorem freeComparison_homEquiv (n : I) {X : PointedCGWH.{u, v}} {M : Carrier.{u, v}}
    (f : (nativeFreeFunctor.{u, v} n).obj X ⟶ M) :
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n).homEquiv X M
      ((freeComparison n).hom.app X ≫ f) = (migratedAdjunction n).homEquiv X M f :=
  EnrichedProjective.NativePresentation.originalFreeIso_homEquiv_apply presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n) (evaluationIso n) f

/-- Every literal original inverse adjunct retains the actual full original map. -/
theorem freeComparison_homEquiv_symm (n : I) {X : PointedCGWH.{u, v}} {M : Carrier.{u, v}}
    (f : X ⟶ (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n).obj M) :
    (freeComparison n).hom.app X ≫ ((migratedAdjunction n).homEquiv X M).symm f =
      ((PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n).homEquiv X M).symm
        f :=
  EnrichedProjective.NativePresentation.originalFreeIso_homEquiv_symm presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n) (evaluationIso n) f

/-- The entire actual original standard RIGHT unit is preserved. -/
theorem freeComparison_unit (n : I) (X : PointedCGWH.{u, v}) :
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n).unit.app X ≫
      (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n).map
        ((freeComparison n).hom.app X) = (migratedAdjunction n).unit.app X :=
  EnrichedProjective.NativePresentation.originalFreeIso_unit presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n) (evaluationIso n) X

/-- The entire actual original standard RIGHT counit is preserved. -/
theorem freeComparison_counit (n : I) :
    Functor.whiskerLeft
      (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} n)
      (freeComparison n).hom ≫ (migratedAdjunction n).counit =
        (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n).counit :=
  Adjunction.leftAdjointUniq_hom_counit
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n)
    (migratedAdjunction n)

/-- The entire original counit equality also gives its exact component proof at every module. -/
theorem freeComparison_counit_app (n : I) (M : Carrier.{u, v}) :
    (Functor.whiskerLeft
      (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} n)
      (freeComparison n).hom ≫ (migratedAdjunction n).counit).app M =
        (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n).counit.app M :=
  congrArg (fun t => t.app M) (freeComparison_counit n)

/-- Every complete original generating arrow maps to the actual full source free arrow. -/
def freeGeneratorArrowIso (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CategoryTheory.Arrow.mk (presentation.functor.map
      ((PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n).map f)) ≅
        CategoryTheory.Arrow.mk ((EnrichedFunctorCat.Free.functor
          (PointedCGWH.SymmetricDRight.obj n)).map f) :=
  CategoryTheory.Arrow.isoOfNatIso (mappedFreeComparison n) (CategoryTheory.Arrow.mk f)

/-- The whole literal original RIGHT I family maps onto the source native I family. -/
theorem boundaryGenerators_map : boundaryGenerators.{u, v}.map presentation.functor =
    (EnrichedProjective.generators (A := PointedCGWH.SymmetricDRight.Index)
      PointedCGWH.realizedBoundaryInclusions.{u, v}).isoClosure :=
  EnrichedProjective.NativePresentation.originalGenerators_map_eq presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardFreeAt
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardEvaluation
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardFreeAdjunction evaluationIso
    PointedCGWH.realizedBoundaryInclusions

/-- The whole literal original RIGHT J family maps onto the source native J family. -/
theorem hornGenerators_map : hornGenerators.{u, v}.map presentation.functor =
    (EnrichedProjective.generators (A := PointedCGWH.SymmetricDRight.Index)
      PointedCGWH.realizedHornInclusions.{u, v}).isoClosure :=
  EnrichedProjective.NativePresentation.originalGenerators_map_eq presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardFreeAt
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardEvaluation
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardFreeAdjunction evaluationIso
    PointedCGWH.realizedHornInclusions

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The full native D_R source cofibration class is its literal source free-I left class. -/
theorem source_cofibrations_eq :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    cofibrations SourceCarrier.{u, v} =
      (EnrichedProjective.generators (A := PointedCGWH.SymmetricDRight.Index)
        PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp :=
  EnrichedProjective.Native.cofibrations_eq

/-- The full native D_R trivial-cofibration class is its literal source free-J left class. -/
theorem source_trivialCofibrations_eq :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    trivialCofibrations SourceCarrier.{u, v} =
      (EnrichedProjective.generators (A := PointedCGWH.SymmetricDRight.Index)
        PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp :=
  EnrichedProjective.Native.trivialCofibrations_eq


attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel

/-- The original standard RIGHT evaluation survives the actual given inverse. -/
def canonicalStandardInverseEvaluationIso (n : I) :
    canonicalPresentation.inverse ⋙ RightPresentationModel.standardEvaluation.{u, v} n ≅
      EnrichedFunctorCat.evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n) :=
  Functor.isoWhiskerLeft canonicalPresentation.inverse (RightPresentationModel.standardEvaluationIso n).symm ≪≫
    (Functor.associator canonicalPresentation.inverse canonicalPresentation.functor _).symm ≪≫
      Functor.isoWhiskerRight canonicalPresentation.counitIso _ ≪≫ Functor.leftUnitor _

/-- The actual original standard RIGHT adjunction lands on the canonical native carrier. -/
def canonicalStandardAdjunction (n : I) :
    RightPresentationModel.standardFreeAt.{u, v} n ⋙ canonicalPresentation.functor ⊣
      EnrichedFunctorCat.evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n) :=
  ((RightPresentationModel.standardFreeAdjunction n).comp canonicalPresentation.toAdjunction).ofNatIsoRight
    (canonicalStandardInverseEvaluationIso n)

/-- The full original standard RIGHT free arrow is the actual mapped canonical free arrow. -/
def canonicalStandardMappedFreeIso (n : I) :
    RightPresentationModel.standardFreeAt.{u, v} n ⋙ canonicalPresentation.functor ≅
      EnrichedFunctorCat.Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} n) :=
  EnrichedProjective.NativePresentation.mappedOriginalFreeIso canonicalPresentation (PointedCGWH.symmetricOperatorObj n)
    (RightPresentationModel.standardFreeAt n) (RightPresentationModel.standardEvaluation n)
    (RightPresentationModel.standardFreeAdjunction n) (RightPresentationModel.standardEvaluationIso n)

omit B in
set_option maxHeartbeats 600000 in
/-- All original standard free arrows use the canonical level model's genuine Quillen adjunction. -/
theorem canonicalStandardAdjunction_isQuillen (n : I) : (canonicalStandardAdjunction.{u, v} n).IsQuillenAdjunction := by
  let q : (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v})
      (PointedCGWH.symmetricOperatorObj.{u, v} n)).IsQuillenAdjunction :=
    PointedCGWH.Spectra.Symmetric.freeAtEvaluation_isQuillenAdjunction _
  let _ := q
  have h : ((EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v})
      (PointedCGWH.symmetricOperatorObj.{u, v} n)).ofNatIsoLeft
        (canonicalStandardMappedFreeIso n).symm).IsQuillenAdjunction := inferInstance
  exact {
    preservesCofibrations := h.preservesCofibrations
    preservesTrivialCofibrations := h.preservesTrivialCofibrations }


end PointedCGWH.Spectra.Symmetric.DRightPresentation
