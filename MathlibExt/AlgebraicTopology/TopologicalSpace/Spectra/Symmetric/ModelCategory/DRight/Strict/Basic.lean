/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.Strict.Factorization
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.FreeEvaluation
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.StrictGenerators

/-!
# Right-module classes in the strict source presentation

At the realized generator cardinal and a chosen ordinal bottom, the strict
presentation of the native right-module model detects weak equivalences,
fibrations and trivial fibrations at every degree. Cofibrations and trivial
cofibrations are the left lifting classes of the boundary and horn free
families, whose images agree with the strict generators up to isomorphism
closure. Comparing the standard right free/evaluation adjunction with the
strict source adjunction gives a Quillen adjunction at each degree.
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

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The strict D_R source weakEquivalences class uses every literal original RIGHT component. -/
theorem strict_weakEquivalences_iff {M N : Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} :=
      EnrichedProjective.BasedNativePresentation.strictModelCategory
    weakEquivalences StrictSourceCarrier.{u, v} (strictPresentation.functor.map f) ↔
      ∀ n : I, weakEquivalences PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  (EnrichedProjective.NativePresentation.strictSource_weakEquivalences_iff presentation f).trans
    (weakEquivalences_iff f)

/-- The strict D_R source fibrations class uses every literal original RIGHT component. -/
theorem strict_fibrations_iff {M N : Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} :=
      EnrichedProjective.BasedNativePresentation.strictModelCategory
    fibrations StrictSourceCarrier.{u, v} (strictPresentation.functor.map f) ↔
      ∀ n : I, fibrations PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  (EnrichedProjective.NativePresentation.strictSource_fibrations_iff presentation f).trans
    (fibrations_iff f)

/-- The strict D_R source trivialFibrations class uses every literal original RIGHT component. -/
theorem strict_trivialFibrations_iff {M N : Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} :=
      EnrichedProjective.BasedNativePresentation.strictModelCategory
    trivialFibrations StrictSourceCarrier.{u, v} (strictPresentation.functor.map f) ↔
      ∀ n : I, trivialFibrations PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  (EnrichedProjective.NativePresentation.strictSource_trivialFibrations_iff presentation f).trans
    (trivialFibrations_iff f)

/-- The full literal original standard RIGHT free family retains its strict cofibrations class. -/
theorem strict_cofibrations_iff {M N : Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} :=
      EnrichedProjective.BasedNativePresentation.strictModelCategory
    cofibrations StrictSourceCarrier.{u, v} (strictPresentation.functor.map f) ↔
      boundaryGenerators.{u, v}.rlp.llp f :=
  (EnrichedProjective.NativePresentation.strictSource_cofibrations_iff presentation f).trans
    (Iff.of_eq (congrArg (fun P : MorphismProperty Carrier.{u, v} => P f) cofibrations_eq))

/-- The full literal original standard RIGHT free family retains its strict trivialCofibrations
  class. -/
theorem strict_trivialCofibrations_iff {M N : Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} :=
      EnrichedProjective.BasedNativePresentation.strictModelCategory
    trivialCofibrations StrictSourceCarrier.{u, v} (strictPresentation.functor.map f) ↔
      hornGenerators.{u, v}.rlp.llp f :=
  (EnrichedProjective.NativePresentation.strictSource_trivialCofibrations_iff presentation f).trans
    (Iff.of_eq (congrArg (fun P : MorphismProperty Carrier.{u, v} => P f) trivialCofibrations_eq))

omit [OrderBot realizedGeneratorCardinal.{v}.ord.ToType] in
/-- The whole original standard RIGHT I family is precisely the literal strict source family. -/
theorem strict_original_I_family_map : boundaryGenerators.{u, v}.map strictPresentation.functor =
    (MorphismProperty.adjointFamilyGenerators
      (EnrichedProjective.BasedNativePresentation.strictFreeAt
        (A := PointedCGWH.SymmetricDRight.Index))
      PointedCGWH.realizedBoundaryInclusions.{u, v}).isoClosure :=
  EnrichedProjective.NativePresentation.strictSourceGenerators_map_eq presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardFreeAt
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardEvaluation
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardFreeAdjunction evaluationIso
    PointedCGWH.realizedBoundaryInclusions

omit [OrderBot realizedGeneratorCardinal.{v}.ord.ToType] in
/-- The whole original standard RIGHT J family is precisely the literal strict source family. -/
theorem strict_original_J_family_map : hornGenerators.{u, v}.map strictPresentation.functor =
    (MorphismProperty.adjointFamilyGenerators
      (EnrichedProjective.BasedNativePresentation.strictFreeAt
        (A := PointedCGWH.SymmetricDRight.Index))
      PointedCGWH.realizedHornInclusions.{u, v}).isoClosure :=
  EnrichedProjective.NativePresentation.strictSourceGenerators_map_eq presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardFreeAt
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardEvaluation
    PointedCGWH.Spectra.Symmetric.RightPresentationModel.standardFreeAdjunction evaluationIso
    PointedCGWH.realizedHornInclusions

/-- The whole actual original standard RIGHT free functor has the exact strict source comparison. -/
def strictFreeComparison (n : I) :
    PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} n ⋙
      strictPresentation.functor ≅ EnrichedProjective.BasedNativePresentation.strictFreeAt
        (PointedCGWH.SymmetricDRight.obj n) :=
  EnrichedProjective.NativePresentation.strictSourceFreeIso presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n) (evaluationIso n)

/-- The actual original chosen adjunction composes with the genuine full strict source
  equivalence. -/
def strictOriginalAdjunction (n : I) :
    PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} n ⋙
      strictPresentation.functor ⊣ EnrichedProjective.BasedNativePresentation.strictEvaluation
        (PointedCGWH.SymmetricDRight.obj n) :=
  EnrichedProjective.NativePresentation.strictSourceOriginalAdjunction presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n) (evaluationIso n)

/-- The actual original standard RIGHT free adjunction is Quillen in literal strict source
  diagrams. -/
theorem strictOriginalAdjunction_isQuillen (n : I) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} :=
      EnrichedProjective.BasedNativePresentation.strictModelCategory
    (strictOriginalAdjunction n).IsQuillenAdjunction :=
  EnrichedProjective.NativePresentation.strictSourceOriginalAdjunction_isQuillen presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n) (evaluationIso n)

end PointedCGWH.Spectra.Symmetric.DRightPresentation
