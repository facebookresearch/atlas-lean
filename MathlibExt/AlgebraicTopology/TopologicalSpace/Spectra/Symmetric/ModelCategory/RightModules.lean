/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.OriginalClasses
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Factorization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Generators
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Quillen
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.ConvertedRightFreeEvaluation

/-!
# Native model on actual original right sphere modules

The complete proved right-module/operator equivalence constructs this model.
Right levels and all whole original transformations identify the actual
classes. The derived original free functor is the original left Day free
followed by the actual right conversion. D_R remains a separate source join.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed ExternalProduct

namespace PointedCGWH.Spectra.Symmetric.RightPresentationModel

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

private abbrev presentation :=
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}

/-- Literal original evaluation of right sphere-module sequences. -/
abbrev evaluation (n : I) :=
  PointedCGWH.SymmetricRightFreeEvaluation.literalEvaluation.{u, v} n

/-- The derived original left Day free functor through the actual right conversion. -/
abbrev freeAt (n : I) :=
  PointedCGWH.SymmetricRightFreeEvaluation.originalFreeFunctor.{u, v} n

/-- Full native evaluation is the literal original right-module evaluation. -/
def evaluationIso (n : I) :
    presentation.functor ⋙ EnrichedFunctorCat.evaluation
      (PointedCGWH.symmetricOperatorObj.{u, v} n) ≅ evaluation.{u, v} n :=
  (eqToIso (PointedCGWH.SymmetricRightFreeEvaluation.nativeEvaluationFunctor_eq n)).symm ≪≫
    PointedCGWH.SymmetricRightFreeEvaluation.evaluationIso n ≪≫
      eqToIso (PointedCGWH.SymmetricRightFreeEvaluation.originalEvaluationFunctor_eq n)

/-- The actual derived right free adjunction retains literal original evaluation. -/
def freeAtEvaluationAdjunction (n : I) : freeAt.{u, v} n ⊣ evaluation.{u, v} n :=
  (PointedCGWH.SymmetricRightFreeEvaluation.originalAdjunction n).ofNatIsoRight
    (eqToIso (PointedCGWH.SymmetricRightFreeEvaluation.originalEvaluationFunctor_eq n))

/-- All original finite-bijection labels cover the entire actual native operator index. -/
theorem operatorObj_surjective : Function.Surjective PointedCGWH.symmetricOperatorObj.{u, v} := by
  intro a
  rcases a with ⟨n⟩
  exact ⟨(show I from n), rfl⟩

/-- Full original labels of the derived right-module free-I family. -/
def boundaryGenerators : MorphismProperty PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
  MorphismProperty.adjointFamilyGenerators freeAt.{u, v}
    PointedCGWH.realizedBoundaryInclusions.{u, v}

/-- Full original labels of the derived right-module free-J family. -/
def hornGenerators : MorphismProperty PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
  MorphismProperty.adjointFamilyGenerators freeAt.{u, v}
    PointedCGWH.realizedHornInclusions.{u, v}

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Original right-module weak equivalences are detected on all original level maps. -/
theorem weakEquivalences_iff {M N : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} f ↔
      ∀ n : I, weakEquivalences PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  EnrichedProjective.NativePresentation.weakEquivalences_iff_original presentation
    PointedCGWH.symmetricOperatorObj operatorObj_surjective evaluation evaluationIso f

/-- Original right-module fibrations are detected on all original level maps. -/
theorem fibrations_iff {M N : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    fibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} f ↔
      ∀ n : I, fibrations PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  EnrichedProjective.NativePresentation.fibrations_iff_original presentation
    PointedCGWH.symmetricOperatorObj operatorObj_surjective evaluation evaluationIso f

/-- Original right-module trivial fibrations are detected on all original level maps. -/
theorem trivialFibrations_iff {M N : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : M ⟶ N)
  :
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    trivialFibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} f ↔
      ∀ n : I, trivialFibrations PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  EnrichedProjective.NativePresentation.trivialFibrations_iff_original presentation
    PointedCGWH.symmetricOperatorObj operatorObj_surjective evaluation evaluationIso f

/-- The entire original right free-I family gives the exact cofibration class. -/
theorem cofibrations_eq :
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    cofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} = boundaryGenerators.{u,
      v}.rlp.llp :=
  EnrichedProjective.NativePresentation.cofibrations_eq_originalGenerators presentation
    PointedCGWH.symmetricOperatorObj operatorObj_surjective freeAt evaluation
    freeAtEvaluationAdjunction evaluationIso

/-- The entire original right free-J family gives the exact trivial-cofibration class. -/
theorem trivialCofibrations_eq :
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    trivialCofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} = hornGenerators.{u,
      v}.rlp.llp :=
  EnrichedProjective.NativePresentation.trivialCofibrations_eq_originalGenerators presentation
    PointedCGWH.symmetricOperatorObj operatorObj_surjective freeAt evaluation
    freeAtEvaluationAdjunction evaluationIso

/-- The actual original right free/evaluation adjunction is Quillen. -/
theorem freeAtEvaluation_isQuillenAdjunction (n : I) :
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    (freeAtEvaluationAdjunction.{u, v} n).IsQuillenAdjunction :=
  EnrichedProjective.NativePresentation.originalFreeEvaluation_isQuillenAdjunction presentation
    (PointedCGWH.symmetricOperatorObj.{u, v} n) (freeAt n) (evaluation n)
    (freeAtEvaluationAdjunction n) (evaluationIso n)

/-- The entire right κ/I middle functor uses the actual full right-module inverse. -/
theorem cofibrantFactorizationData_Z :
  ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z =
    presentation.functor.mapArrow ⋙
      (EnrichedProjective.Native.cofibrantFactorizationData
        (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).Z ⋙
          PointedCGWH.SymmetricRightModulePresentation.operatorToRightModule.{u, v} := rfl

/-- The entire right κ/J middle functor uses the actual full right-module inverse. -/
theorem fibrantFactorizationData_Z : ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z =
    presentation.functor.mapArrow ⋙
      (EnrichedProjective.Native.fibrantFactorizationData
        (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).Z ⋙
          PointedCGWH.SymmetricRightModulePresentation.operatorToRightModule.{u, v} := rfl

/-- Actual original κ/I components factor the same whole right-module arrow. -/
theorem cofibrantFactorizationData_fac (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f = f.hom :=
  EnrichedProjective.NativePresentation.cofibrantFactorizationData_fac presentation f

/-- Actual original κ/J components factor the same whole right-module arrow. -/
theorem fibrantFactorizationData_fac (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f = f.hom :=
  EnrichedProjective.NativePresentation.fibrantFactorizationData_fac presentation f

end PointedCGWH.Spectra.Symmetric.RightPresentationModel
