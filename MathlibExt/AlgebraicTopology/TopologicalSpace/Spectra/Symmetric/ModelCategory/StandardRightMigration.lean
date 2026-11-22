/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.RightModuleMigration
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.MappedFreeHom
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StandardRightFreeEvaluation

/-!
# The actual standard RIGHT Day free and original native model classes

The source functor is the unchanged ordinary evaluation left adjoint,
original Day wrapper and actual Mod.free in the monoidal opposite.
Its carrier, maps and action keep X ⊗ S. The proved right-module equivalence
identifies its whole I/J families and the actual original-cardinal data.
The independent D_R mapping category is a separate source join.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.RightPresentationModel

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

private abbrev e := SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}
private abbrev j := symmetricOperatorObj.{u, v}
local notation "I" => Operad.SmallFinBijGroupoid

/-- The literal actual standard original RIGHT Day free functor. -/
abbrev standardFreeAt (n : I) :=
  SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} n

/-- The exact evaluation endpoint of the actual standard source adjunction. -/
abbrev standardEvaluation (n : I) :=
  SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} n

/-- Preserve the actual selected original ordinary/Day/right-module adjunction. -/
abbrev standardFreeAdjunction (n : I) :=
  SymmetricStandardRightFreeEvaluation.originalAdjunction.{u, v} n

/-- Actual native evaluation compares to the same original complete source evaluation. -/
def standardEvaluationIso (n : I) :
    e.functor ⋙ EnrichedFunctorCat.evaluation (j n) ≅ standardEvaluation.{u, v} n :=
  (eqToIso (SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor_eq n)).symm ≪≫
    SymmetricStandardRightFreeEvaluation.evaluationIso n

/-- The actual standard free comparison uses the whole original equivalence counit. -/
def mappedStandardFreeIso (n : I) :
    standardFreeAt.{u, v} n ⋙ e.functor ≅ EnrichedFunctorCat.Free.functor (j n) :=
  Functor.isoWhiskerRight (SymmetricStandardRightFreeEvaluation.freeComparison n) e.functor ≪≫
    Functor.isoWhiskerRight
      (eqToIso (SymmetricStandardRightFreeEvaluation.nativeFreeFunctor_eq n)) e.functor ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (EnrichedFunctorCat.Free.functor (j n)) e.counitIso ≪≫
            Functor.rightUnitor _

/-- Every literal original standard free arrow retains both entire endpoints and its map. -/
def standardFreeArrowIso (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CategoryTheory.Arrow.mk (e.functor.map ((standardFreeAt n).map f)) ≅
      CategoryTheory.Arrow.mk ((EnrichedFunctorCat.Free.functor (j n)).map f) :=
  CategoryTheory.Arrow.isoOfNatIso (mappedStandardFreeIso n) (CategoryTheory.Arrow.mk f)

/-- Every actual iso-invariant native class preserves the complete original standard free arrow. -/
theorem standardFreeArrowClass_iff (n : I)
    (P : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}))
    [P.RespectsIso] {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    P (e.functor.map ((standardFreeAt n).map f)) ↔
      P ((EnrichedFunctorCat.Free.functor (j n)).map f) :=
  P.arrow_mk_iso_iff (standardFreeArrowIso n f)

/-- The whole original standard RIGHT free-I family with correlated original labels. -/
def standardBoundaryGenerators : MorphismProperty PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
  :=
  MorphismProperty.adjointFamilyGenerators standardFreeAt
    realizedBoundaryInclusions.{u, v}

/-- The whole original standard RIGHT free-J family with correlated original labels. -/
def standardHornGenerators : MorphismProperty PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
  MorphismProperty.adjointFamilyGenerators standardFreeAt
    realizedHornInclusions.{u, v}

/-- The literal original standard I family maps onto precisely the full native Arrow closure. -/
theorem standardBoundaryGenerators_map : standardBoundaryGenerators.{u, v}.map e.functor =
    (EnrichedProjective.generators (A := SymmetricOperatorIndex.{u, v})
      realizedBoundaryInclusions.{u, v}).isoClosure :=
  EnrichedProjective.NativePresentation.originalGenerators_map_eq e j
    operatorObj_surjective standardFreeAt standardEvaluation standardFreeAdjunction
      standardEvaluationIso _

/-- The literal original standard J family maps onto precisely the full native Arrow closure. -/
theorem standardHornGenerators_map : standardHornGenerators.{u, v}.map e.functor =
    (EnrichedProjective.generators (A := SymmetricOperatorIndex.{u, v})
      realizedHornInclusions.{u, v}).isoClosure :=
  EnrichedProjective.NativePresentation.originalGenerators_map_eq e j
    operatorObj_surjective standardFreeAt standardEvaluation standardFreeAdjunction
      standardEvaluationIso _

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Original standard RIGHT free-I lifting is exactly the actual full trivial-fibration class. -/
theorem standard_trivialFibrations_eq :
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    trivialFibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} =
      standardBoundaryGenerators.{u, v}.rlp :=
  EnrichedProjective.NativePresentation.trivialFibrations_eq_originalGenerators e j
    operatorObj_surjective standardFreeAt standardEvaluation standardFreeAdjunction
      standardEvaluationIso

/-- Original standard RIGHT free-J lifting is exactly the actual full fibration class. -/
theorem standard_fibrations_eq :
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    fibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} = standardHornGenerators.{u, v}.rlp
      :=
  EnrichedProjective.NativePresentation.fibrations_eq_originalGenerators e j
    operatorObj_surjective standardFreeAt standardEvaluation standardFreeAdjunction
      standardEvaluationIso

/-- The actual cofibrations use the complete original standard RIGHT free-I family. -/
theorem standard_cofibrations_eq :
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    cofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} = standardBoundaryGenerators.{u,
      v}.rlp.llp :=
  EnrichedProjective.NativePresentation.cofibrations_eq_originalGenerators e j
    operatorObj_surjective standardFreeAt standardEvaluation standardFreeAdjunction
      standardEvaluationIso

/-- The actual trivial cofibrations use the complete original standard RIGHT free-J family. -/
theorem standard_trivialCofibrations_eq :
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    trivialCofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} =
      standardHornGenerators.{u, v}.rlp.llp :=
  EnrichedProjective.NativePresentation.trivialCofibrations_eq_originalGenerators e j
    operatorObj_surjective standardFreeAt standardEvaluation standardFreeAdjunction
      standardEvaluationIso

/-- The entire actual standard original free/evaluation adjunction is Quillen. -/
theorem standardFreeAdjunction_isQuillen (n : I) :
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    (standardFreeAdjunction.{u, v} n).IsQuillenAdjunction :=
  EnrichedProjective.NativePresentation.originalFreeEvaluation_isQuillenAdjunction
    e (j n) (standardFreeAt n) (standardEvaluation n)
      (standardFreeAdjunction n) (standardEvaluationIso n)

/-- The actual original κ/I data use the complete original standard RIGHT left class. -/
theorem cofibrantFactorizationData_standard_classes (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    standardBoundaryGenerators.{u, v}.rlp.llp
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f) ∧
      ∀ n : I, trivialFibrations PointedCGWH.{u, v}
        ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f).hom.natTrans.app
          n) := by
  let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
  exact ⟨Eq.mp (congrArg (fun P : MorphismProperty PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
    =>
    P (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f))
      standard_cofibrations_eq)
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hi f),
    (trivialFibrations_iff _).mp (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hp f)⟩

/-- The actual original κ/J data use the complete original standard RIGHT left class. -/
theorem fibrantFactorizationData_standard_classes (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    standardHornGenerators.{u, v}.rlp.llp
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f) ∧
      ∀ n : I, fibrations PointedCGWH.{u, v}
        ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f).hom.natTrans.app
          n) := by
  let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
  exact ⟨Eq.mp (congrArg (fun P : MorphismProperty PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
    =>
    P (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f))
      standard_trivialCofibrations_eq)
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hi f),
    (fibrations_iff _).mp (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hp f)⟩

/-- The entire actual I factorization retains the same original right-module level map. -/
theorem cofibrantFactorizationData_level_fac
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) (n : I) :
    (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f).hom.natTrans.app n ≫
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f).hom.natTrans.app n
        =
        f.hom.hom.natTrans.app n := by
  have h := congrArg (fun g => (evaluation n).map g) (cofibrantFactorizationData_fac f)
  rw [(evaluation n).map_comp] at h
  exact h

/-- The entire actual J factorization retains the same original right-module level map. -/
theorem fibrantFactorizationData_level_fac
    (f : CategoryTheory.Arrow PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) (n : I) :
    (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f).hom.natTrans.app n ≫
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f).hom.natTrans.app n
        =
        f.hom.hom.natTrans.app n := by
  have h := congrArg (fun g => (evaluation n).map g) (fibrantFactorizationData_fac f)
  rw [(evaluation n).map_comp] at h
  exact h

end PointedCGWH.Spectra.Symmetric.RightPresentationModel
