/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.RightModules
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.LeftPresentationModel.Migration

/-!
# Original left/right module class and cardinal migration

The computed commutative sphere converts actual left modules to actual right
modules. Its full unit compares their entire native carrier functors.
Consequently all five model classes stay on the literal original conversion
maps; full original right free families and κ data remain correlated.
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

private abbrev presentation :=
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}

private abbrev leftPresentation :=
  PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

/-- The whole actual left-to-right conversion commutes with the complete native carrier. -/
def leftCarrierComparison :
    PointedCGWH.SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
      presentation.functor ≅ leftPresentation.functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      PointedCGWH.SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.unitIso.symm
      leftPresentation.functor ≪≫ Functor.leftUnitor _

private theorem nativePropertyComparison_iff
    (P : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v}
      PointedCGWH.SymmetricOperatorIndex.{u, v})) [P.RespectsIso]
    {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) :
    P (leftPresentation.functor.map f) ↔
      P (presentation.functor.map
        (PointedCGWH.SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor.map
          f)) :=
  (P.arrow_mk_iso_iff (CategoryTheory.Arrow.isoOfNatIso leftCarrierComparison
    (CategoryTheory.Arrow.mk f))).symm

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The literal original left-to-right conversion preserves the complete weakEquivalences class. -/
theorem left_weakEquivalences_iff
    {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} f ↔
      weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
        (PointedCGWH.SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor.map
          f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      PointedCGWH.SymmetricOperatorIndex.{u, v}) := EnrichedProjective.Native.modelCategory
  let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
  let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
  exact nativePropertyComparison_iff (weakEquivalences _) f

/-- The literal original left-to-right conversion preserves the complete cofibrations class. -/
theorem left_cofibrations_iff
    {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    cofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} f ↔
      cofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
        (PointedCGWH.SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor.map
          f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      PointedCGWH.SymmetricOperatorIndex.{u, v}) := EnrichedProjective.Native.modelCategory
  let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
  let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
  exact nativePropertyComparison_iff (cofibrations _) f

/-- The literal original left-to-right conversion preserves the complete fibrations class. -/
theorem left_fibrations_iff
    {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    fibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} f ↔
      fibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
        (PointedCGWH.SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor.map
          f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      PointedCGWH.SymmetricOperatorIndex.{u, v}) := EnrichedProjective.Native.modelCategory
  let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
  let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
  exact nativePropertyComparison_iff (fibrations _) f

/-- The literal original left-to-right conversion preserves the complete trivialFibrations class. -/
theorem left_trivialFibrations_iff
    {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    trivialFibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} f ↔
      trivialFibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
        (PointedCGWH.SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor.map
          f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      PointedCGWH.SymmetricOperatorIndex.{u, v}) := EnrichedProjective.Native.modelCategory
  let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
  let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
  exact nativePropertyComparison_iff (trivialFibrations _) f

/-- The literal original conversion preserves the complete trivial-cofibration class. -/
theorem left_trivialCofibrations_iff
    {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    trivialCofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} f ↔
      trivialCofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
        (PointedCGWH.SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor.map
          f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      PointedCGWH.SymmetricOperatorIndex.{u, v}) := EnrichedProjective.Native.modelCategory
  let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
  let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
  exact nativePropertyComparison_iff (trivialCofibrations _) f

/-- The actual right κ/I left class and every original right component are preserved. -/
theorem cofibrantFactorizationData_original_classes (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    boundaryGenerators.{u, v}.rlp.llp
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f) ∧
      ∀ n : Operad.SmallFinBijGroupoid, trivialFibrations PointedCGWH.{u, v}
        ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f).hom.natTrans.app
          n) := by
  let _ : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
  exact ⟨Eq.mp (congrArg (fun P : MorphismProperty PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
    =>
    P (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f)) cofibrations_eq)
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hi f),
    (trivialFibrations_iff _).mp (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hp f)⟩

/-- The actual right κ/J left class and every original right component are preserved. -/
theorem fibrantFactorizationData_original_classes (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    hornGenerators.{u, v}.rlp.llp (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f) ∧
      ∀ n : Operad.SmallFinBijGroupoid, fibrations PointedCGWH.{u, v}
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
      trivialCofibrations_eq)
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hi f),
    (fibrations_iff _).mp (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hp f)⟩

/-- Every original right-module square retains the actual whole κ/I middle map. -/
theorem cofibrantFactorizationData_Z_map {f g : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (φ : f ⟶ g) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ =
      presentation.inverse.map
        ((EnrichedProjective.Native.cofibrantFactorizationData
          (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).Z.map
            (presentation.functor.mapArrow.map φ)) := rfl

/-- Every original right-module square retains the actual whole κ/J middle map. -/
theorem fibrantFactorizationData_Z_map {f g : CategoryTheory.Arrow
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (φ : f ⟶ g) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ =
      presentation.inverse.map
        ((EnrichedProjective.Native.fibrantFactorizationData
          (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).Z.map
            (presentation.functor.mapArrow.map φ)) := rfl

end PointedCGWH.Spectra.Symmetric.RightPresentationModel
