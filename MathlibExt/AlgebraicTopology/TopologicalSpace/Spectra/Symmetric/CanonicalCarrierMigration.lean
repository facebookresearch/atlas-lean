/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.CanonicalProjectiveModels
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.RightModules

/-!
# Original right-module model data and canonical projective data

The existing rightModuleToOperator, operatorToRightModule and
rightModuleOperatorEquivalence supply the complete carrier conversions. This
file compares the original model classes and full cardinal factorization data
with the canonical level model through those established declarations.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open CategoryTheory.MonoidalOpposite
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory MonoidalClosed ExternalProduct

namespace PointedCGWH.Spectra.Symmetric.CanonicalCarrierMigration

open PointedCGWH.SymmetricRightModulePresentation

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- All five original source classes are preserved by the same actual forward functor. -/
theorem five_model_classes {M N : RightSphereModule.{u, v}} (f : M ⟶ N) :
    letI : ModelCategory RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    letI : ModelCategory Spectrum.{u, v} := PointedCGWH.Spectra.Symmetric.levelModel
    (weakEquivalences RightSphereModule f ↔
      weakEquivalences Spectrum (rightModuleToOperator.map f)) ∧
      (fibrations RightSphereModule f ↔ fibrations Spectrum (rightModuleToOperator.map f)) ∧
      (cofibrations RightSphereModule f ↔ cofibrations Spectrum (rightModuleToOperator.map f)) ∧
      (trivialFibrations RightSphereModule f ↔
        trivialFibrations Spectrum (rightModuleToOperator.map f)) ∧
      (trivialCofibrations RightSphereModule f ↔
        trivialCofibrations Spectrum (rightModuleToOperator.map f)) := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- The full original source I data use the same canonical factor and actual inverse functor. -/
theorem source_I_fields :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z =
        rightModuleToOperator.mapArrow ⋙
          PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.Z ⋙ operatorToRightModule ∧
      (∀ f, HEq (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f)
        (rightModuleOperatorEquivalence.unitIso.hom.app f.left ≫ operatorToRightModule.map
          (PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.i.app
            (rightModuleToOperator.mapArrow.obj f)))) ∧
      (∀ f, HEq (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f)
        (operatorToRightModule.map (PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.p.app
          (rightModuleToOperator.mapArrow.obj f)) ≫
            rightModuleOperatorEquivalence.unitIso.inv.app f.right)) := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact ⟨rfl, (fun _ => HEq.rfl), (fun _ => HEq.rfl)⟩

/-- The full original source J data use the same canonical factor and actual inverse functor. -/
theorem source_J_fields :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z =
        rightModuleToOperator.mapArrow ⋙ PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.Z ⋙
          operatorToRightModule ∧
      (∀ f, HEq (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app f)
        (rightModuleOperatorEquivalence.unitIso.hom.app f.left ≫ operatorToRightModule.map
          (PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.i.app
            (rightModuleToOperator.mapArrow.obj f)))) ∧
      (∀ f, HEq (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app f)
        (operatorToRightModule.map (PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.p.app
          (rightModuleToOperator.mapArrow.obj f)) ≫
            rightModuleOperatorEquivalence.unitIso.inv.app f.right)) := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact ⟨rfl, (fun _ => HEq.rfl), (fun _ => HEq.rfl)⟩

/-- Every original source Arrow square retains both complete canonical middle maps. -/
theorem source_factor_Z_map {f g : Arrow RightSphereModule.{u, v}} (φ : f ⟶ g) :
    HEq (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ)
        (operatorToRightModule.map (PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.Z.map
          (rightModuleToOperator.mapArrow.map φ))) ∧
      HEq (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map φ)
        (operatorToRightModule.map (PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.Z.map
          (rightModuleToOperator.mapArrow.map φ))) := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact ⟨HEq.rfl, HEq.rfl⟩

end PointedCGWH.Spectra.Symmetric.CanonicalCarrierMigration

namespace PointedCGWH.Spectra.Symmetric.CanonicalCarrierMigration

open PointedCGWH.SymmetricRightModulePresentation

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction PointedCGWH.Spectra.Symmetric.levelModel

/-- The raw-right weak class is a derived presentation of the canonical class. -/
def sourceWeakEquivalences : MorphismProperty RightSphereModule.{u, v} :=
  (weakEquivalences Spectrum.{u, v}).inverseImage rightModuleToOperator

/-- The original right I data are computed from the canonical data and its
actual full source inverse, without another source model constructor. -/
def sourceCofibrantFactorizationData :
    FunctorialFactorizationData
      ((cofibrations Spectrum.{u, v}).inverseImage rightModuleToOperator)
      ((trivialFibrations Spectrum.{u, v}).inverseImage rightModuleToOperator) :=
  PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.ofEquivalence
    rightModuleOperatorEquivalence

/-- The original right J data retain their same canonical algorithm and
the same actual source inverse and unit. -/
def sourceFibrantFactorizationData :
    FunctorialFactorizationData
      ((trivialCofibrations Spectrum.{u, v}).inverseImage rightModuleToOperator)
      ((fibrations Spectrum.{u, v}).inverseImage rightModuleToOperator) :=
  PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.ofEquivalence
    rightModuleOperatorEquivalence

/-- The entire derived original I middle functor is the specified source reconstruction. -/
theorem sourceCofibrantFactorizationData_Z : sourceCofibrantFactorizationData.{u, v}.Z =
    rightModuleToOperator.mapArrow ⋙ PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.Z ⋙
      operatorToRightModule := rfl

/-- The entire derived original J middle functor is the same specified reconstruction. -/
theorem sourceFibrantFactorizationData_Z : sourceFibrantFactorizationData.{u, v}.Z =
    rightModuleToOperator.mapArrow ⋙ PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.Z ⋙
      operatorToRightModule := rfl

/-- Every original I source square keeps the same complete canonical middle map. -/
theorem sourceCofibrantFactorizationData_Z_map
    {f g : Arrow RightSphereModule.{u, v}} (φ : f ⟶ g) :
    sourceCofibrantFactorizationData.Z.map φ = operatorToRightModule.map
      (PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.Z.map
        (rightModuleToOperator.mapArrow.map φ)) := rfl

/-- Every original J source square keeps the same complete canonical middle map. -/
theorem sourceFibrantFactorizationData_Z_map
    {f g : Arrow RightSphereModule.{u, v}} (φ : f ⟶ g) :
    sourceFibrantFactorizationData.Z.map φ = operatorToRightModule.map
      (PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.Z.map
        (rightModuleToOperator.mapArrow.map φ)) := rfl

/-- All original I source components use the actual given unit and inverse. -/
theorem sourceCofibrantFactorizationData_fields :
    (∀ f : Arrow RightSphereModule.{u, v}, sourceCofibrantFactorizationData.i.app f =
      rightModuleOperatorEquivalence.unitIso.hom.app f.left ≫ operatorToRightModule.map
        (PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.i.app
          (rightModuleToOperator.mapArrow.obj f))) ∧
    (∀ f : Arrow RightSphereModule.{u, v}, sourceCofibrantFactorizationData.p.app f =
      operatorToRightModule.map (PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.p.app
        (rightModuleToOperator.mapArrow.obj f)) ≫ rightModuleOperatorEquivalence.unitIso.inv.app
          f.right) := ⟨fun _ => rfl, fun _ => rfl⟩

/-- All original J source components retain that same given unit and inverse. -/
theorem sourceFibrantFactorizationData_fields :
    (∀ f : Arrow RightSphereModule.{u, v}, sourceFibrantFactorizationData.i.app f =
      rightModuleOperatorEquivalence.unitIso.hom.app f.left ≫ operatorToRightModule.map
        (PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.i.app
          (rightModuleToOperator.mapArrow.obj f))) ∧
    (∀ f : Arrow RightSphereModule.{u, v}, sourceFibrantFactorizationData.p.app f =
      operatorToRightModule.map (PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.p.app
        (rightModuleToOperator.mapArrow.obj f)) ≫ rightModuleOperatorEquivalence.unitIso.inv.app
          f.right) := ⟨fun _ => rfl, fun _ => rfl⟩

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The full derived I record is the given original right record at every caller bottom. -/
theorem sourceCofibrantFactorizationData_heq_existing :
    HEq sourceCofibrantFactorizationData.{u, v}
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The full derived J record is the given original right record at every caller bottom. -/
theorem sourceFibrantFactorizationData_heq_existing :
    HEq sourceFibrantFactorizationData.{u, v}
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The raw-right source weak class is the full original one under its actual bottom. -/
theorem sourceWeakEquivalences_eq_existing : sourceWeakEquivalences.{u, v} =
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u,
      v}).categoryWithWeakEquivalences.weakEquivalences := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

end PointedCGWH.Spectra.Symmetric.CanonicalCarrierMigration
