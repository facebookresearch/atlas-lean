/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.MorphismProperty.Factorization.GivenDataEquality
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.LeftRightFactorization

/-!
# Entire original left and right chosen factorization records

The actual original inverse sphere conversion carries the left class pairs to the right
class pairs. Reclassification keeps the same given left middle functor and both whole
natural transformations. The complete resulting records equal the original right choices.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open CategoryTheory.MorphismProperty.FunctorialFactorizationData
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

namespace PointedCGWH.Spectra.Symmetric.LeftRightNativeModel

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

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

/-- The whole original left cofibration class maps to the original right class. -/
theorem actualLeftCofibrationClassToRight :
    (cofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).inverseImage
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ≤
      cofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} := by
  intro X Y f hf
  exact (toLeft_cofibrations_iff f).mp hf

/-- The whole original left trivial-fibration class maps to the original right class. -/
theorem actualLeftTrivialFibrationClassToRight :
    (trivialFibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).inverseImage
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ≤
      trivialFibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} := by
  intro X Y f hf
  exact (toLeft_trivialFibrations_iff f).mp hf

/-- The original left trivial-cofibration class maps to the entire original right class. -/
theorem actualLeftTrivialCofibrationClassToRight :
    (trivialCofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).inverseImage
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ≤
      trivialCofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} := by
  intro X Y f hf
  exact (toLeft_trivialCofibrations_iff f).mp hf

/-- The original left fibration class maps to the entire original right class. -/
theorem actualLeftFibrationClassToRight :
    (fibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).inverseImage
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ≤
      fibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} := by
  intro X Y f hf
  exact (toLeft_fibrations_iff f).mp hf

/-- The whole I record uses the actual original left data and inverse conversion. -/
def actualLeftCofibrantDataToRight :
    FunctorialFactorizationData (cofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
      (trivialFibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
  (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).ofEquivalence
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).ofLE
      actualLeftCofibrationClassToRight actualLeftTrivialFibrationClassToRight

/-- The whole J record uses the same original left data and inverse conversion. -/
def actualLeftFibrantDataToRight :
    FunctorialFactorizationData (trivialCofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u,
      v})
      (fibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
  (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).ofEquivalence
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm).ofLE
      actualLeftTrivialCofibrationClassToRight actualLeftFibrationClassToRight

/-- The entire original right I record is the given original left route, with the same choices. -/
theorem rightCofibrantData_eq_actualLeftFullRecord :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) =
      actualLeftCofibrantDataToRight.{u, v} := by
  apply eq_of_middle_and_heq_natural_maps
  · exact rightCofibrantData_actualLeft_Z
  · apply heq_of_eq
    apply NatTrans.ext
    funext f
    exact rightCofibrantData_actualLeft_i f
  · apply heq_of_eq
    apply NatTrans.ext
    funext f
    exact rightCofibrantData_actualLeft_p f

/-- The entire original right J record is the same given original left route. -/
theorem rightFibrantData_eq_actualLeftFullRecord :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) =
      actualLeftFibrantDataToRight.{u, v} := by
  apply eq_of_middle_and_heq_natural_maps
  · exact rightFibrantData_actualLeft_Z
  · apply heq_of_eq
    apply NatTrans.ext
    funext f
    exact rightFibrantData_actualLeft_i f
  · apply heq_of_eq
    apply NatTrans.ext
    funext f
    exact rightFibrantData_actualLeft_p f

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel
