/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.LeftRightConversion
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedAdjunction

/-!
# Complete canonical derived data for the original sphere-module conversion

Use the two actual conversion adjunctions and the two fixed native projective model structures.
The canonical total derived functors retain their comparison transformations and all four derived
functor conditions. Both original adjunctions keep their existing units, counits and full Hom maps.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
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

/-- The complete canonical derived data of the actual original forward conversion adjunction. -/
def toRightDerivedAdjunctionData :
    QuillenDerivedAdjunctionData
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.toAdjunction := by
  let _ : Adjunction.IsQuillenAdjunction
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.toAdjunction :=
    toRight_isQuillenAdjunction
  exact quillenDerivedAdjunctionData
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.toAdjunction

/-- All canonical derived fields of the genuine original inverse conversion adjunction. -/
def toLeftDerivedAdjunctionData :
    QuillenDerivedAdjunctionData
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm.toAdjunction := by
  let _ : Adjunction.IsQuillenAdjunction
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm.toAdjunction :=
    toLeft_isQuillenAdjunction
  exact quillenDerivedAdjunctionData
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm.toAdjunction

private theorem toRight_hasLeftDerived :
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
      (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}).Q).HasLeftDerivedFunctor
        (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) := by
  let _ := toRightDerivedAdjunctionData.{u, v}.leftIsDerived
  exact Functor.HasLeftDerivedFunctor.mk'
    (LF := toRightDerivedAdjunctionData.{u, v}.leftDerived)
    (α := toRightDerivedAdjunctionData.{u, v}.leftComparison)

private theorem toRight_hasRightDerived :
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ⋙
      (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).Q).HasRightDerivedFunctor
        (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) := by
  let _ := toRightDerivedAdjunctionData.{u, v}.rightIsDerived
  exact Functor.HasRightDerivedFunctor.mk'
    (RF := toRightDerivedAdjunctionData.{u, v}.rightDerived)
    (α := toRightDerivedAdjunctionData.{u, v}.rightComparison)

private theorem toLeft_hasLeftDerived :
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ⋙
      (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).Q).HasLeftDerivedFunctor
        (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) := by
  let _ := toLeftDerivedAdjunctionData.{u, v}.leftIsDerived
  exact Functor.HasLeftDerivedFunctor.mk'
    (LF := toLeftDerivedAdjunctionData.{u, v}.leftDerived)
    (α := toLeftDerivedAdjunctionData.{u, v}.leftComparison)

private theorem toLeft_hasRightDerived :
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
      (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}).Q).HasRightDerivedFunctor
        (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) := by
  let _ := toLeftDerivedAdjunctionData.{u, v}.rightIsDerived
  exact Functor.HasRightDerivedFunctor.mk'
    (RF := toLeftDerivedAdjunctionData.{u, v}.rightDerived)
    (α := toLeftDerivedAdjunctionData.{u, v}.rightComparison)

attribute [local instance] toRight_hasLeftDerived toRight_hasRightDerived
  toLeft_hasLeftDerived toLeft_hasRightDerived

/-- The actual forward total left derived functor uses the original localization choices. -/
theorem toRightDerived_left_value : toRightDerivedAdjunctionData.{u, v}.leftDerived =
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
      (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}).Q).totalLeftDerived
        (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).Q
        (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) := rfl

/-- The original forward total right derived functor keeps the actual inverse and localization. -/
theorem toRightDerived_right_value : toRightDerivedAdjunctionData.{u, v}.rightDerived =
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ⋙
      (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).Q).totalRightDerived
        (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}).Q
        (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) := rfl

/-- The forward left comparison retains the complete chosen original derived counit. -/
theorem toRightDerived_left_comparison : toRightDerivedAdjunctionData.{u, v}.leftComparison =
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
      (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}).Q).totalLeftDerivedCounit
        (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).Q
        (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) := rfl

/-- The forward right comparison retains the whole chosen original derived unit. -/
theorem toRightDerived_right_comparison : toRightDerivedAdjunctionData.{u, v}.rightComparison =
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ⋙
      (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).Q).totalRightDerivedUnit
        (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}).Q
        (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) := rfl

/-- The inverse left derived value uses the same original inverse and localization functors. -/
theorem toLeftDerived_left_value : toLeftDerivedAdjunctionData.{u, v}.leftDerived =
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ⋙
      (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).Q).totalLeftDerived
        (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}).Q
        (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) := rfl

/-- The inverse right derived value keeps the full original forward conversion and localization. -/
theorem toLeftDerived_right_value : toLeftDerivedAdjunctionData.{u, v}.rightDerived =
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
      (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}).Q).totalRightDerived
        (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).Q
        (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) := rfl

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel

/-!
The native consumers below use the canonical spectrum carrier and its
level model, with the complete original conversion conjugated by the
proved source/operator equivalences.
-/

namespace PointedCGWH.Spectra.Symmetric.LeftRightNativeModel.Canonical

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction


attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel

/-- The complete canonical derived data of the actual original forward conversion adjunction. -/
def toRightDerivedAdjunctionData :
    QuillenDerivedAdjunctionData
      carrierEquivalence.{u, v}.toAdjunction := by
  let _ : Adjunction.IsQuillenAdjunction
      carrierEquivalence.{u, v}.toAdjunction :=
    toRight_isQuillenAdjunction
  exact quillenDerivedAdjunctionData
    carrierEquivalence.{u, v}.toAdjunction

/-- All canonical derived fields of the genuine original inverse conversion adjunction. -/
def toLeftDerivedAdjunctionData :
    QuillenDerivedAdjunctionData
      carrierEquivalence.{u, v}.symm.toAdjunction := by
  let _ : Adjunction.IsQuillenAdjunction
      carrierEquivalence.{u, v}.symm.toAdjunction :=
    toLeft_isQuillenAdjunction
  exact quillenDerivedAdjunctionData
    carrierEquivalence.{u, v}.symm.toAdjunction

private theorem toRight_hasLeftDerived :
    (carrierEquivalence.{u, v}.functor ⋙
      (weakEquivalences Spectrum.{u, v}).Q).HasLeftDerivedFunctor
        (weakEquivalences Spectrum.{u, v}) := by
  let _ := toRightDerivedAdjunctionData.{u, v}.leftIsDerived
  exact Functor.HasLeftDerivedFunctor.mk'
    (LF := toRightDerivedAdjunctionData.{u, v}.leftDerived)
    (α := toRightDerivedAdjunctionData.{u, v}.leftComparison)

private theorem toRight_hasRightDerived :
    (carrierEquivalence.{u, v}.inverse ⋙
      (weakEquivalences Spectrum.{u, v}).Q).HasRightDerivedFunctor
        (weakEquivalences Spectrum.{u, v}) := by
  let _ := toRightDerivedAdjunctionData.{u, v}.rightIsDerived
  exact Functor.HasRightDerivedFunctor.mk'
    (RF := toRightDerivedAdjunctionData.{u, v}.rightDerived)
    (α := toRightDerivedAdjunctionData.{u, v}.rightComparison)

private theorem toLeft_hasLeftDerived :
    (carrierEquivalence.{u, v}.inverse ⋙
      (weakEquivalences Spectrum.{u, v}).Q).HasLeftDerivedFunctor
        (weakEquivalences Spectrum.{u, v}) := by
  let _ := toLeftDerivedAdjunctionData.{u, v}.leftIsDerived
  exact Functor.HasLeftDerivedFunctor.mk'
    (LF := toLeftDerivedAdjunctionData.{u, v}.leftDerived)
    (α := toLeftDerivedAdjunctionData.{u, v}.leftComparison)

private theorem toLeft_hasRightDerived :
    (carrierEquivalence.{u, v}.functor ⋙
      (weakEquivalences Spectrum.{u, v}).Q).HasRightDerivedFunctor
        (weakEquivalences Spectrum.{u, v}) := by
  let _ := toLeftDerivedAdjunctionData.{u, v}.rightIsDerived
  exact Functor.HasRightDerivedFunctor.mk'
    (RF := toLeftDerivedAdjunctionData.{u, v}.rightDerived)
    (α := toLeftDerivedAdjunctionData.{u, v}.rightComparison)

attribute [local instance] toRight_hasLeftDerived toRight_hasRightDerived
  toLeft_hasLeftDerived toLeft_hasRightDerived

/-- The actual forward total left derived functor uses the original localization choices. -/
theorem toRightDerived_left_value : toRightDerivedAdjunctionData.{u, v}.leftDerived =
    (carrierEquivalence.{u, v}.functor ⋙
      (weakEquivalences Spectrum.{u, v}).Q).totalLeftDerived
        (weakEquivalences Spectrum.{u, v}).Q
        (weakEquivalences Spectrum.{u, v}) := rfl

/-- The original forward total right derived functor keeps the actual inverse and localization. -/
theorem toRightDerived_right_value : toRightDerivedAdjunctionData.{u, v}.rightDerived =
    (carrierEquivalence.{u, v}.inverse ⋙
      (weakEquivalences Spectrum.{u, v}).Q).totalRightDerived
        (weakEquivalences Spectrum.{u, v}).Q
        (weakEquivalences Spectrum.{u, v}) := rfl

/-- The forward left comparison retains the complete chosen original derived counit. -/
theorem toRightDerived_left_comparison : toRightDerivedAdjunctionData.{u, v}.leftComparison =
    (carrierEquivalence.{u, v}.functor ⋙
      (weakEquivalences Spectrum.{u, v}).Q).totalLeftDerivedCounit
        (weakEquivalences Spectrum.{u, v}).Q
        (weakEquivalences Spectrum.{u, v}) := rfl

/-- The forward right comparison retains the whole chosen original derived unit. -/
theorem toRightDerived_right_comparison : toRightDerivedAdjunctionData.{u, v}.rightComparison =
    (carrierEquivalence.{u, v}.inverse ⋙
      (weakEquivalences Spectrum.{u, v}).Q).totalRightDerivedUnit
        (weakEquivalences Spectrum.{u, v}).Q
        (weakEquivalences Spectrum.{u, v}) := rfl

/-- The inverse left derived value uses the same original inverse and localization functors. -/
theorem toLeftDerived_left_value : toLeftDerivedAdjunctionData.{u, v}.leftDerived =
    (carrierEquivalence.{u, v}.inverse ⋙
      (weakEquivalences Spectrum.{u, v}).Q).totalLeftDerived
        (weakEquivalences Spectrum.{u, v}).Q
        (weakEquivalences Spectrum.{u, v}) := rfl

/-- The inverse right derived value keeps the full original forward conversion and localization. -/
theorem toLeftDerived_right_value : toLeftDerivedAdjunctionData.{u, v}.rightDerived =
    (carrierEquivalence.{u, v}.functor ⋙
      (weakEquivalences Spectrum.{u, v}).Q).totalRightDerived
        (weakEquivalences Spectrum.{u, v}).Q
        (weakEquivalences Spectrum.{u, v}) := rfl

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel.Canonical
