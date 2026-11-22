/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedCarrierComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.LeftRightDerivedEquivalence
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.LeftRightFactorization
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.OriginalRightLevelHo

/-!
# The original sphere carriers, their actual Ho maps and canonical derived data

Identify the literal original LEFT localization and the existing whole RIGHT
localization with the two actual models before constructing any comparison.
The strict sphere conversion lifts retain their original unit and counit.
Both canonical derived equivalences compare with those whole original lifts.
The native operator comparison uses the proved original carrier composition.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
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
  Native.modelCategory toRight_isQuillenAdjunction toLeft_isQuillenAdjunction

/-- The literal original LEFT localization of the complete given module/operator carrier. -/
abbrev originalLeftHo := NativePresentation.LevelHo.HoCategory
  SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

/-- The strict original LEFT projection keeps the actual source weak-class construction. -/
abbrev originalLeftProjection := NativePresentation.LevelHo.projection
  SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

theorem originalLeftHo_eq_model :
    originalLeftHo.{u, v} = HomotopyCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} := rfl

theorem originalLeftProjection_eq_model : originalLeftProjection.{u, v} =
    toHomotopyCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} := rfl

theorem originalRightHo_eq_model : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) =
    HomotopyCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} := rfl

theorem originalRightProjection_eq_model : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) =
    toHomotopyCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} := rfl

/-- The whole original sphere conversion on the two already identified original Ho categories. -/
def originalSphereHoEquivalence : originalLeftHo.{u, v} ≌
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) :=
  Localization.originalEquivalence
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toLeft_allWeakMaps)

/-- The whole original inverse conversion uses its own given inverse unit and counit. -/
def originalInverseSphereHoEquivalence : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ≌
    originalLeftHo.{u, v} :=
  Localization.originalEquivalence
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm
    (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toRight_allWeakMaps)

theorem originalSphereHo_forward_projection :
    originalLeftProjection.{u, v} ⋙ originalSphereHoEquivalence.{u, v}.functor =
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
        (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) :=
  Localization.originalForward_projection
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps)

theorem originalSphereHo_inverse_projection :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
        originalSphereHoEquivalence.{u, v}.inverse =
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ⋙
        originalLeftProjection.{u, v} :=
  Localization.originalInverse_projection
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (QuillenCarrierLocalization.inverseInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toLeft_allWeakMaps)

theorem originalSphereHo_forward_map {X Y : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : X ⟶ Y) :
    originalSphereHoEquivalence.functor.map (originalLeftProjection.map f) =
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).map
        (SymmetricRightModulePresentation.sphereModuleEquivalence.functor.map f) :=
  Localization.originalForward_map_projected
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps) f

theorem originalSphereHo_inverse_map {X Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f :
  X ⟶ Y) :
    originalSphereHoEquivalence.inverse.map
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).map f) =
      originalLeftProjection.map
        (SymmetricRightModulePresentation.sphereModuleEquivalence.inverse.map f) :=
  Localization.originalInverse_map_projected
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (QuillenCarrierLocalization.inverseInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toLeft_allWeakMaps) f

theorem originalSphereHo_unit_hom (X : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    originalSphereHoEquivalence.unitIso.hom.app (originalLeftProjection.obj X) =
      originalLeftProjection.map
        (SymmetricRightModulePresentation.sphereModuleEquivalence.unitIso.hom.app X) :=
  Localization.originalUnitIso_hom_projected
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toLeft_allWeakMaps) X

theorem originalSphereHo_unit_inv (X : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    originalSphereHoEquivalence.unitIso.inv.app (originalLeftProjection.obj X) =
      originalLeftProjection.map
        (SymmetricRightModulePresentation.sphereModuleEquivalence.unitIso.inv.app X) :=
  Localization.originalUnitIso_inv_projected
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toLeft_allWeakMaps) X

theorem originalSphereHo_counit_hom (Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    originalSphereHoEquivalence.counitIso.hom.app
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).obj Y) =
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).map
        (SymmetricRightModulePresentation.sphereModuleEquivalence.counitIso.hom.app Y) :=
  Localization.originalCounitIso_hom_projected
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toLeft_allWeakMaps) Y

theorem originalSphereHo_counit_inv (Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    originalSphereHoEquivalence.counitIso.inv.app
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).obj Y) =
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).map
        (SymmetricRightModulePresentation.sphereModuleEquivalence.counitIso.inv.app Y) :=
  Localization.originalCounitIso_inv_projected
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toLeft_allWeakMaps) Y

theorem originalInverseSphereHo_unitIso : originalInverseSphereHoEquivalence.{u, v}.unitIso =
    originalSphereHoEquivalence.{u, v}.counitIso.symm :=
  Localization.originalEquivalence_unitIso_symm
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toLeft_allWeakMaps)

theorem originalInverseSphereHo_counitIso : originalInverseSphereHoEquivalence.{u, v}.counitIso =
    originalSphereHoEquivalence.{u, v}.unitIso.symm :=
  Localization.originalEquivalence_counitIso_symm
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toLeft_allWeakMaps)

/-- The entire original forward total left derived functor compares with its strict carrier lift. -/
def toRightCarrierLeftComparison : toRightDerivedAdjunctionData.{u, v}.leftDerived ≅
    originalSphereHoEquivalence.{u, v}.functor :=
  QuillenCarrierLocalization.leftDerivedComparison
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps

/-- The original forward total right derived functor keeps its actual inverse carrier comparison. -/
def toRightCarrierRightComparison : originalSphereHoEquivalence.{u, v}.inverse ≅
    toRightDerivedAdjunctionData.{u, v}.rightDerived :=
  QuillenCarrierLocalization.rightDerivedComparison
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toLeft_allWeakMaps

/-- The actual inverse total left derived functor compares with the whole inverse carrier lift. -/
def toLeftCarrierLeftComparison : toLeftDerivedAdjunctionData.{u, v}.leftDerived ≅
    originalInverseSphereHoEquivalence.{u, v}.functor :=
  QuillenCarrierLocalization.leftDerivedComparison
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps

/-- The inverse total right derived functor retains the actual original forward carrier lift. -/
def toLeftCarrierRightComparison : originalInverseSphereHoEquivalence.{u, v}.inverse ≅
    toLeftDerivedAdjunctionData.{u, v}.rightDerived :=
  QuillenCarrierLocalization.rightDerivedComparison
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toRight_allWeakMaps

theorem toRightCarrierLeftComparison_hom (X : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    toRightCarrierLeftComparison.hom.app (originalLeftProjection.obj X) =
      toRightDerivedAdjunctionData.leftComparison.app X :=
  QuillenCarrierLocalization.leftDerivedComparisonHomProjected
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps X

theorem toRightCarrierRightComparison_hom (Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    toRightCarrierRightComparison.hom.app ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).obj Y) =
      toRightDerivedAdjunctionData.rightComparison.app Y :=
  QuillenCarrierLocalization.rightDerivedComparisonHomProjected
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toLeft_allWeakMaps Y

theorem toLeftCarrierLeftComparison_hom (Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    toLeftCarrierLeftComparison.hom.app ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).obj Y) =
      toLeftDerivedAdjunctionData.leftComparison.app Y :=
  QuillenCarrierLocalization.leftDerivedComparisonHomProjected
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps Y

theorem toLeftCarrierRightComparison_hom (X : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    toLeftCarrierRightComparison.hom.app (originalLeftProjection.obj X) =
      toLeftDerivedAdjunctionData.rightComparison.app X :=
  QuillenCarrierLocalization.rightDerivedComparisonHomProjected
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toRight_allWeakMaps X

theorem toRightCarrier_unit : toRightDerivedAdjunctionData.{u, v}.adjunction.unit ≫
    Functor.whiskerRight toRightCarrierLeftComparison.hom
      toRightDerivedAdjunctionData.rightDerived =
    originalSphereHoEquivalence.unitIso.hom ≫
      Functor.whiskerLeft originalSphereHoEquivalence.functor toRightCarrierRightComparison.hom :=
  QuillenCarrierLocalization.unitComparison
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
        toLeft_allWeakMaps

theorem toRightCarrier_counit : Functor.whiskerRight toRightCarrierRightComparison.hom
      toRightDerivedAdjunctionData.{u, v}.leftDerived ≫
        toRightDerivedAdjunctionData.adjunction.counit =
    Functor.whiskerLeft originalSphereHoEquivalence.inverse toRightCarrierLeftComparison.hom ≫
      originalSphereHoEquivalence.counitIso.hom :=
  QuillenCarrierLocalization.counitComparison
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v} toRight_allWeakMaps
        toLeft_allWeakMaps

theorem toLeftCarrier_unit : toLeftDerivedAdjunctionData.{u, v}.adjunction.unit ≫
    Functor.whiskerRight toLeftCarrierLeftComparison.hom toLeftDerivedAdjunctionData.rightDerived =
    originalInverseSphereHoEquivalence.unitIso.hom ≫
      Functor.whiskerLeft originalInverseSphereHoEquivalence.functor
        toLeftCarrierRightComparison.hom :=
  QuillenCarrierLocalization.unitComparison
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
        toRight_allWeakMaps

theorem toLeftCarrier_counit : Functor.whiskerRight toLeftCarrierRightComparison.hom
      toLeftDerivedAdjunctionData.{u, v}.leftDerived ≫
        toLeftDerivedAdjunctionData.adjunction.counit =
    Functor.whiskerLeft originalInverseSphereHoEquivalence.inverse toLeftCarrierLeftComparison.hom ≫
      originalInverseSphereHoEquivalence.counitIso.hom :=
  QuillenCarrierLocalization.counitComparison
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm toLeft_allWeakMaps
        toRight_allWeakMaps

/-- The original inverse sphere lift followed by the literal LEFT operator lift is the given RIGHT
operator lift on every Ho object and morphism. -/
theorem originalSphereHo_inverse_toNative :
    originalSphereHoEquivalence.{u, v}.inverse ⋙ NativePresentation.LevelHo.forward
        SymmetricModulePresentation.moduleOperatorEquivalence.{u, v} =
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor := by
  apply Localization.Construction.uniq
  calc
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
        (originalSphereHoEquivalence.inverse ⋙ NativePresentation.LevelHo.forward
          SymmetricModulePresentation.moduleOperatorEquivalence) =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
        originalSphereHoEquivalence.inverse) ⋙
        NativePresentation.LevelHo.forward SymmetricModulePresentation.moduleOperatorEquivalence :=
      rfl
    _ = (SymmetricRightModulePresentation.sphereModuleEquivalence.inverse ⋙
        originalLeftProjection) ⋙ NativePresentation.LevelHo.forward
          SymmetricModulePresentation.moduleOperatorEquivalence := by
      rw [originalSphereHo_inverse_projection]
    _ = SymmetricRightModulePresentation.sphereModuleEquivalence.inverse ⋙
        (originalLeftProjection ⋙ NativePresentation.LevelHo.forward
          SymmetricModulePresentation.moduleOperatorEquivalence) := rfl
    _ = SymmetricRightModulePresentation.sphereModuleEquivalence.inverse ⋙
        (SymmetricModulePresentation.moduleOperatorEquivalence.functor ⋙ toHomotopyCategory
          PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}) := by
      rw [NativePresentation.LevelHo.forward_projection]
    _ = SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor ⋙
        toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v} := rfl
    _ = (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
        (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor :=
      (RightPresentationModel.LevelHomotopy.toNativeHo_projection).symm

theorem originalSphereHo_forward_toNative_projection :
    originalLeftProjection.{u, v} ⋙
        (originalSphereHoEquivalence.{u, v}.functor ⋙
          (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor) =
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor) ⋙
          toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v} := by
  calc
    originalLeftProjection ⋙
        (originalSphereHoEquivalence.functor ⋙
          (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor) =
      (originalLeftProjection ⋙ originalSphereHoEquivalence.functor) ⋙
        (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor := rfl
    _ = (SymmetricRightModulePresentation.sphereModuleEquivalence.functor ⋙
        (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) ⋙
          (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor := by
      rw [originalSphereHo_forward_projection]
    _ = SymmetricRightModulePresentation.sphereModuleEquivalence.functor ⋙
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
          (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor) := rfl
    _ = SymmetricRightModulePresentation.sphereModuleEquivalence.functor ⋙
        (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor ⋙
          toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}) := by
      rw [RightPresentationModel.LevelHomotopy.toNativeHo_projection]
    _ = (SymmetricRightModulePresentation.sphereModuleEquivalence.functor ⋙
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor) ⋙
          toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v} := rfl

/-- The literal two-stage source carrier lift before applying its given original unit inverse. -/
@[instance_reducible]
def originalSphereNativeCompositeLifting : Localization.Lifting originalLeftProjection.{u, v}
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})
    ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
      SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor) ⋙
        toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})
    (originalSphereHoEquivalence.{u, v}.functor ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor) :=
  ⟨eqToIso originalSphereHo_forward_toNative_projection⟩

/-- The full forward carrier comparison retains the literal original sphere unit inverse. -/
def originalSphereNativeComparison :
    originalSphereHoEquivalence.{u, v}.functor ⋙
        (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ≅
      NativePresentation.LevelHo.forward SymmetricModulePresentation.moduleOperatorEquivalence.{u,
        v} := by
  letI : originalLeftProjection.{u, v}.IsLocalization
      (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) := by
    change (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).Q.IsLocalization
      (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})
    infer_instance
  letI : Localization.Lifting originalLeftProjection.{u, v}
      (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})
      ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor) ⋙
          toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})
      (originalSphereHoEquivalence.{u, v}.functor ⋙
        (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor) :=
    originalSphereNativeCompositeLifting
  letI : Localization.Lifting originalLeftProjection.{u, v}
      (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})
      (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor ⋙
        toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})
      (NativePresentation.LevelHo.forward
        SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}) :=
    ⟨eqToIso (show originalLeftProjection.{u, v} ⋙ NativePresentation.LevelHo.forward
        SymmetricModulePresentation.moduleOperatorEquivalence.{u, v} =
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor ⋙
        toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v} from
      NativePresentation.LevelHo.forward_projection
        SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})⟩
  have route :
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor) ⋙
          toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v} =
      ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse) ⋙
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor) ⋙
            toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v} :=
    congrArg (fun e => (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
      e.functor) ⋙ toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})
      rightOperatorEquivalence_eq
  let sourceIso :
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor ⋙
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor) ⋙
          toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v} ≅
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor ⋙
        toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v} :=
    eqToIso route ≪≫ Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
          SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.unitIso.symm
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor ≪≫
        Functor.leftUnitor SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor)
      (toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})
  exact Localization.liftNatIso originalLeftProjection
    (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier) _ _ _ _ sourceIso

theorem originalSphereNativeComparison_hom (X : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    originalSphereNativeComparison.hom.app (originalLeftProjection.obj X) =
      (toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}).map
        (SymmetricModulePresentation.moduleOperatorEquivalence.functor.map
          (SymmetricRightModulePresentation.sphereModuleEquivalence.unitIso.inv.app X)) := by
  rw [originalSphereNativeComparison]
  simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    eqToIso.inv, eqToHom_app]
  change 𝟙 _ ≫ (toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}).map
    (SymmetricModulePresentation.moduleOperatorEquivalence.functor.map
      (SymmetricRightModulePresentation.sphereModuleEquivalence.unitIso.inv.app X) ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- The actual canonical derived forward map compares with the given original operator lift. -/
def toRightDerivedNativeComparison : toRightDerivedAdjunctionData.{u, v}.leftDerived ⋙
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ≅
      NativePresentation.LevelHo.forward SymmetricModulePresentation.moduleOperatorEquivalence.{u,
        v} :=
  Functor.isoWhiskerRight toRightCarrierLeftComparison
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ≪≫
      originalSphereNativeComparison

theorem toRightDerivedNativeComparison_hom (X : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    toRightDerivedNativeComparison.hom.app (originalLeftProjection.obj X) =
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor.map
          (toRightDerivedAdjunctionData.leftComparison.app X) ≫
        (toHomotopyCategory PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}).map
          (SymmetricModulePresentation.moduleOperatorEquivalence.functor.map
            (SymmetricRightModulePresentation.sphereModuleEquivalence.unitIso.inv.app X)) := by
  change (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor.map
      (toRightCarrierLeftComparison.hom.app (originalLeftProjection.obj X)) ≫
        originalSphereNativeComparison.hom.app (originalLeftProjection.obj X) = _
  exact congrArg₂ (fun f g => f ≫ g)
    (congrArg (fun f => (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor.map f)
      (toRightCarrierLeftComparison_hom X)) (originalSphereNativeComparison_hom X)

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel

namespace PointedCGWH.Spectra.Symmetric.LeftRightNativeModel.Canonical

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction


attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel toRight_isQuillenAdjunction
  toLeft_isQuillenAdjunction

/-- The literal original LEFT localization of the complete given module/operator carrier. -/
abbrev originalLeftHo := PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}

/-- The strict original LEFT projection keeps the actual source weak-class construction. -/
abbrev originalLeftProjection := PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.{u, v}

theorem originalLeftHo_eq_model :
    originalLeftHo.{u, v} = HomotopyCategory Spectrum.{u, v} := rfl

theorem originalLeftProjection_eq_model : originalLeftProjection.{u, v} =
    toHomotopyCategory Spectrum.{u, v} := rfl

theorem originalRightHo_eq_model : PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v} =
    HomotopyCategory Spectrum.{u, v} := rfl

theorem originalRightProjection_eq_model : PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.{u, v} =
    toHomotopyCategory Spectrum.{u, v} := rfl

/-- The whole original sphere conversion on the two already identified original Ho categories. -/
def originalSphereHoEquivalence : originalLeftHo.{u, v} ≌
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v} :=
  Localization.originalEquivalence
    carrierEquivalence.{u, v}
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      carrierEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      carrierEquivalence.{u, v} toLeft_allWeakMaps)

/-- The whole original inverse conversion uses its own given inverse unit and counit. -/
def originalInverseSphereHoEquivalence : PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v} ≌
    originalLeftHo.{u, v} :=
  Localization.originalEquivalence
    carrierEquivalence.{u, v}.symm
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      carrierEquivalence.{u, v}.symm toLeft_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      carrierEquivalence.{u, v}.symm toRight_allWeakMaps)

theorem originalSphereHo_forward_projection :
    originalLeftProjection.{u, v} ⋙ originalSphereHoEquivalence.{u, v}.functor =
      carrierEquivalence.{u, v}.functor ⋙
        PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.{u, v} :=
  Localization.originalForward_projection
    carrierEquivalence.{u, v}
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      carrierEquivalence.{u, v} toRight_allWeakMaps)

theorem originalSphereHo_inverse_projection :
    PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.{u, v} ⋙
        originalSphereHoEquivalence.{u, v}.inverse =
      carrierEquivalence.{u, v}.inverse ⋙
        originalLeftProjection.{u, v} :=
  Localization.originalInverse_projection
    carrierEquivalence.{u, v}
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.inverseInverts
      carrierEquivalence.{u, v} toLeft_allWeakMaps)

theorem originalSphereHo_forward_map {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    originalSphereHoEquivalence.functor.map (originalLeftProjection.map f) =
      PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.map
        (carrierEquivalence.{u, v}.functor.map f) :=
  Localization.originalForward_map_projected
    carrierEquivalence.{u, v}
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      carrierEquivalence.{u, v} toRight_allWeakMaps) f

theorem originalSphereHo_inverse_map {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    originalSphereHoEquivalence.inverse.map
        (PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.map f) =
      originalLeftProjection.map
        (carrierEquivalence.{u, v}.inverse.map f) :=
  Localization.originalInverse_map_projected
    carrierEquivalence.{u, v}
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.inverseInverts
      carrierEquivalence.{u, v} toLeft_allWeakMaps) f

theorem originalSphereHo_unit_hom (X : Spectrum.{u, v}) :
    originalSphereHoEquivalence.unitIso.hom.app (originalLeftProjection.obj X) =
      originalLeftProjection.map
        (carrierEquivalence.{u, v}.unitIso.hom.app X) :=
  Localization.originalUnitIso_hom_projected
    carrierEquivalence.{u, v}
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      carrierEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      carrierEquivalence.{u, v} toLeft_allWeakMaps) X

theorem originalSphereHo_unit_inv (X : Spectrum.{u, v}) :
    originalSphereHoEquivalence.unitIso.inv.app (originalLeftProjection.obj X) =
      originalLeftProjection.map
        (carrierEquivalence.{u, v}.unitIso.inv.app X) :=
  Localization.originalUnitIso_inv_projected
    carrierEquivalence.{u, v}
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      carrierEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      carrierEquivalence.{u, v} toLeft_allWeakMaps) X

theorem originalSphereHo_counit_hom (Y : Spectrum.{u, v}) :
    originalSphereHoEquivalence.counitIso.hom.app
        (PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.obj Y) =
      PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.map
        (carrierEquivalence.{u, v}.counitIso.hom.app Y) :=
  Localization.originalCounitIso_hom_projected
    carrierEquivalence.{u, v}
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      carrierEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      carrierEquivalence.{u, v} toLeft_allWeakMaps) Y

theorem originalSphereHo_counit_inv (Y : Spectrum.{u, v}) :
    originalSphereHoEquivalence.counitIso.inv.app
        (PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.obj Y) =
      PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.map
        (carrierEquivalence.{u, v}.counitIso.inv.app Y) :=
  Localization.originalCounitIso_inv_projected
    carrierEquivalence.{u, v}
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      carrierEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      carrierEquivalence.{u, v} toLeft_allWeakMaps) Y

theorem originalInverseSphereHo_unitIso : originalInverseSphereHoEquivalence.{u, v}.unitIso =
    originalSphereHoEquivalence.{u, v}.counitIso.symm :=
  Localization.originalEquivalence_unitIso_symm
    carrierEquivalence.{u, v}
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      carrierEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      carrierEquivalence.{u, v} toLeft_allWeakMaps)

theorem originalInverseSphereHo_counitIso : originalInverseSphereHoEquivalence.{u, v}.counitIso =
    originalSphereHoEquivalence.{u, v}.unitIso.symm :=
  Localization.originalEquivalence_counitIso_symm
    carrierEquivalence.{u, v}
    (weakEquivalences Spectrum.{u, v}) (weakEquivalences
      Spectrum.{u, v})
    (QuillenCarrierLocalization.forwardInverts
      carrierEquivalence.{u, v} toRight_allWeakMaps)
    (QuillenCarrierLocalization.inverseInverts
      carrierEquivalence.{u, v} toLeft_allWeakMaps)

/-- The entire original forward total left derived functor compares with its strict carrier lift. -/
def toRightCarrierLeftComparison : toRightDerivedAdjunctionData.{u, v}.leftDerived ≅
    originalSphereHoEquivalence.{u, v}.functor :=
  QuillenCarrierLocalization.leftDerivedComparison
    carrierEquivalence.{u, v} toRight_allWeakMaps

/-- The original forward total right derived functor keeps its actual inverse carrier comparison. -/
def toRightCarrierRightComparison : originalSphereHoEquivalence.{u, v}.inverse ≅
    toRightDerivedAdjunctionData.{u, v}.rightDerived :=
  QuillenCarrierLocalization.rightDerivedComparison
    carrierEquivalence.{u, v} toLeft_allWeakMaps

/-- The actual inverse total left derived functor compares with the whole inverse carrier lift. -/
def toLeftCarrierLeftComparison : toLeftDerivedAdjunctionData.{u, v}.leftDerived ≅
    originalInverseSphereHoEquivalence.{u, v}.functor :=
  QuillenCarrierLocalization.leftDerivedComparison
    carrierEquivalence.{u, v}.symm toLeft_allWeakMaps

/-- The inverse total right derived functor retains the actual original forward carrier lift. -/
def toLeftCarrierRightComparison : originalInverseSphereHoEquivalence.{u, v}.inverse ≅
    toLeftDerivedAdjunctionData.{u, v}.rightDerived :=
  QuillenCarrierLocalization.rightDerivedComparison
    carrierEquivalence.{u, v}.symm toRight_allWeakMaps

theorem toRightCarrierLeftComparison_hom (X : Spectrum.{u, v}) :
    toRightCarrierLeftComparison.hom.app (originalLeftProjection.obj X) =
      toRightDerivedAdjunctionData.leftComparison.app X :=
  QuillenCarrierLocalization.leftDerivedComparisonHomProjected
    carrierEquivalence.{u, v} toRight_allWeakMaps X

theorem toRightCarrierRightComparison_hom (Y : Spectrum.{u, v}) :
    toRightCarrierRightComparison.hom.app (PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.obj Y) =
      toRightDerivedAdjunctionData.rightComparison.app Y :=
  QuillenCarrierLocalization.rightDerivedComparisonHomProjected
    carrierEquivalence.{u, v} toLeft_allWeakMaps Y

theorem toLeftCarrierLeftComparison_hom (Y : Spectrum.{u, v}) :
    toLeftCarrierLeftComparison.hom.app (PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection.obj Y) =
      toLeftDerivedAdjunctionData.leftComparison.app Y :=
  QuillenCarrierLocalization.leftDerivedComparisonHomProjected
    carrierEquivalence.{u, v}.symm toLeft_allWeakMaps Y

theorem toLeftCarrierRightComparison_hom (X : Spectrum.{u, v}) :
    toLeftCarrierRightComparison.hom.app (originalLeftProjection.obj X) =
      toLeftDerivedAdjunctionData.rightComparison.app X :=
  QuillenCarrierLocalization.rightDerivedComparisonHomProjected
    carrierEquivalence.{u, v}.symm toRight_allWeakMaps X

theorem toRightCarrier_unit : toRightDerivedAdjunctionData.{u, v}.adjunction.unit ≫
    Functor.whiskerRight toRightCarrierLeftComparison.hom
      toRightDerivedAdjunctionData.rightDerived =
    originalSphereHoEquivalence.unitIso.hom ≫
      Functor.whiskerLeft originalSphereHoEquivalence.functor toRightCarrierRightComparison.hom :=
  QuillenCarrierLocalization.unitComparison
    carrierEquivalence.{u, v} toRight_allWeakMaps
        toLeft_allWeakMaps

theorem toRightCarrier_counit : Functor.whiskerRight toRightCarrierRightComparison.hom
      toRightDerivedAdjunctionData.{u, v}.leftDerived ≫
        toRightDerivedAdjunctionData.adjunction.counit =
    Functor.whiskerLeft originalSphereHoEquivalence.inverse toRightCarrierLeftComparison.hom ≫
      originalSphereHoEquivalence.counitIso.hom :=
  QuillenCarrierLocalization.counitComparison
    carrierEquivalence.{u, v} toRight_allWeakMaps
        toLeft_allWeakMaps

theorem toLeftCarrier_unit : toLeftDerivedAdjunctionData.{u, v}.adjunction.unit ≫
    Functor.whiskerRight toLeftCarrierLeftComparison.hom toLeftDerivedAdjunctionData.rightDerived =
    originalInverseSphereHoEquivalence.unitIso.hom ≫
      Functor.whiskerLeft originalInverseSphereHoEquivalence.functor
        toLeftCarrierRightComparison.hom :=
  QuillenCarrierLocalization.unitComparison
    carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
        toRight_allWeakMaps

theorem toLeftCarrier_counit : Functor.whiskerRight toLeftCarrierRightComparison.hom
      toLeftDerivedAdjunctionData.{u, v}.leftDerived ≫
        toLeftDerivedAdjunctionData.adjunction.counit =
    Functor.whiskerLeft originalInverseSphereHoEquivalence.inverse toLeftCarrierLeftComparison.hom ≫
      originalInverseSphereHoEquivalence.counitIso.hom :=
  QuillenCarrierLocalization.counitComparison
    carrierEquivalence.{u, v}.symm toLeft_allWeakMaps
        toRight_allWeakMaps


/-- The actual conjugated right-operator counit compares the full native carrier lift. -/
def originalSphereNativeComparison : originalSphereHoEquivalence.{u, v}.functor ≅
    𝟭 PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v} := by
  letI : Localization.Lifting originalLeftProjection.{u, v}
      (weakEquivalences Spectrum.{u, v})
      (carrierEquivalence.{u, v}.functor ⋙ PointedCGWH.Spectra.Symmetric.LevelHomotopy.projection)
      originalSphereHoEquivalence.functor :=
    ⟨eqToIso originalSphereHo_forward_projection⟩
  letI : Localization.Lifting originalLeftProjection.{u, v}
      (weakEquivalences Spectrum.{u, v}) originalLeftProjection.{u, v}
      (𝟭 PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v}) :=
    ⟨Functor.rightUnitor originalLeftProjection⟩
  exact Localization.liftNatIso originalLeftProjection (weakEquivalences Spectrum.{u, v})
    _ _ _ _ (Functor.isoWhiskerRight forwardComparisonIso originalLeftProjection ≪≫
      Functor.leftUnitor originalLeftProjection)

/-- Every projected component retains that same actual operator counit. -/
theorem originalSphereNativeComparison_hom (X : Spectrum.{u, v}) :
    originalSphereNativeComparison.hom.app (originalLeftProjection.obj X) =
      originalLeftProjection.map (forwardComparisonIso.hom.app X) := by
  rw [originalSphereNativeComparison]
  simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change 𝟙 _ ≫ (originalLeftProjection.map (forwardComparisonIso.hom.app X) ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- The full canonical derived functor compares with the actual native operator identity lift. -/
def toRightDerivedNativeComparison : toRightDerivedAdjunctionData.{u, v}.leftDerived ≅
    𝟭 PointedCGWH.Spectra.Symmetric.LevelHomotopy.HoCategory.{u, v} :=
  toRightCarrierLeftComparison ≪≫ originalSphereNativeComparison

/-- Every derived component keeps its given comparison and the complete original operator counit. -/
theorem toRightDerivedNativeComparison_hom (X : Spectrum.{u, v}) :
    toRightDerivedNativeComparison.hom.app (originalLeftProjection.obj X) =
      toRightDerivedAdjunctionData.leftComparison.app X ≫
        originalLeftProjection.map (forwardComparisonIso.hom.app X) := by
  change toRightCarrierLeftComparison.hom.app (originalLeftProjection.obj X) ≫
    originalSphereNativeComparison.hom.app (originalLeftProjection.obj X) = _
  exact congrArg₂ (fun f g => f ≫ g) (toRightCarrierLeftComparison_hom X)
    (originalSphereNativeComparison_hom X)

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel.Canonical
