/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension.ScalarSmashFunctorFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricScalarSmashUnitCoherence
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.BasedHomotopyExtension

/-!
# Scalar endpoints and symmetric smash products

A coefficient endpoint `𝟙 ⟶ T` commutes with the scalar–smash comparison
on arbitrary symmetric spectra. This specializes to every free-time point
and both realized-interval endpoints. The inverse functor comparison gives
the zero-endpoint naturality equation for right smashing in both cases.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension

open SymmetricScalarSmash

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  SymmetricSmash.monoidalCategory SymmetricSmash.symmetricCategory SymmetricSmash.monoidalClosed

/-- Every original pointed coefficient endpoint keeps the unit inverse and the full actual scalar interchange. -/
theorem coefficientEndpoint_interchange {T : PointedCGWH.{u, v}}
    (a : (𝟙_ PointedCGWH.{u, v}) ⟶ T) (X Y : Carrier.{u, v}) :
    ((scalarUnitIso (X ⊗ Y)).inv ≫ scalarTensorMap a (X ⊗ Y)) ≫
        (scalarSmashIso T X Y).hom =
      ((scalarUnitIso X).inv ≫ scalarTensorMap a X) ▷ Y :=
  Primitive.endpointInterchange
    ((ScalarLeibniz.tensorBifunctor
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map a) X Y
    (scalarSmashIso (𝟙_ PointedCGWH.{u, v}) X Y) (scalarSmashIso T X Y)
    (scalarUnitIso X) (scalarUnitIso (X ⊗ Y))
    (scalarSmashIso_coefficient a X Y) (UnitCoherence.scalarSmashIso_unit X Y)

/-- Every literal free-time endpoint keeps the original inclusion on both arbitrary native spectra. -/
theorem timeInclusion_interchange (t : unitInterval) (X Y : Carrier.{u, v}) :
    PointedCGWH.EnrichedIntervalContraction.timeInclusion t (X ⊗ Y) ≫
        (scalarSmashIso PointedCGWH.RealizedIntervalContraction.time X Y).hom =
      PointedCGWH.EnrichedIntervalContraction.timeInclusion t X ▷ Y :=
  coefficientEndpoint_interchange (PointedCGWH.freePointIntervalEndpoint t) X Y

/-- Both original realized interval endpoints keep their full original scalar unit and coefficient maps. -/
theorem intervalInclusion_interchange (j : Fin 2) (X Y : Carrier.{u, v}) :
    PointedCGWH.EnrichedIntervalCylinder.inclusion j (X ⊗ Y) ≫
        (scalarSmashIso PointedCGWH.IntervalCoefficient.interval X Y).hom =
      PointedCGWH.EnrichedIntervalCylinder.inclusion j X ▷ Y := by
  rw [PointedCGWH.EnrichedIntervalCylinder.inclusion_eq,
    PointedCGWH.EnrichedIntervalCylinder.inclusion_eq]
  exact coefficientEndpoint_interchange (PointedCGWH.IntervalCoefficient.endpoint j) X Y

set_option maxHeartbeats 500000 in

/-- The original time endpoint is carried by the exact inverse whole right-smash comparison. -/
theorem timeRightSmash_endpoint (Y Z : Carrier.{u, v}) :
    (MonoidalCategory.tensorRight Y).map
        ((PointedCGWH.EnrichedIntervalContraction.timeInclusionNatTrans 0).app Z) ≫
      (((scalarSmashFunctorIso PointedCGWH.RealizedIntervalContraction.time Y).symm).app Z).hom =
    (PointedCGWH.EnrichedIntervalContraction.timeInclusionNatTrans 0).app
      ((MonoidalCategory.tensorRight Y).obj Z) := by
  have hC := scalarSmashFunctorIso_symm_app_hom PointedCGWH.RealizedIntervalContraction.time Z Y
  have hE : (PointedCGWH.EnrichedIntervalContraction.timeInclusion 0 Z ▷ Y) ≫
      (scalarSmashIso PointedCGWH.RealizedIntervalContraction.time Z Y).inv =
    PointedCGWH.EnrichedIntervalContraction.timeInclusion 0 (Z ⊗ Y) := by
    apply (cancel_mono (scalarSmashIso PointedCGWH.RealizedIntervalContraction.time Z Y).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (timeInclusion_interchange 0 Z Y).symm
  exact (congrArg₂ (fun f g => f ≫ g) (Eq.refl
    (PointedCGWH.EnrichedIntervalContraction.timeInclusion 0 Z ▷ Y)) hC).trans hE

set_option maxHeartbeats 500000 in

/-- The original delta-zero endpoint is carried by the exact inverse whole right-smash comparison. -/
theorem intervalRightSmash_endpoint (Y Z : Carrier.{u, v}) :
    (MonoidalCategory.tensorRight Y).map
        ((PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0).app Z) ≫
      (((scalarSmashFunctorIso PointedCGWH.IntervalCoefficient.interval Y).symm).app Z).hom =
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0).app
      ((MonoidalCategory.tensorRight Y).obj Z) := by
  have hC := scalarSmashFunctorIso_symm_app_hom PointedCGWH.IntervalCoefficient.interval Z Y
  have hE : (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 Z ▷ Y) ≫
      (scalarSmashIso PointedCGWH.IntervalCoefficient.interval Z Y).inv =
    PointedCGWH.EnrichedIntervalCylinder.inclusion 0 (Z ⊗ Y) := by
    apply (cancel_mono (scalarSmashIso PointedCGWH.IntervalCoefficient.interval Z Y).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (intervalInclusion_interchange 0 Z Y).symm
  exact (congrArg₂ (fun f g => f ≫ g) (Eq.refl
    (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 Z ▷ Y)) hC).trans hE







end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension
