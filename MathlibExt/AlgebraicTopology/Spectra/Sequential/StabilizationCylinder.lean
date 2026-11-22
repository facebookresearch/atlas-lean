/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationMapping
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderCofibration
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSphereOne

/-!
# Actual native stabilization mapping cylinders

The original unitStabilizationMap at the original native one-sphere is the
literal caller arrow. The original native free/evaluation Quillen outputs
and actual pointed unit/sphere cofibrancy supply both cofibrant endpoints.
The same actual mapping-cylinder source is a cofibration and retraction is
level weak at every native degree. No factorization/cofibrancy/weak or stable
model dictionary is an input.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  MonoidalClosed.enrichedCategorySelf

private theorem freeCoefficient_cofibrant
    (a : CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne.{u, v})
    (T : PointedCGWH.{u, v}) [IsCofibrant T] : IsCofibrant (Free.object a T) := by
  let _ : (Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    HomotopicalAlgebra.EnrichedProjective.Native.freeAtEvaluation_isQuillenAdjunction a
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := Free.adjunction (V := PointedCGWH.{u, v}) a) inferInstance

/-- The actual original sphere-coefficient stabilization source is native cofibrant. -/
theorem unitStabilization_source_cofibrant (n : ℕ) :
    IsCofibrant (Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)).left := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  change IsCofibrant (Free.object
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne (n + 1))
      PointedCGWH.sphereOne.{u, v})
  exact freeCoefficient_cofibrant _ _

/-- The actual original unit-coefficient stabilization target is native cofibrant. -/
theorem unitStabilization_target_cofibrant (n : ℕ) :
    IsCofibrant (Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)).right := by
  let _ : IsCofibrant (𝟙_ PointedCGWH.{u, v}) :=
    PointedCGWH.modelCategory.smashUnit_isCofibrant
  change IsCofibrant (Free.object
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n)
      (𝟙_ PointedCGWH.{u, v}))
  exact freeCoefficient_cofibrant _ _

/-- The actual mapping cylinder of the same original native stabilization arrow. -/
abbrev stabilizationCylinder (n : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} :=
  EnrichedIntervalMappingCylinder.object
    (Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne n))

/-- The original second interval endpoint gives the actual stabilization cofibration factor. -/
abbrev stabilizationCylinderSource (n : ℕ) :=
  EnrichedIntervalMappingCylinder.source
    (Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n))

/-- The original same mapping-cylinder contraction gives the actual weak retraction factor. -/
abbrev stabilizationCylinderRetraction (n : ℕ) :=
  EnrichedIntervalMappingCylinder.retraction
    (Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n))

omit B in
/-- The factorization retains the literal original stabilization map. -/
theorem stabilizationCylinder_fac (n : ℕ) :
    stabilizationCylinderSource.{u, v} n ≫ stabilizationCylinderRetraction n =
      unitStabilizationMap PointedCGWH.sphereOne.{u, v} n :=
  EnrichedIntervalMappingCylinder.fac _

/-- The literal actual stabilization source factor is a native projective cofibration. -/
theorem stabilizationCylinderSource_cofibration (n : ℕ) :
    Cofibration (stabilizationCylinderSource.{u, v} n) := by
  let _ : IsCofibrant
      (Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)).left :=
    unitStabilization_source_cofibrant n
  let _ : IsCofibrant
      (Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)).right :=
    unitStabilization_target_cofibrant n
  exact EnrichedIntervalMappingCylinderModel.source_cofibration _

/-- The literal actual stabilization retraction factor is weak
in the original native level model. -/
theorem stabilizationCylinderRetraction_weakEquivalence (n : ℕ) :
    WeakEquivalence (stabilizationCylinderRetraction.{u, v} n) := by
  let _ : IsCofibrant
      (Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)).left :=
    unitStabilization_source_cofibrant n
  exact EnrichedIntervalMappingCylinderModel.retraction_weakEquivalence _

/-- Every original native degree sees the actual same retraction as pointed weak. -/
theorem stabilizationCylinderRetraction_evaluation_weak (n m : ℕ) :
    weakEquivalences PointedCGWH.{u, v}
      ((EnrichedFunctorCat.evaluation
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)).map
          (stabilizationCylinderRetraction.{u, v} n)) := by
  let _ : IsCofibrant
      (Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)).left :=
    unitStabilization_source_cofibrant n
  exact EnrichedIntervalMappingCylinderModel.retraction_evaluation_weak _ _

end PointedCGWH.SequentialSpectrum
