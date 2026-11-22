/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationMappingNormalization
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationCylinder
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableK
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSphereOne

/-!
# The original sequential stabilization family in the shared native K API

Every comparison uses the same actual sphere, degree, successor inclusion,
unit-normalized free map, mapping cylinder and correlated scalar family.
The fixed realized-boundary/horn convention and original cardinal are retained.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.StabilizationKAdapter

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev SequentialIndex :=
  CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne.{u, v}

private abbrev degree (n : ℕ) :=
  CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne.{u, v} n

private abbrev successorIso (n : ℕ) :=
  CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
    PointedCGWH.sphereOne.{u, v} n

private theorem dependent_congr {A : Sort _} {B : A → Sort _}
    (f : ∀ a, B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

/-- The sequential adapter aliases the one original native family in the StableK home. -/
abbrev family : NativeStabilizationFamily.{u, v} SequentialIndex ℕ :=
  StableK.stabilizationFamily

/-- Equality is proved through the original whole Free adjunct, without choosing another map. -/
theorem stabilization_eq_unitStabilizationMap (n : ℕ) :
    NativeK.stabilization.{u, v} family n =
      unitStabilizationMap PointedCGWH.sphereOne.{u, v} n :=
  StableK.stabilizationFamily_stabilization_eq_unitStabilizationMap n

/-- The whole original family function keeps every source, target and inclusion label. -/
theorem stabilization_function_eq :
    (fun n : ℕ => NativeK.stabilization.{u, v} family n) =
      unitStabilizationMap PointedCGWH.sphereOne.{u, v} := by
  funext n
  exact stabilization_eq_unitStabilizationMap n

/-- The complete cylinder object is formed from the same original unit-normalized map. -/
theorem cylinder_eq (n : ℕ) :
    NativeK.cylinder.{u, v} family n = stabilizationCylinder.{u, v} n := by
  dsimp [NativeK.cylinder, stabilizationCylinder]
  rw [stabilization_eq_unitStabilizationMap]
  rfl

/-- The entire actual cylinder-source Arrow retains both original endpoints. -/
private theorem cylinderSourceArrow_eq (n : ℕ) :
    Arrow.mk (NativeK.cylinderSource.{u, v} family n) =
      Arrow.mk (stabilizationCylinderSource.{u, v} n) := by
  exact congrArg
    (fun f : Arrow PointedCGWH.SequentialSpectrum.{u, v} =>
      Arrow.mk (EnrichedIntervalMappingCylinder.source f))
    (congrArg Arrow.mk (stabilization_eq_unitStabilizationMap n))

/-- Both original cylinder sources retain their literal full map values. -/
theorem cylinderSource_eq (n : ℕ) :
    HEq (NativeK.cylinderSource.{u, v} family n)
      (stabilizationCylinderSource.{u, v} n) := by
  simpa only [Arrow.mk_hom] using
    dependent_congr (fun f : Arrow PointedCGWH.SequentialSpectrum.{u, v} => f.hom)
      (cylinderSourceArrow_eq n)

/-- Both original cylinder retractions retain the complete actual target map. -/
theorem cylinderRetraction_eq (n : ℕ) :
    HEq (NativeK.cylinderRetraction.{u, v} family n)
      (stabilizationCylinderRetraction.{u, v} n) := by
  have h : Arrow.mk (NativeK.cylinderRetraction.{u, v} family n) =
      Arrow.mk (stabilizationCylinderRetraction.{u, v} n) :=
    congrArg
      (fun f : Arrow PointedCGWH.SequentialSpectrum.{u, v} =>
        Arrow.mk (EnrichedIntervalMappingCylinder.retraction f))
      (congrArg Arrow.mk (stabilization_eq_unitStabilizationMap n))
  simpa only [Arrow.mk_hom] using
    dependent_congr (fun f : Arrow PointedCGWH.SequentialSpectrum.{u, v} => f.hom) h

/-- Both tensor families are the same original whole scalar bifunctor. -/
theorem tensorBifunctor_eq :
    WeightedEndVariance.tensorBifunctor
      (V := PointedCGWH.{u, v}) (I := SequentialIndex) =
      ScalarLeibniz.tensorBifunctor
        (V := PointedCGWH.{u, v}) (A := SequentialIndex) := rfl

/-- Both original scalar boundary families have the same complete coefficient arrow. -/
theorem boundaryMap_eq (m : ℕ) :
    NativeK.boundaryMap.{u, v} m = StableK.boundaryMap.{u, v} m := rfl

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

omit B in
/-- The complete actual generator Arrow keeps the original endpoints as well as its map. -/
theorem generatorArrow_obj_eq (n m : ℕ) :
    Arrow.mk (NativeK.generatorMap.{u, v} family n m) =
      Arrow.mk (StableK.generatorMap.{u, v} n m) :=
  StableK.stabilizationFamily_generatorArrow_eq n m

omit B in
/-- The original full correlated generator arrow keeps both labels and both endpoints. -/
theorem generatorMap_eq (n m : ℕ) :
    HEq (NativeK.generatorMap.{u, v} family n m) (StableK.generatorMap.{u, v} n m) := by
  simpa only [Arrow.mk_hom] using
    dependent_congr (fun f : Arrow PointedCGWH.SequentialSpectrum.{u, v} => f.hom)
      (generatorArrow_obj_eq n m)

omit B in
/-- Equality of the whole pair-indexed Arrow function retains every original n,m value. -/
theorem generatorArrow_function_eq :
    (fun nm : ℕ × ℕ => Arrow.mk (NativeK.generatorMap.{u, v} family nm.1 nm.2)) =
      fun nm => Arrow.mk (StableK.generatorMap.{u, v} nm.1 nm.2) := by
  funext nm
  exact generatorArrow_obj_eq nm.1 nm.2

omit B in
/-- The entire original additional class is unchanged through the actual pair function. -/
theorem additionalGenerators_eq :
    NativeK.additionalGenerators.{u, v} family = StableK.additionalGenerators.{u, v} :=
  StableK.stabilizationFamily_additionalGenerators_eq

omit B in
/-- Both constructions retain the same entire original free-horn J family. -/
theorem levelJ_eq : NativeK.levelJ.{u, v} (I := SequentialIndex) = StableK.levelJ.{u, v} := rfl

omit B in
/-- The literal K classes are equal after the original full family value correspondences. -/
theorem generators_eq : NativeK.generators.{u, v} family = StableK.generators.{u, v} := rfl

/-- The original sequential K source-smallness obligations are supplied by the shared factory. -/
theorem original_generators_eligible :
    StableK.generators.{u, v}.IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := by
  rw [← generators_eq]
  exact NativeK.generators_isCardinalForSmallObjectArgument.{u, v} family

omit B in
/-- Both full zero-arrow functors keep the same explicit native zero and all original maps. -/
theorem zeroArrows_eq :
    NativeK.zeroArrows.{u, v} (I := SequentialIndex) =
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZeroArrow := by
  rfl

/-- The original sequential K data aliases the shared native data, with only class transport. -/
abbrev originalFactorizationData :
    MorphismProperty.FunctorialFactorizationData
      StableK.generators.{u, v}.rlp.llp StableK.generators.rlp :=
  (NativeK.factorizationData.{u, v} (B := B) family).ofLE
    (by rw [generators_eq]) (by rw [generators_eq])

section
attribute [local instance] original_generators_eligible

/-- The whole alias keeps the original literal κ/B small-object choice for the old K family. -/
theorem originalFactorizationData_eq_original : originalFactorizationData.{u, v} (B := B) =
    SmallObject.functorialFactorizationData StableK.generators.{u, v}
      realizedGeneratorCardinal.{v} := rfl

end

/-- The whole middle functor is the shared native value without a second small-object argument. -/
theorem factorizationData_Z_eq :
    (NativeK.factorizationData.{u, v} (B := B) family).Z =
      (originalFactorizationData.{u, v} (B := B)).Z := rfl

/-- Both original left factor functions are the same complete shared natural transformation. -/
theorem factorizationData_i_eq :
    HEq (NativeK.factorizationData.{u, v} (B := B) family).i
      (originalFactorizationData.{u, v} (B := B)).i := HEq.rfl

/-- Both original right factor functions are the same complete shared natural transformation. -/
theorem factorizationData_p_eq :
    HEq (NativeK.factorizationData.{u, v} (B := B) family).p
      (originalFactorizationData.{u, v} (B := B)).p := HEq.rfl

private def sourceMappingArrows
    (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    PointedCGWH.SequentialSpectrum.{u, v} → Arrow PointedCGWH.{u, v} :=
  fun X => Arrow.mk (EnrichedFunctorCat.WeightedEndVariance.pre f.hom X)

omit B in
/-- Both complete source-mapping Arrow functions keep all original endpoint mapping objects. -/
theorem cylinderMappingSource_function_eq (n : ℕ) :
    sourceMappingArrows (Arrow.mk (NativeK.cylinderSource.{u, v} family n)) =
      sourceMappingArrows (Arrow.mk (stabilizationCylinderSource.{u, v} n)) :=
  congrArg sourceMappingArrows (cylinderSourceArrow_eq n)

end PointedCGWH.SequentialSpectrum.StabilizationKAdapter
