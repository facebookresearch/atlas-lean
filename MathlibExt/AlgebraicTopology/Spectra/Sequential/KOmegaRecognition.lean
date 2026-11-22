/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOneSphereRecognition
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKReflection
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationKAdapter
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationMapping
import MathlibExt.Topology.Category.PointedCGWH.NativeMappingCorner

/-!
# Original sequential K recognition through the current native mapping functor

The source, retraction, zero corner and original stabilization map keep
their actual values. The shared native source functor supplies the full
mapping maps and its factorization law. Both original K recognition
directions and level-fibration recognition remain on the original carrier.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat PointedCGWH.EnrichedFunctorMapping
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.StableK

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

omit B in
private theorem pointedWeak_iff {A C : PointedCGWH.{u, v}} (f : A ⟶ C) :
    weakEquivalences PointedCGWH.{u, v} f ↔ CGWH.weakHomotopyEquivalences f.right :=
  (HomotopicalAlgebra.weakEquivalence_iff f).symm.trans
    ((PointedCGWH.weakEquivalence_iff f).trans (CGWH.modelCategory.weakEquivalence_iff f.right))

/-- The original stabilization cylinder is genuinely native cofibrant. -/
theorem stabilizationCylinder_isCofibrant (n : ℕ) :
    IsCofibrant (stabilizationCylinder.{u, v} n) := by
  let _ : Cofibration (stabilizationCylinderSource.{u, v} n) :=
    stabilizationCylinderSource_cofibration n
  let _ : IsCofibrant (Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)).left :=
    unitStabilization_source_cofibrant n
  exact isCofibrant_of_cofibration (stabilizationCylinderSource n)

/-- The original weak retraction acts weakly on the complete actual native mapping object. -/
theorem stabilizationRetraction_mapping_weak (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    WeakEquivalence (WeightedEndVariance.pre (stabilizationCylinderRetraction n) X) := by
  let _ : WeakEquivalence (stabilizationCylinderRetraction.{u, v} n) :=
    stabilizationCylinderRetraction_weakEquivalence n
  let _ : IsCofibrant (stabilizationCylinder.{u, v} n) := stabilizationCylinder_isCofibrant n
  let _ : IsCofibrant (Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)).right :=
    unitStabilization_target_cofibrant n
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    (NativeK.mapSource_weak_of_cofibrant (stabilizationCylinderRetraction n) X)

omit B in
/-- Source variance keeps the literal original stabilization mapping arrow. -/
theorem stabilizationMappingArrow_eq_mapSource
    (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    stabilizationMappingArrow PointedCGWH.sphereOne n X =
      WeightedEndVariance.pre (unitStabilizationMap PointedCGWH.sphereOne n) X := by
  let A : PointedCGWH.SequentialSpectrum.{u, v} :=
    (freeAt PointedCGWH.sphereOne n).obj (𝟙_ PointedCGWH.{u, v})
  let C : PointedCGWH.SequentialSpectrum.{u, v} :=
    (freeAt PointedCGWH.sphereOne (n + 1)).obj PointedCGWH.sphereOne
  let f : C ⟶ A := unitStabilizationMap PointedCGWH.sphereOne n
  change Enriched.weightedEnd.mapWeight A.toEnrichedFunctor X.toEnrichedFunctor
      C.toEnrichedFunctor f = (PointedCGWH.NativeMappingSourceFunctor.source X).map f.op
  exact (PointedCGWH.NativeMappingSourceFunctor.source_map C A X f).symm

/-- Original cylinder source weakness is exactly original stabilization mapping weakness. -/
theorem stabilizationSource_mapping_weak_iff
    (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    weakEquivalences PointedCGWH.{u, v}
      (WeightedEndVariance.pre (stabilizationCylinderSource n) X) ↔
      weakEquivalences PointedCGWH.{u, v}
        (WeightedEndVariance.pre (unitStabilizationMap PointedCGWH.sphereOne n) X) := by
  let P : MorphismProperty PointedCGWH.{u, v} := weakEquivalences PointedCGWH.{u, v}
  have hSource :
      Arrow.mk (WeightedEndVariance.pre (NativeK.cylinderSource StabilizationKAdapter.family n) X) =
        Arrow.mk (WeightedEndVariance.pre (stabilizationCylinderSource n) X) :=
    congrFun (StabilizationKAdapter.cylinderMappingSource_function_eq n) X
  have hMap :
      Arrow.mk (WeightedEndVariance.pre (NativeK.stabilization StabilizationKAdapter.family n) X) =
        Arrow.mk (WeightedEndVariance.pre (unitStabilizationMap PointedCGWH.sphereOne n) X) :=
    congrArg (fun f => Arrow.mk (WeightedEndVariance.pre f X))
      (StabilizationKAdapter.stabilization_eq_unitStabilizationMap n)
  have hNative :
      P (WeightedEndVariance.pre (NativeK.cylinderSource StabilizationKAdapter.family n) X) ↔
        P (WeightedEndVariance.pre (NativeK.stabilization StabilizationKAdapter.family n) X) :=
    NativeK.cylinderSource_weak_iff StabilizationKAdapter.family n X
  exact (P.arrow_mk_iso_iff (eqToIso hSource)).symm.trans
    (hNative.trans (P.arrow_mk_iso_iff (eqToIso hMap)))

/-- The actual cylinder-source map into any native level target is a pointed fibration. -/
theorem stabilizationSource_mapping_fibration
    (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    fibrations PointedCGWH.{u, v} (WeightedEndVariance.pre (stabilizationCylinderSource n) X) :=
  NativeK.mapSource_fibration _
    ((HomotopicalAlgebra.cofibration_iff _).mp (stabilizationCylinderSource_cofibration n)) X

/-- The original zero-target K corner detects the literal original stabilization test. -/
theorem zeroCorner_trivialFibration_iff (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    trivialFibrations PointedCGWH.{u, v}
      (PointedCGWH.NativeMappingCorner.square (stabilizationCylinderSource n) (toZero X)).π ↔
    CGWH.weakHomotopyEquivalences (stabilizationMappingArrow PointedCGWH.sphereOne n X).right :=
  by
  rw [(trivialFibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (PointedCGWH.NativeMappingZeroSource.cornerArrowIso (stabilizationCylinderSource n) X)]
  change (fibrations PointedCGWH.{u, v}
      (WeightedEndVariance.pre (stabilizationCylinderSource n) X) ∧
    weakEquivalences PointedCGWH.{u, v}
      (WeightedEndVariance.pre (stabilizationCylinderSource n) X)) ↔ _
  have hF := stabilizationSource_mapping_fibration n X
  rw [and_iff_right hF, stabilizationSource_mapping_weak_iff]
  rw [← stabilizationMappingArrow_eq_mapSource]
  exact pointedWeak_iff _

/-- Both original K lifting directions identify genuine native level-fibrant Omega objects. -/
theorem lifting_toZero_iff_fibrantOmega (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    generators.rlp (toZero X) ↔ IsFibrant X ∧ X.IsOmega := by
  constructor
  · intro h
    have hp := (lifting_iff (toZero X)).mp h
    refine ⟨(isFibrant_iff_of_isTerminal (toZero X) zeroDiagramIsTerminal).mpr
      ((HomotopicalAlgebra.fibration_iff _).mpr hp.1), ?_⟩
    exact (isOmega_iff_stabilizationMappingArrows X).mpr
      (fun n => (zeroCorner_trivialFibration_iff n X).mp (hp.2 n))
  · rintro ⟨hF, hOmega⟩
    apply (lifting_iff (toZero X)).mpr
    refine ⟨(HomotopicalAlgebra.fibration_iff _).mp
      ((isFibrant_iff_of_isTerminal (toZero X) zeroDiagramIsTerminal).mp hF), ?_⟩
    exact fun n => (zeroCorner_trivialFibration_iff n X).mpr
      ((isOmega_iff_stabilizationMappingArrows X).mp hOmega n)

/-- Actual native level fibrancy makes original K-local objects precisely original Omega spectra. -/
theorem lifting_toZero_iff_isOmega (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    generators.rlp (toZero X) ↔ X.IsOmega :=
  ⟨fun h => ((lifting_toZero_iff_fibrantOmega X).mp h).2,
    fun h => (lifting_toZero_iff_fibrantOmega X).mpr
      ⟨HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant X, h⟩⟩

/-- A genuine original Omega target makes every original cylinder source map a trivial fibration. -/
theorem stabilizationSource_mapping_trivialFibration
    (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (hX : X.IsOmega) :
    trivialFibrations PointedCGWH.{u, v}
      (WeightedEndVariance.pre (stabilizationCylinderSource n) X) := by
  have h := (zeroCorner_trivialFibration_iff n X).mpr
    ((isOmega_iff_stabilizationMappingArrows X).mp hX n)
  exact ((trivialFibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (PointedCGWH.NativeMappingZeroSource.cornerArrowIso (stabilizationCylinderSource n) X)).mp h

/-- A level fibration between actual original Omega objects has the full original K lifting. -/
theorem levelFibration_betweenOmega_hasLifting
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (hp : fibrations PointedCGWH.SequentialSpectrum.{u, v} p) (hX : X.IsOmega) (hY : Y.IsOmega) :
    generators.rlp p := by
  have hX' : (NativeK.generators StabilizationKAdapter.family).rlp (toZero X) := by
    simpa only [StabilizationKAdapter.generators_eq] using (lifting_toZero_iff_isOmega X).mpr hX
  have hY' : (NativeK.generators StabilizationKAdapter.family).rlp (toZero Y) := by
    simpa only [StabilizationKAdapter.generators_eq] using (lifting_toZero_iff_isOmega Y).mpr hY
  have h := NativeK.levelFibration_between_local_mem_right StabilizationKAdapter.family p hp hX' hY'
  simpa only [StabilizationKAdapter.generators_eq] using h

/-- Both K and level fibration classes agree on actual maps between original Omega objects. -/
theorem levelFibration_betweenOmega_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y) (hX : X.IsOmega) (hY : Y.IsOmega) :
    generators.rlp p ↔ fibrations PointedCGWH.SequentialSpectrum.{u, v} p :=
  ⟨fun h => ((lifting_iff p).mp h).1,
    fun h => levelFibration_betweenOmega_hasLifting p h hX hY⟩

/-- A K-right map whose caller-chosen fiber collapse satisfies Omega-target tests is a level
trivial fibration. Every original component is a trivial fibration, including degree zero
and the full path-component condition. -/
theorem chosenFiber_omegaTests_levelTrivialFibration
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (hp : generators.rlp p)
    (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)
    (hTests : NativeK.omegaTests StabilizationKAdapter.family c.snd) :
    trivialFibrations PointedCGWH.SequentialSpectrum.{u, v} p ∧
      ∀ n : ℕ, trivialFibrations PointedCGWH.{u, v} (levelMap p n) := by
  let s := StabilizationKAdapter.family.{u, v}
  have hpS : (NativeK.generators s).rlp p := by
    simpa only [StabilizationKAdapter.generators_eq] using hp
  have h := NativeK.chosenFiber_omegaTests_levelTrivialFibration s
    (fun a : PointedCGWH.Spectra.Sequential.Index.{u, v} => a.degree)
    (by rintro ⟨n⟩; rfl) (fun _ => Iso.refl _) p hpS c hc hTests
  refine ⟨h.1, fun n => ?_⟩
  exact h.2 (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n)

end PointedCGWH.SequentialSpectrum.StableK
