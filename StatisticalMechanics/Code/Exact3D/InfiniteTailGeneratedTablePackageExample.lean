/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.InfiniteTailGeneratedTablePackage
import Code.Exact3D.FiniteWitnessPackageExample
import Code.Exact3D.GeneratedTableTailBridgeExample

open scoped BigOperators








namespace StatMech
namespace Exact3D
namespace InfiniteTailGeneratedTablePackageExample

open BoundedPolymerCase
open BoundedPolymerCase.GeneratedTableTailBridgeExample
open InfiniteTailTableWitnessPackage



noncomputable def generatedBoundedCaseInfiniteTailPackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    InfiniteTailTableWitnessPackage
      (Case := FiniteCutoffCase d K)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailTableWitnessPackage.ofGeneratedIntervalTableFiniteCutoff
    (finiteBound := (1 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support (classifyFiniteCutoffCoordinate K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffCoordinate K))
    support (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffCoordinate K))
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffCoordinate K))
    (fun _ => rfl)
    (fun c => zeroOneInterval_memR_keyImageIndicator support
      (classifyFiniteCutoffCoordinate K) c)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffCoordinate K))
    (zero_tailEnvelope_sum_le support)
    (keyImageIndicatorSplit_finite_zero_off_saturated_support support
      (classifyFiniteCutoffCoordinate K) hsaturated)
    (by intro _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)


noncomputable def generatedCubicClassInfiniteTailPackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    InfiniteTailTableWitnessPackage
      (Case := CubicClass d K.radius K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailTableWitnessPackage.ofGeneratedCubicIntervalTableFiniteCutoff
    (finiteBound := (1 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support (classifyFiniteCutoffCubicClass K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffCubicClass K))
    support (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffCubicClass K))
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffCubicClass K))
    (fun _ => rfl)
    (fun q => zeroOneInterval_memR_keyImageIndicator support
      (classifyFiniteCutoffCubicClass K) q)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffCubicClass K))
    (zero_tailEnvelope_sum_le support)
    (keyImageIndicatorSplit_finite_zero_off_saturated_support support
      (classifyFiniteCutoffCubicClass K) hsaturated)
    (by intro _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)


noncomputable def generatedStableKeyInfiniteTailPackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    InfiniteTailTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailTableWitnessPackage.ofGeneratedStableKeyIntervalTableFiniteCutoff
    (finiteBound := (1 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support (classifyFiniteCutoffStableKey K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffStableKey K))
    support (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffStableKey K))
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffStableKey K))
    (fun _ => rfl)
    (fun k _hk => zeroOneInterval_memR_keyImageIndicator support
      (classifyFiniteCutoffStableKey K) k)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffStableKey K))
    (zero_tailEnvelope_sum_le support)
    (keyImageIndicatorSplit_finite_zero_off_saturated_support support
      (classifyFiniteCutoffStableKey K) hsaturated)
    (by intro _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)



noncomputable def generatedMinimalCubicStableKeyInfiniteTailPackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    InfiniteTailTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailTableWitnessPackage.ofGeneratedMinimalCubicStableKeyTableFiniteCutoff
    (finiteBound := (1 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffMinimalCubicStableKey K))
    support (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (keyImageIndicatorSplit_additive support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (fun _ => rfl)
    (fun k _hk => zeroOneInterval_memR_keyImageIndicator support
      (classifyFiniteCutoffMinimalCubicStableKey K) k)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (zero_tailEnvelope_sum_le support)
    (keyImageIndicatorSplit_finite_zero_off_saturated_support support
      (classifyFiniteCutoffMinimalCubicStableKey K) hsaturated)
    (by intro _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)


theorem generatedBoundedCaseInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedCubicClassInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedStableKeyInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_finiteChecks
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedBoundedCaseInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedBoundedCaseInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds


theorem generatedBoundedCaseInfiniteTailPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem generatedBoundedCaseInfiniteTailPackage_linearizationEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem generatedBoundedCaseInfiniteTailPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedBoundedCaseInfiniteTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry


theorem generatedCubicClassInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedCubicClassInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds


theorem generatedCubicClassInfiniteTailPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem generatedCubicClassInfiniteTailPackage_linearizationEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem generatedCubicClassInfiniteTailPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedCubicClassInfiniteTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry


theorem generatedStableKeyInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedStableKeyInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds


theorem generatedStableKeyInfiniteTailPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem generatedStableKeyInfiniteTailPackage_linearizationEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem generatedStableKeyInfiniteTailPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedStableKeyInfiniteTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_finiteCaseChecks
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_tailBounds
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds



theorem generatedMinimalCubicStableKeyInfiniteTailPackage_fixedPointEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_hyperbolicSplitting
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_orbitEntry
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry



theorem generatedStableKeyInfiniteTailPackage_predictedExponent_eq_boundedCase
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hstable :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (hbounded :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hstable).certificate.predictedExponent =
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hbounded).certificate.predictedExponent := by
  rfl



theorem generatedBoundedCaseInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [generatedBoundedCaseInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]



theorem generatedCubicClassInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [generatedCubicClassInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedCubicIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]



theorem generatedStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [generatedStableKeyInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedStableKeyIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [generatedMinimalCubicStableKeyInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedMinimalCubicStableKeyTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]



theorem generatedBoundedCaseInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [generatedBoundedCaseInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem generatedCubicClassInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [generatedCubicClassInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedCubicIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem generatedStableKeyInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [generatedStableKeyInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedStableKeyIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem generatedMinimalCubicStableKeyInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [generatedMinimalCubicStableKeyInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedMinimalCubicStableKeyTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem generatedBoundedCaseInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem generatedBoundedCaseInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem generatedCubicClassInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem generatedCubicClassInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem generatedStableKeyInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem generatedStableKeyInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P :=
    generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P :=
    generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem generatedBoundedCaseInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    ((generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedBoundedCaseInfiniteTailPackage,
            ofGeneratedIntervalTableFiniteCutoff])).finiteBound =
      2 :=
  rfl



theorem generatedBoundedCaseInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    ((generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedBoundedCaseInfiniteTailPackage,
            ofGeneratedIntervalTableFiniteCutoff])).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [generatedBoundedCaseInfiniteTailPackage,
    ofGeneratedIntervalTableFiniteCutoff,
    with_larger_finiteBound, tableCertifiedTotalBound]



theorem generatedCubicClassInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    ((generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedCubicClassInfiniteTailPackage,
            ofGeneratedCubicIntervalTableFiniteCutoff])).finiteBound =
      2 :=
  rfl



theorem generatedCubicClassInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    ((generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedCubicClassInfiniteTailPackage,
            ofGeneratedCubicIntervalTableFiniteCutoff])).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [generatedCubicClassInfiniteTailPackage,
    ofGeneratedCubicIntervalTableFiniteCutoff,
    with_larger_finiteBound, tableCertifiedTotalBound]



theorem generatedStableKeyInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedStableKeyInfiniteTailPackage,
            ofGeneratedStableKeyIntervalTableFiniteCutoff])).finiteBound =
      2 :=
  rfl


theorem generatedStableKeyInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedStableKeyInfiniteTailPackage,
            ofGeneratedStableKeyIntervalTableFiniteCutoff])).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [generatedStableKeyInfiniteTailPackage,
    ofGeneratedStableKeyIntervalTableFiniteCutoff,
    with_larger_finiteBound, tableCertifiedTotalBound]



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedMinimalCubicStableKeyInfiniteTailPackage,
            ofGeneratedMinimalCubicStableKeyTableFiniteCutoff])).finiteBound =
      2 :=
  rfl



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedMinimalCubicStableKeyInfiniteTailPackage,
            ofGeneratedMinimalCubicStableKeyTableFiniteCutoff]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [generatedMinimalCubicStableKeyInfiniteTailPackage,
    ofGeneratedMinimalCubicStableKeyTableFiniteCutoff,
    with_larger_finiteBound, tableCertifiedTotalBound]



noncomputable def generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    InfiniteTailTableWitnessPackage
      (Case := FiniteCutoffCase d K)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 1) (tailBound' := 1)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffCoordinate K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffCoordinate K))
      (by norm_num)



theorem
    generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  rw [generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope]
  rw [with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound]
  change (support.card : ℝ) * (1 : ℝ) + 1 + 1 =
    (support.card : ℝ) + 2
  ring



theorem
    generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
      K support hsaturated]
  exact
    (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound

@[simp] theorem
    generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).certificate :=
  rfl



theorem
    generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hbridge :
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge



theorem generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_valid
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hvalid :
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).certificate.Valid
        correlationLength) :
    (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.Valid
        correlationLength := by
  simpa using hvalid



theorem
    generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedBoundedCaseInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope
        (d := d) K support hsaturated).certificate.predictedExponent := by
  simpa using hν



noncomputable def generatedCubicClassInfiniteTailPackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    InfiniteTailTableWitnessPackage
      (Case := CubicClass d K.radius K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 1) (tailBound' := 1)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffCubicClass K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffCubicClass K))
      (by norm_num)



theorem
    generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  rw [generatedCubicClassInfiniteTailPackage_replacedTailEnvelope]
  rw [with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound]
  change (support.card : ℝ) * (1 : ℝ) + 1 + 1 =
    (support.card : ℝ) + 2
  ring



theorem
    generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
      K support hsaturated]
  exact
    (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound

@[simp] theorem
    generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).certificate :=
  rfl



theorem
    generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hbridge :
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge



theorem generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_valid
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hvalid :
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).certificate.Valid
        correlationLength) :
    (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.Valid
        correlationLength := by
  simpa using hvalid



theorem
    generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedCubicClassInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope
        (d := d) K support hsaturated).certificate.predictedExponent := by
  simpa using hν



noncomputable def
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    InfiniteTailTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 1) (tailBound' := 1)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffMinimalCubicStableKey K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffMinimalCubicStableKey K))
      (by norm_num)



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  rw [generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope]
  rw [with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound]
  change (support.card : ℝ) * (1 : ℝ) + 1 + 1 =
    (support.card : ℝ) + 2
  ring



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
      K support hsaturated]
  exact
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound

@[simp] theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate :=
  rfl



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hbridge :
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_valid
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hvalid :
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.Valid
        correlationLength) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.Valid
        correlationLength := by
  simpa using hvalid



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedMinimalCubicStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
        (d := d) K support hsaturated).certificate.predictedExponent := by
  simpa using hν






noncomputable def generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    InfiniteTailTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 1) (tailBound' := 1)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffStableKey K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffStableKey K))
      (by norm_num)



theorem
    generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  rw [generatedStableKeyInfiniteTailPackage_replacedTailEnvelope]
  rw [with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound]
  change (support.card : ℝ) * (1 : ℝ) + 1 + 1 =
    (support.card : ℝ) + 2
  ring



theorem generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
      K support hsaturated]
  exact
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound

@[simp] theorem
    generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate :=
  rfl



theorem
    generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hbridge :
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge



theorem generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_valid
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hvalid :
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.Valid
        correlationLength) :
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.Valid
        correlationLength := by
  simpa using hvalid



theorem
    generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
        (d := d) K support hsaturated).certificate.predictedExponent := by
  simpa using hν



theorem generatedBoundedCaseInfiniteTailPackage_rgToExponentBridge_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  hbridge



theorem generatedCubicClassInfiniteTailPackage_rgToExponentBridge_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  hbridge



theorem generatedStableKeyInfiniteTailPackage_rgToExponentBridge_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  hbridge



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_rgToExponentBridge_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  hbridge



theorem generatedBoundedCaseInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge



theorem generatedBoundedCaseInfiniteTailPackage_hasCriticalNu_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge



theorem generatedCubicClassInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge



theorem generatedCubicClassInfiniteTailPackage_hasCriticalNu_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge



theorem generatedStableKeyInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge



theorem generatedStableKeyInfiniteTailPackage_hasCriticalNu_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge



theorem generatedMinimalCubicStableKeyInfiniteTailPackage_valid_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge



theorem generatedMinimalCubicStableKeyInfiniteTailPackage_hasCriticalNu_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge



theorem generatedBoundedCaseInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedBoundedCaseInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν



theorem generatedBoundedCaseInfiniteTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedBoundedCaseInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν



theorem generatedCubicClassInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedCubicClassInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν



theorem generatedCubicClassInfiniteTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedCubicClassInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν



theorem generatedStableKeyInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν



theorem generatedStableKeyInfiniteTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν



theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedMinimalCubicStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν



theorem generatedMinimalCubicStableKeyInfiniteTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedMinimalCubicStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν

end InfiniteTailGeneratedTablePackageExample

end Exact3D
end StatMech
