/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.InfiniteTailStableKeyPackage
import Code.Exact3D.FiniteWitnessPackageExample
import Code.Exact3D.StableKeyTailBridgeExample
import Code.Exact3D.GeneratedTableTailBridgeExample

open scoped BigOperators









namespace StatMech
namespace Exact3D
namespace InfiniteTailStableKeyPackageExample

open BoundedPolymerCase
open BoundedPolymerCase.StableKeyCertificateExample
open BoundedPolymerCase.StableKeyTailBridgeExample
open BoundedPolymerCase.GeneratedTableTailBridgeExample
open InfiniteTailTableWitnessPackage


def zeroOneRowOfKey {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    StableKeyIntervalRow maxDegree maxRange :=
  StableKeyIntervalRow.ofKey (fun _ => zeroOneInterval) k



theorem mem_rowKeyFinset_map_zeroOneRowOfKey {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset (s.toList.map zeroOneRowOfKey) ↔
      k ∈ s := by
  classical
  simpa [zeroOneRowOfKey] using
    StableKeyIntervalRow.mem_keyFinset_map_ofKeyInterval
      s (fun _ => zeroOneInterval) k


noncomputable def rawZeroOneRows (d R maxDegree maxRange : ℕ) :
    List (StableKeyIntervalRow maxDegree maxRange) :=
  StableKeyIntervalRow.rowsOfKeys
    ((exhaustiveTable d R maxDegree maxRange).image stableKey)
    (fun _ => zeroOneInterval)


noncomputable def minimalCubicZeroOneRows (d R maxDegree maxRange : ℕ) :
    List (StableKeyIntervalRow maxDegree maxRange) :=
  StableKeyIntervalRow.rowsOfKeys
    ((exhaustiveCubicClassTable d R maxDegree maxRange).image
      minimalCubicStableKey)
    (fun _ => zeroOneInterval)



theorem rawZeroOneRows_exactKeySet (d R maxDegree maxRange : ℕ) :
    StableKeyIntervalRow.ExactKeySet
      (rawZeroOneRows d R maxDegree maxRange)
      ((exhaustiveTable d R maxDegree maxRange).image stableKey) := by
  simpa [rawZeroOneRows] using
    StableKeyIntervalRow.exactKeySet_rowsOfKeys
      ((exhaustiveTable d R maxDegree maxRange).image stableKey)
      (fun _ => zeroOneInterval)



theorem minimalCubicZeroOneRows_exactKeySet
    (d R maxDegree maxRange : ℕ) :
    StableKeyIntervalRow.ExactKeySet
      (minimalCubicZeroOneRows d R maxDegree maxRange)
      ((exhaustiveCubicClassTable d R maxDegree maxRange).image
        minimalCubicStableKey) := by
  simpa [minimalCubicZeroOneRows] using
    StableKeyIntervalRow.exactKeySet_rowsOfKeys
      ((exhaustiveCubicClassTable d R maxDegree maxRange).image
        minimalCubicStableKey)
      (fun _ => zeroOneInterval)


theorem rawZeroOneRows_cover (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    stableKey c ∈ stableKeyIntervalRowKeyFinset
      (rawZeroOneRows d R maxDegree maxRange) := by
  classical
  rw [rawZeroOneRows]
  exact
    (StableKeyIntervalRow.mem_keyFinset_rowsOfKeys _
      _ (stableKey c)).2
    (Finset.mem_image.mpr
      ⟨c, exhaustiveTable_covers d R maxDegree maxRange c, rfl⟩)


theorem minimalCubicZeroOneRows_cover (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset
      (minimalCubicZeroOneRows d R maxDegree maxRange) := by
  classical
  rw [minimalCubicZeroOneRows]
  exact
    (StableKeyIntervalRow.mem_keyFinset_rowsOfKeys _
      _
      (classifyByMinimalCubicStableKey c)).2
      (Finset.mem_image.mpr
        ⟨cubicClass c, exhaustiveCubicClassTable_covers
          d R maxDegree maxRange c, rfl⟩)


theorem rawZeroOneRows_row_sound_keyImageIndicator {d : ℕ}
    (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K))
    (row : StableKeyIntervalRow K.maxDegree K.maxRange)
    (hrow : row ∈ rawZeroOneRows d K.radius K.maxDegree K.maxRange) :
    row.interval.MemR
      (keyImageIndicator support (classifyFiniteCutoffStableKey K)
        row.key.toKey) := by
  exact StableKeyIntervalRow.memR_of_mem_rowsOfKeys
    ((exhaustiveTable d K.radius K.maxDegree K.maxRange).image stableKey)
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffStableKey K))
    (fun k _ =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffStableKey K) k)
    (by simpa [rawZeroOneRows] using hrow)



theorem minimalCubicZeroOneRows_row_sound_keyImageIndicator {d : ℕ}
    (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K))
    (row : StableKeyIntervalRow K.maxDegree K.maxRange)
    (hrow : row ∈ minimalCubicZeroOneRows d K.radius K.maxDegree K.maxRange) :
    row.interval.MemR
      (keyImageIndicator support
        (classifyFiniteCutoffMinimalCubicStableKey K) row.key.toKey) := by
  exact StableKeyIntervalRow.memR_of_mem_rowsOfKeys
    ((exhaustiveCubicClassTable d K.radius K.maxDegree K.maxRange).image
      minimalCubicStableKey)
    (fun _ => zeroOneInterval)
    (keyImageIndicator support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (fun k _ =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffMinimalCubicStableKey K) k)
    (by simpa [minimalCubicZeroOneRows] using hrow)


theorem rawZeroOneRows_row_upper_one (d R maxDegree maxRange : ℕ)
    (row : StableKeyIntervalRow maxDegree maxRange)
    (hrow : row ∈ rawZeroOneRows d R maxDegree maxRange) :
    ((row.interval.upper : ℚ) : ℝ) ≤ 1 := by
  exact StableKeyIntervalRow.upper_le_of_mem_rowsOfKeys
    ((exhaustiveTable d R maxDegree maxRange).image stableKey)
    (fun _ => zeroOneInterval)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (by simpa [rawZeroOneRows] using hrow)


theorem minimalCubicZeroOneRows_row_upper_one
    (d R maxDegree maxRange : ℕ)
    (row : StableKeyIntervalRow maxDegree maxRange)
    (hrow : row ∈ minimalCubicZeroOneRows d R maxDegree maxRange) :
    ((row.interval.upper : ℚ) : ℝ) ≤ 1 := by
  exact StableKeyIntervalRow.upper_le_of_mem_rowsOfKeys
    ((exhaustiveCubicClassTable d R maxDegree maxRange).image
      minimalCubicStableKey)
    (fun _ => zeroOneInterval)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (by simpa [minimalCubicZeroOneRows] using hrow)



noncomputable def rawRowsZeroInfiniteTailPackage {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    InfiniteTailTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey
    (finiteBound := (0 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (zeroSplit (d := d) K)
    (rawRows d K.radius K.maxDegree K.maxRange)
    zeroInterval (fun _ => (0 : ℝ)) ∅
    (fun _ => (0 : ℝ))
    (zeroSplit_total_nonneg K)
    (zeroSplit_additive K)
    (rawRows_cover d K.radius K.maxDegree K.maxRange)
    (fun _ => rfl)
    (rawRows_row_sound d K.radius K.maxDegree K.maxRange)
    (rawRows_row_upper_zero d K.radius K.maxDegree K.maxRange)
    (zeroSplit_tailEnvelopeOn K ∅)
    (by simp)
    (by intro _ _; rfl)
    (by intro _; simp)
    (by intro _ _; simp [zeroSplit])
    (by simp)
    (by simp)



noncomputable def rawZeroOneRowsIndicatorInfiniteTailPackage {d : ℕ}
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
  InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey
    (finiteBound := (1 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support (classifyFiniteCutoffStableKey K))
    (rawZeroOneRows d K.radius K.maxDegree K.maxRange)
    zeroOneInterval
    (keyImageIndicator support (classifyFiniteCutoffStableKey K))
    support (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffStableKey K))
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffStableKey K))
    (rawZeroOneRows_cover d K.radius K.maxDegree K.maxRange)
    (fun _ => rfl)
    (rawZeroOneRows_row_sound_keyImageIndicator K support)
    (rawZeroOneRows_row_upper_one d K.radius K.maxDegree K.maxRange)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffStableKey K))
    (zero_tailEnvelope_sum_le support)
    (keyImageIndicatorSplit_finite_zero_off_saturated_support support
      (classifyFiniteCutoffStableKey K) hsaturated)
    (by intro _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)



noncomputable def minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
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
  InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic
    (finiteBound := (1 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (minimalCubicZeroOneRows d K.radius K.maxDegree K.maxRange)
    zeroOneInterval
    (keyImageIndicator support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    support (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (keyImageIndicatorSplit_additive support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (minimalCubicZeroOneRows_cover d K.radius K.maxDegree K.maxRange)
    (fun _ => rfl)
    (minimalCubicZeroOneRows_row_sound_keyImageIndicator K support)
    (minimalCubicZeroOneRows_row_upper_one
      d K.radius K.maxDegree K.maxRange)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (zero_tailEnvelope_sum_le support)
    (keyImageIndicatorSplit_finite_zero_off_saturated_support support
      (classifyFiniteCutoffMinimalCubicStableKey K) hsaturated)
    (by intro _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)



noncomputable def minimalCubicRowsZeroInfiniteTailPackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    InfiniteTailTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic
    (finiteBound := (0 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (zeroSplit (d := d) K)
    (minimalCubicRows d K.radius K.maxDegree K.maxRange)
    zeroInterval (fun _ => (0 : ℝ)) ∅
    (fun _ => (0 : ℝ))
    (zeroSplit_total_nonneg K)
    (zeroSplit_additive K)
    (minimalCubicRows_cover d K.radius K.maxDegree K.maxRange)
    (fun _ => rfl)
    (minimalCubicRows_row_sound d K.radius K.maxDegree K.maxRange)
    (minimalCubicRows_row_upper_zero d K.radius K.maxDegree K.maxRange)
    (zeroSplit_tailEnvelopeOn K ∅)
    (by simp)
    (by intro _ _; rfl)
    (by intro _; simp)
    (by intro _ _; simp [zeroSplit])
    (by simp)
    (by simp)



theorem rawRowsZeroInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.FiniteChecks :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).finiteChecks


theorem rawRowsZeroInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.FiniteCaseChecks :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).finiteCaseChecks


theorem rawRowsZeroInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.TailBounds :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).tailBounds



theorem rawRowsZeroInfiniteTailPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.FixedPointEnclosure :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).fixedPointEnclosure



theorem rawRowsZeroInfiniteTailPackage_linearizationEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.LinearizationEnclosure :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).linearizationEnclosure


theorem rawRowsZeroInfiniteTailPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.HyperbolicSplitting :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).hyperbolicSplitting


theorem rawRowsZeroInfiniteTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.OrbitEntry :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).orbitEntry


theorem minimalCubicRowsZeroInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.FiniteChecks :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).finiteChecks



theorem minimalCubicRowsZeroInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.FiniteCaseChecks :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).finiteCaseChecks



theorem minimalCubicRowsZeroInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.TailBounds :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).tailBounds



theorem minimalCubicRowsZeroInfiniteTailPackage_fixedPointEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.FixedPointEnclosure :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).fixedPointEnclosure



theorem minimalCubicRowsZeroInfiniteTailPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.LinearizationEnclosure :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).linearizationEnclosure



theorem minimalCubicRowsZeroInfiniteTailPackage_hyperbolicSplitting
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.HyperbolicSplitting :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).hyperbolicSplitting



theorem minimalCubicRowsZeroInfiniteTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.OrbitEntry :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).orbitEntry



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks



theorem minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_finiteChecks
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_fixedPointEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_hyperbolicSplitting
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_orbitEntry
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_finiteCaseChecks
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks



theorem minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailBounds
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_fixedPointEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_hyperbolicSplitting
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting



theorem minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_orbitEntry
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry


theorem rawRowsZeroInfiniteTailPackage_tableCertifiedTotalBound_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).tableCertifiedTotalBound = 0 := by
  simp [rawRowsZeroInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]



theorem minimalCubicRowsZeroInfiniteTailPackage_tableCertifiedTotalBound_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).tableCertifiedTotalBound = 0 := by
  simp [minimalCubicRowsZeroInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [rawZeroOneRowsIndicatorInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]


theorem rawRowsZeroInfiniteTailPackage_tailTotalTsum_le_zero {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum ≤ 0 := by
  simpa [rawRowsZeroInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (rawRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound



theorem minimalCubicRowsZeroInfiniteTailPackage_tailTotalTsum_le_zero {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum
      ≤ 0 := by
  simpa [minimalCubicRowsZeroInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [rawZeroOneRowsIndicatorInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey,
    tableCertifiedTotalBound] using
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    tableCertifiedTotalBound] using
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem rawRowsZeroInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).tailRemainderSum = 0 := by
  let P := rawRowsZeroInfiniteTailPackage (d := d) K
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem rawRowsZeroInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum =
      (rawRowsZeroInfiniteTailPackage (d := d) K).tailPrefixSum := by
  let P := rawRowsZeroInfiniteTailPackage (d := d) K
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem minimalCubicRowsZeroInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).tailRemainderSum = 0 := by
  let P := minimalCubicRowsZeroInfiniteTailPackage (d := d) K
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem minimalCubicRowsZeroInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum =
      (minimalCubicRowsZeroInfiniteTailPackage
        (d := d) K).tailPrefixSum := by
  let P := minimalCubicRowsZeroInfiniteTailPackage (d := d) K
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (rawZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P :=
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P :=
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [rawZeroOneRowsIndicatorInfiniteTailPackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey])).finiteBound =
      2 :=
  rfl



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [rawZeroOneRowsIndicatorInfiniteTailPackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [rawZeroOneRowsIndicatorInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey, with_larger_finiteBound,
    tableCertifiedTotalBound]



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).finiteBound =
      2 :=
  rfl



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic, with_larger_finiteBound,
    tableCertifiedTotalBound]



noncomputable def
    rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope
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
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 1) (tailBound' := 1)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffStableKey K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffStableKey K))
      (by norm_num)



theorem
    rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  rw [rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope]
  rw [with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound]
  change (support.card : ℝ) * (1 : ℝ) + 1 + 1 =
    (support.card : ℝ) + 2
  ring



theorem
    rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
      K support hsaturated]
  exact
    (rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



noncomputable def
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope
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
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 1) (tailBound' := 1)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffMinimalCubicStableKey K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffMinimalCubicStableKey K))
      (by norm_num)



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  rw [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope]
  rw [with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound]
  change (support.card : ℝ) * (1 : ℝ) + 1 + 1 =
    (support.card : ℝ) + 2
  ring



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
      K support hsaturated]
  exact
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem rawRowsZeroInfiniteTailPackage_relaxedTailBound_tailBound_eq_one
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    ((rawRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [rawRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffStableKey])).tailBound =
      1 :=
  rfl



theorem rawRowsZeroInfiniteTailPackage_relaxedTailBound_tailTotalTsum_le_one
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    ((rawRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [rawRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffStableKey])).tailTotalTsum
      ≤ 1 := by
  simpa [rawRowsZeroInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey, tableCertifiedTotalBound] using
    (((rawRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [rawRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffStableKey])).tailTotalTsum_le_tableCertifiedTotalBound)



theorem minimalCubicRowsZeroInfiniteTailPackage_relaxedTailBound_tailBound_eq_one
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    ((minimalCubicRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [minimalCubicRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).tailBound =
      1 :=
  rfl



theorem
    minimalCubicRowsZeroInfiniteTailPackage_relaxedTailBound_tailTotalTsum_le_one
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    ((minimalCubicRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [minimalCubicRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).tailTotalTsum
      ≤ 1 := by
  simpa [minimalCubicRowsZeroInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    tableCertifiedTotalBound] using
    (((minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [minimalCubicRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffMinimalCubic]
      )).tailTotalTsum_le_tableCertifiedTotalBound)



noncomputable def rawRowsZeroInfiniteTailPackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    InfiniteTailTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 1) (tailBound' := 1)
      (zeroSplit_tailEnvelopeOn K ∅)
      (by norm_num)
      (zeroSplit_tailContribution_nonpos_off_support K ∅)
      (by norm_num)


theorem rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tableCertifiedTotalBound = 2 := by
  norm_num [rawRowsZeroInfiniteTailPackage_replacedTailEnvelope,
    rawRowsZeroInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey,
    tablePrefixBudget, tableFiniteBudget]


@[simp] theorem rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).certificate =
      (rawRowsZeroInfiniteTailPackage (d := d) K).certificate :=
  rfl



theorem rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_tsum_le_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tailTotalTsum ≤ 2 := by
  rw [←
    rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
      (d := d) K]
  exact
    (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound



noncomputable def minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    InfiniteTailTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (minimalCubicRowsZeroInfiniteTailPackage
    (d := d) K).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 1) (tailBound' := 1)
      (zeroSplit_tailEnvelopeOn K ∅)
      (by norm_num)
      (zeroSplit_tailContribution_nonpos_off_support K ∅)
      (by norm_num)



theorem minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tableCertifiedTotalBound = 2 := by
  norm_num [minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope,
    minimalCubicRowsZeroInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    tablePrefixBudget, tableFiniteBudget]



@[simp] theorem
    minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).certificate =
      (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate :=
  rfl



theorem minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_tsum_le_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tailTotalTsum ≤ 2 := by
  rw [←
    minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
      (d := d) K]
  exact
    (minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound



theorem rawRowsZeroInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (rawRowsZeroInfiniteTailPackage
        (d := d) K).certificate.RGToExponentBridge correlationLength) :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.Valid correlationLength :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).valid_of_bridge hbridge



theorem rawRowsZeroInfiniteTailPackage_hasCriticalNu_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (rawRowsZeroInfiniteTailPackage
        (d := d) K).certificate.RGToExponentBridge correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (rawRowsZeroInfiniteTailPackage
        (d := d) K).certificate.predictedExponent :=
  (rawRowsZeroInfiniteTailPackage
    (d := d) K).hasCriticalNu_of_bridge hbridge



theorem minimalCubicRowsZeroInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (minimalCubicRowsZeroInfiniteTailPackage
        (d := d) K).certificate.RGToExponentBridge correlationLength) :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.Valid correlationLength :=
  (minimalCubicRowsZeroInfiniteTailPackage
    (d := d) K).valid_of_bridge hbridge



theorem minimalCubicRowsZeroInfiniteTailPackage_hasCriticalNu_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (minimalCubicRowsZeroInfiniteTailPackage
        (d := d) K).certificate.RGToExponentBridge correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (minimalCubicRowsZeroInfiniteTailPackage
        (d := d) K).certificate.predictedExponent :=
  (minimalCubicRowsZeroInfiniteTailPackage
    (d := d) K).hasCriticalNu_of_bridge hbridge



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (rawZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_hasCriticalNu_of_bridge
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
      (rawZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (rawZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_valid_of_bridge
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
      (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge




theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_hasCriticalNu_of_bridge
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
      (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge



theorem rawRowsZeroInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (rawRowsZeroInfiniteTailPackage
          (d := d) K).certificate.predictedExponent) :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.RGToExponentBridge correlationLength :=
  (rawRowsZeroInfiniteTailPackage
    (d := d) K).rgToExponentBridge_of_hasCriticalNu hν



theorem rawRowsZeroInfiniteTailPackage_valid_of_hasCriticalNu {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (rawRowsZeroInfiniteTailPackage
          (d := d) K).certificate.predictedExponent) :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.Valid correlationLength :=
  (rawRowsZeroInfiniteTailPackage
    (d := d) K).valid_of_hasCriticalNu hν



theorem
    minimalCubicRowsZeroInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (minimalCubicRowsZeroInfiniteTailPackage
          (d := d) K).certificate.predictedExponent) :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.RGToExponentBridge correlationLength :=
  (minimalCubicRowsZeroInfiniteTailPackage
    (d := d) K).rgToExponentBridge_of_hasCriticalNu hν



theorem minimalCubicRowsZeroInfiniteTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (minimalCubicRowsZeroInfiniteTailPackage
          (d := d) K).certificate.predictedExponent) :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.Valid correlationLength :=
  (minimalCubicRowsZeroInfiniteTailPackage
    (d := d) K).valid_of_hasCriticalNu hν



theorem
    rawZeroOneRowsIndicatorInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
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
        (rawZeroOneRowsIndicatorInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν



theorem rawZeroOneRowsIndicatorInfiniteTailPackage_valid_of_hasCriticalNu
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
        (rawZeroOneRowsIndicatorInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
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
        (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν



theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_valid_of_hasCriticalNu
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
        (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν

end InfiniteTailStableKeyPackageExample

end Exact3D
end StatMech
