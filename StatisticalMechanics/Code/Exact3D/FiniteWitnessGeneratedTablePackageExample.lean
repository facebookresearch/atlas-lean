/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FiniteWitnessGeneratedTablePackage
import Code.Exact3D.FiniteWitnessPackageExample
import Code.Exact3D.GeneratedTableTailBridgeExample

open scoped BigOperators










namespace StatMech
namespace Exact3D
namespace FiniteWitnessGeneratedTablePackageExample

open BoundedPolymerCase
open BoundedPolymerCase.GeneratedTableTailBridgeExample



noncomputable def generatedBoundedCaseIndicatorPackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    FiniteWitnessPackage (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  FiniteWitnessPackage.ofGeneratedIntervalTableFiniteCutoff
    (finiteBound := (1 : ℝ)) (tailEnvelopeBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support (classifyFiniteCutoffCoordinate K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffCoordinate K))
    support ∅
    (fun _ => (0 : ℝ))
    (by simp)
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffCoordinate K) hsaturated)
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffCoordinate K))
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffCoordinate K))
    (fun _ => rfl)
    (fun c => zeroOneInterval_memR_keyImageIndicator support
      (classifyFiniteCutoffCoordinate K) c)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffCoordinate K))
    (by simp)


noncomputable def generatedCubicClassIndicatorPackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    FiniteWitnessPackage (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  FiniteWitnessPackage.ofGeneratedCubicIntervalTableFiniteCutoff
    (finiteBound := (1 : ℝ)) (tailEnvelopeBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support (classifyFiniteCutoffCubicClass K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffCubicClass K))
    support ∅
    (fun _ => (0 : ℝ))
    (by simp)
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffCubicClass K) hsaturated)
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffCubicClass K))
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffCubicClass K))
    (fun _ => rfl)
    (fun q => zeroOneInterval_memR_keyImageIndicator support
      (classifyFiniteCutoffCubicClass K) q)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffCubicClass K))
    (by simp)



noncomputable def generatedStableKeyIndicatorPackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    FiniteWitnessPackage (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  FiniteWitnessPackage.ofGeneratedStableKeyIntervalTableFiniteCutoff
    (finiteBound := (1 : ℝ)) (tailEnvelopeBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support (classifyFiniteCutoffStableKey K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffStableKey K))
    support ∅
    (fun _ => (0 : ℝ))
    (by simp)
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffStableKey K) hsaturated)
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffStableKey K))
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffStableKey K))
    (fun _ => rfl)
    (fun k _hk =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffStableKey K) k)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffStableKey K))
    (by simp)



noncomputable def generatedMinimalCubicStableKeyIndicatorPackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    FiniteWitnessPackage (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  FiniteWitnessPackage.ofGeneratedMinimalCubicStableKeyTableFiniteCutoff
    (finiteBound := (1 : ℝ)) (tailEnvelopeBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffMinimalCubicStableKey K))
    support ∅
    (fun _ => (0 : ℝ))
    (by simp)
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffMinimalCubicStableKey K) hsaturated)
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (keyImageIndicatorSplit_additive support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (fun _ => rfl)
    (fun k _hk =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffMinimalCubicStableKey K) k)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (by simp)



theorem generatedBoundedCaseIndicatorPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    RGCertificate.FiniteChecks
      ((generatedBoundedCaseIndicatorPackage
        (d := d) K support hsaturated).certificate) :=
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).finiteChecks



theorem generatedCubicClassIndicatorPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    RGCertificate.FiniteChecks
      ((generatedCubicClassIndicatorPackage
        (d := d) K support hsaturated).certificate) :=
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).finiteChecks



theorem generatedStableKeyIndicatorPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    RGCertificate.FiniteChecks
      ((generatedStableKeyIndicatorPackage
        (d := d) K support hsaturated).certificate) :=
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).finiteChecks



theorem generatedMinimalCubicStableKeyIndicatorPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    RGCertificate.FiniteChecks
      ((generatedMinimalCubicStableKeyIndicatorPackage
        (d := d) K support hsaturated).certificate) :=
  (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedBoundedCaseIndicatorPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedBoundedCaseIndicatorPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedBoundedCaseIndicatorPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedBoundedCaseIndicatorPackage
    (d := d) K support hsaturated).tailBounds


theorem generatedBoundedCaseIndicatorPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedBoundedCaseIndicatorPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem generatedBoundedCaseIndicatorPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedBoundedCaseIndicatorPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem generatedBoundedCaseIndicatorPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedBoundedCaseIndicatorPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedBoundedCaseIndicatorPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedBoundedCaseIndicatorPackage
    (d := d) K support hsaturated).orbitEntry


theorem generatedCubicClassIndicatorPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedCubicClassIndicatorPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedCubicClassIndicatorPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedCubicClassIndicatorPackage
    (d := d) K support hsaturated).tailBounds


theorem generatedCubicClassIndicatorPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedCubicClassIndicatorPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem generatedCubicClassIndicatorPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedCubicClassIndicatorPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem generatedCubicClassIndicatorPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedCubicClassIndicatorPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedCubicClassIndicatorPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedCubicClassIndicatorPackage
    (d := d) K support hsaturated).orbitEntry


theorem generatedStableKeyIndicatorPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedStableKeyIndicatorPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedStableKeyIndicatorPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedStableKeyIndicatorPackage
    (d := d) K support hsaturated).tailBounds


theorem generatedStableKeyIndicatorPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedStableKeyIndicatorPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem generatedStableKeyIndicatorPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedStableKeyIndicatorPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem generatedStableKeyIndicatorPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedStableKeyIndicatorPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedStableKeyIndicatorPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedStableKeyIndicatorPackage
    (d := d) K support hsaturated).orbitEntry


theorem generatedMinimalCubicStableKeyIndicatorPackage_finiteCaseChecks
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedMinimalCubicStableKeyIndicatorPackage_tailBounds
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).tailBounds



theorem generatedMinimalCubicStableKeyIndicatorPackage_fixedPointEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).fixedPointEnclosure



theorem
    generatedMinimalCubicStableKeyIndicatorPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).linearizationEnclosure



theorem generatedMinimalCubicStableKeyIndicatorPackage_hyperbolicSplitting
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedMinimalCubicStableKeyIndicatorPackage_orbitEntry
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).orbitEntry



theorem generatedStableKeyIndicatorPackage_predictedExponent_eq_boundedCase
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
    (generatedStableKeyIndicatorPackage
      (d := d) K support hstable).certificate.predictedExponent =
      (generatedBoundedCaseIndicatorPackage
        (d := d) K support hbounded).certificate.predictedExponent := by
  rfl


theorem generatedBoundedCaseIndicatorPackage_tailPrefixSum_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).tailPrefixSum = 0 := by
  simp [generatedBoundedCaseIndicatorPackage,
    FiniteWitnessPackage.tailPrefixSum,
    FiniteWitnessPackage.ofGeneratedIntervalTableFiniteCutoff,
    finiteSupportCertificate_of_generatedIntervalTable_finiteCutoff,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem generatedBoundedCaseIndicatorPackage_tailBudget_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).tailBudget = (support.card : ℝ) := by
  simp [generatedBoundedCaseIndicatorPackage,
    FiniteWitnessPackage.tailBudget,
    FiniteWitnessPackage.ofGeneratedIntervalTableFiniteCutoff,
    finiteSupportCertificate_of_generatedIntervalTable_finiteCutoff,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem generatedBoundedCaseIndicatorPackage_tailCertifiedTotalBound_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).tailCertifiedTotalBound =
      (support.card : ℝ) := by
  rw [FiniteWitnessPackage.tailCertifiedTotalBound,
    generatedBoundedCaseIndicatorPackage_tailPrefixSum_eq K support hsaturated,
    generatedBoundedCaseIndicatorPackage_tailBudget_eq K support hsaturated]
  ring



theorem generatedBoundedCaseIndicatorPackage_tail_tsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (∑' a,
      (generatedBoundedCaseIndicatorPackage
        (d := d) K support hsaturated).tailCertificate.weight a) ≤
      (support.card : ℝ) := by
  rw [← generatedBoundedCaseIndicatorPackage_tailCertifiedTotalBound_eq
    K support hsaturated]
  exact (generatedBoundedCaseIndicatorPackage
    (d := d) K support hsaturated).tail_tsum_le_certifiedTotalBound



theorem generatedBoundedCaseIndicatorPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedBoundedCaseIndicatorPackage_tailCertifiedTotalBound_eq
    K support hsaturated]
  exact (generatedBoundedCaseIndicatorPackage
    (d := d) K support hsaturated).tailTotalTsum_le_certifiedTotalBound


theorem generatedCubicClassIndicatorPackage_tailPrefixSum_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).tailPrefixSum = 0 := by
  simp [generatedCubicClassIndicatorPackage,
    FiniteWitnessPackage.tailPrefixSum,
    FiniteWitnessPackage.ofGeneratedCubicIntervalTableFiniteCutoff,
    finiteSupportCertificate_of_generatedCubicIntervalTable_finiteCutoff,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem generatedCubicClassIndicatorPackage_tailBudget_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).tailBudget = (support.card : ℝ) := by
  simp [generatedCubicClassIndicatorPackage,
    FiniteWitnessPackage.tailBudget,
    FiniteWitnessPackage.ofGeneratedCubicIntervalTableFiniteCutoff,
    finiteSupportCertificate_of_generatedCubicIntervalTable_finiteCutoff,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem generatedCubicClassIndicatorPackage_tailCertifiedTotalBound_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).tailCertifiedTotalBound =
      (support.card : ℝ) := by
  rw [FiniteWitnessPackage.tailCertifiedTotalBound,
    generatedCubicClassIndicatorPackage_tailPrefixSum_eq K support hsaturated,
    generatedCubicClassIndicatorPackage_tailBudget_eq K support hsaturated]
  ring



theorem generatedCubicClassIndicatorPackage_tail_tsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (∑' a,
      (generatedCubicClassIndicatorPackage
        (d := d) K support hsaturated).tailCertificate.weight a) ≤
      (support.card : ℝ) := by
  rw [← generatedCubicClassIndicatorPackage_tailCertifiedTotalBound_eq
    K support hsaturated]
  exact (generatedCubicClassIndicatorPackage
    (d := d) K support hsaturated).tail_tsum_le_certifiedTotalBound



theorem generatedCubicClassIndicatorPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedCubicClassIndicatorPackage_tailCertifiedTotalBound_eq
    K support hsaturated]
  exact (generatedCubicClassIndicatorPackage
    (d := d) K support hsaturated).tailTotalTsum_le_certifiedTotalBound


theorem generatedStableKeyIndicatorPackage_tailPrefixSum_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).tailPrefixSum = 0 := by
  simp [generatedStableKeyIndicatorPackage,
    FiniteWitnessPackage.tailPrefixSum,
    FiniteWitnessPackage.ofGeneratedStableKeyIntervalTableFiniteCutoff,
    finiteSupportCertificate_of_generatedStableKeyIntervalTable_finiteCutoff,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem generatedStableKeyIndicatorPackage_tailBudget_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).tailBudget = (support.card : ℝ) := by
  simp [generatedStableKeyIndicatorPackage,
    FiniteWitnessPackage.tailBudget,
    FiniteWitnessPackage.ofGeneratedStableKeyIntervalTableFiniteCutoff,
    finiteSupportCertificate_of_generatedStableKeyIntervalTable_finiteCutoff,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem generatedStableKeyIndicatorPackage_tailCertifiedTotalBound_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).tailCertifiedTotalBound =
      (support.card : ℝ) := by
  rw [FiniteWitnessPackage.tailCertifiedTotalBound,
    generatedStableKeyIndicatorPackage_tailPrefixSum_eq K support hsaturated,
    generatedStableKeyIndicatorPackage_tailBudget_eq K support hsaturated]
  ring



theorem generatedStableKeyIndicatorPackage_tail_tsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (∑' a,
      (generatedStableKeyIndicatorPackage
        (d := d) K support hsaturated).tailCertificate.weight a) ≤
      (support.card : ℝ) := by
  rw [← generatedStableKeyIndicatorPackage_tailCertifiedTotalBound_eq
    K support hsaturated]
  exact (generatedStableKeyIndicatorPackage
    (d := d) K support hsaturated).tail_tsum_le_certifiedTotalBound



theorem generatedStableKeyIndicatorPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedStableKeyIndicatorPackage_tailCertifiedTotalBound_eq
    K support hsaturated]
  exact (generatedStableKeyIndicatorPackage
    (d := d) K support hsaturated).tailTotalTsum_le_certifiedTotalBound


theorem generatedMinimalCubicStableKeyIndicatorPackage_tailPrefixSum_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).tailPrefixSum = 0 := by
  simp [generatedMinimalCubicStableKeyIndicatorPackage,
    FiniteWitnessPackage.tailPrefixSum,
    FiniteWitnessPackage.ofGeneratedMinimalCubicStableKeyTableFiniteCutoff,
    finiteSupportCertificate_of_generatedMinimalCubicStableKeyTable_finiteCutoff,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem generatedMinimalCubicStableKeyIndicatorPackage_tailBudget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).tailBudget =
      (support.card : ℝ) := by
  simp [generatedMinimalCubicStableKeyIndicatorPackage,
    FiniteWitnessPackage.tailBudget,
    FiniteWitnessPackage.ofGeneratedMinimalCubicStableKeyTableFiniteCutoff,
    finiteSupportCertificate_of_generatedMinimalCubicStableKeyTable_finiteCutoff,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem generatedMinimalCubicStableKeyIndicatorPackage_tailCertifiedTotalBound_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).tailCertifiedTotalBound =
      (support.card : ℝ) := by
  rw [FiniteWitnessPackage.tailCertifiedTotalBound,
    generatedMinimalCubicStableKeyIndicatorPackage_tailPrefixSum_eq
      K support hsaturated,
    generatedMinimalCubicStableKeyIndicatorPackage_tailBudget_eq
      K support hsaturated]
  ring



theorem generatedMinimalCubicStableKeyIndicatorPackage_tail_tsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (∑' a,
      (generatedMinimalCubicStableKeyIndicatorPackage
        (d := d) K support hsaturated).tailCertificate.weight a) ≤
      (support.card : ℝ) := by
  rw [← generatedMinimalCubicStableKeyIndicatorPackage_tailCertifiedTotalBound_eq
    K support hsaturated]
  exact (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).tail_tsum_le_certifiedTotalBound



theorem generatedMinimalCubicStableKeyIndicatorPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedMinimalCubicStableKeyIndicatorPackage_tailCertifiedTotalBound_eq
    K support hsaturated]
  exact (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).tailTotalTsum_le_certifiedTotalBound



theorem generatedBoundedCaseIndicatorPackage_rgToExponentBridge_of_bridge
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
      RGCertificate.RGToExponentBridge
        ((generatedBoundedCaseIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    RGCertificate.RGToExponentBridge
      ((generatedBoundedCaseIndicatorPackage
        (d := d) K support hsaturated).certificate)
      correlationLength :=
  hbridge



theorem generatedStableKeyIndicatorPackage_rgToExponentBridge_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((generatedStableKeyIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    RGCertificate.RGToExponentBridge
      ((generatedStableKeyIndicatorPackage
        (d := d) K support hsaturated).certificate)
      correlationLength :=
  hbridge



theorem generatedCubicClassIndicatorPackage_rgToExponentBridge_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((generatedCubicClassIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    RGCertificate.RGToExponentBridge
      ((generatedCubicClassIndicatorPackage
        (d := d) K support hsaturated).certificate)
      correlationLength :=
  hbridge



theorem
    generatedMinimalCubicStableKeyIndicatorPackage_rgToExponentBridge_of_bridge
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
      RGCertificate.RGToExponentBridge
        ((generatedMinimalCubicStableKeyIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    RGCertificate.RGToExponentBridge
      ((generatedMinimalCubicStableKeyIndicatorPackage
        (d := d) K support hsaturated).certificate)
      correlationLength :=
  hbridge



theorem generatedBoundedCaseIndicatorPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((generatedBoundedCaseIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    RGCertificate.Valid
      ((generatedBoundedCaseIndicatorPackage
        (d := d) K support hsaturated).certificate)
      correlationLength :=
  (generatedBoundedCaseIndicatorPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge



theorem generatedStableKeyIndicatorPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((generatedStableKeyIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    RGCertificate.Valid
      ((generatedStableKeyIndicatorPackage
        (d := d) K support hsaturated).certificate)
      correlationLength :=
  (generatedStableKeyIndicatorPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge



theorem generatedCubicClassIndicatorPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((generatedCubicClassIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    RGCertificate.Valid
      ((generatedCubicClassIndicatorPackage
        (d := d) K support hsaturated).certificate)
      correlationLength :=
  (generatedCubicClassIndicatorPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge



theorem generatedMinimalCubicStableKeyIndicatorPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((generatedMinimalCubicStableKeyIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    RGCertificate.Valid
      ((generatedMinimalCubicStableKeyIndicatorPackage
        (d := d) K support hsaturated).certificate)
      correlationLength :=
  (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge



theorem generatedBoundedCaseIndicatorPackage_hasCriticalNu_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((generatedBoundedCaseIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedBoundedCaseIndicatorPackage
        (d := d) K support hsaturated).certificate.predictedExponent := by
  exact FiniteWitnessPackage.hasCriticalNu_of_bridge
    (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated)
    hbridge



theorem generatedCubicClassIndicatorPackage_hasCriticalNu_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((generatedCubicClassIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedCubicClassIndicatorPackage
        (d := d) K support hsaturated).certificate.predictedExponent := by
  exact FiniteWitnessPackage.hasCriticalNu_of_bridge
    (generatedCubicClassIndicatorPackage (d := d) K support hsaturated)
    hbridge



theorem generatedStableKeyIndicatorPackage_hasCriticalNu_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((generatedStableKeyIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedStableKeyIndicatorPackage
        (d := d) K support hsaturated).certificate.predictedExponent := by
  exact FiniteWitnessPackage.hasCriticalNu_of_bridge
    (generatedStableKeyIndicatorPackage (d := d) K support hsaturated)
    hbridge



theorem generatedMinimalCubicStableKeyIndicatorPackage_hasCriticalNu_of_bridge
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
      RGCertificate.RGToExponentBridge
        ((generatedMinimalCubicStableKeyIndicatorPackage
          (d := d) K support hsaturated).certificate)
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedMinimalCubicStableKeyIndicatorPackage
        (d := d) K support hsaturated).certificate.predictedExponent := by
  exact FiniteWitnessPackage.hasCriticalNu_of_bridge
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated)
    hbridge



theorem generatedBoundedCaseIndicatorPackage_rgToExponentBridge_of_hasCriticalNu
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
        (generatedBoundedCaseIndicatorPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedBoundedCaseIndicatorPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν



theorem generatedBoundedCaseIndicatorPackage_valid_of_hasCriticalNu
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
        (generatedBoundedCaseIndicatorPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedBoundedCaseIndicatorPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (generatedBoundedCaseIndicatorPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν



theorem generatedCubicClassIndicatorPackage_rgToExponentBridge_of_hasCriticalNu
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
        (generatedCubicClassIndicatorPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedCubicClassIndicatorPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν



theorem generatedCubicClassIndicatorPackage_valid_of_hasCriticalNu
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
        (generatedCubicClassIndicatorPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedCubicClassIndicatorPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (generatedCubicClassIndicatorPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν



theorem generatedStableKeyIndicatorPackage_rgToExponentBridge_of_hasCriticalNu
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
        (generatedStableKeyIndicatorPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedStableKeyIndicatorPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν



theorem generatedStableKeyIndicatorPackage_valid_of_hasCriticalNu
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
        (generatedStableKeyIndicatorPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (generatedStableKeyIndicatorPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν



theorem
    generatedMinimalCubicStableKeyIndicatorPackage_rgToExponentBridge_of_hasCriticalNu
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
        (generatedMinimalCubicStableKeyIndicatorPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν



theorem generatedMinimalCubicStableKeyIndicatorPackage_valid_of_hasCriticalNu
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
        (generatedMinimalCubicStableKeyIndicatorPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedMinimalCubicStableKeyIndicatorPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (generatedMinimalCubicStableKeyIndicatorPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν

end FiniteWitnessGeneratedTablePackageExample
end Exact3D
end StatMech
