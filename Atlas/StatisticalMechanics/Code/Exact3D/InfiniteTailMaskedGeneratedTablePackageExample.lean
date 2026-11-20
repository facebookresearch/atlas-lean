/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.InfiniteTailMaskedGeneratedTablePackage
import Code.Exact3D.FiniteWitnessPackageExample
import Code.Exact3D.GeneratedTableTailBridgeExample

open scoped BigOperators








namespace StatMech
namespace Exact3D
namespace InfiniteTailMaskedGeneratedTablePackageExample

open BoundedPolymerCase
open BoundedPolymerCase.GeneratedTableTailBridgeExample
open InfiniteTailMaskedTableWitnessPackage


noncomputable def generatedBoundedCaseMaskedTablePackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    InfiniteTailMaskedTableWitnessPackage
      (Case := FiniteCutoffCase d K)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailMaskedTableWitnessPackage.ofGeneratedIntervalTableFiniteCutoff
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
    (by intro _ _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)


noncomputable def generatedCubicClassMaskedTablePackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    InfiniteTailMaskedTableWitnessPackage
      (Case := CubicClass d K.radius K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailMaskedTableWitnessPackage.ofGeneratedCubicIntervalTableFiniteCutoff
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
    (by intro _ _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)


noncomputable def generatedStableKeyMaskedTablePackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailMaskedTableWitnessPackage.ofGeneratedStableKeyIntervalTableFiniteCutoff
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
    (by intro _ _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)



noncomputable def generatedMinimalCubicStableKeyMaskedTablePackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailMaskedTableWitnessPackage.ofGeneratedMinimalCubicStableKeyTableFiniteCutoff
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
    (by intro _ _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)


theorem generatedBoundedCaseMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedBoundedCaseMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedCubicClassMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedCubicClassMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedStableKeyMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedStableKeyMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks



theorem generatedMinimalCubicStableKeyMaskedTablePackage_finiteChecks
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedMinimalCubicStableKeyMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks



theorem generatedBoundedCaseMaskedTablePackage_budget_eq_card {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [generatedBoundedCaseMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofGeneratedIntervalTableFiniteCutoff,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]



theorem generatedBoundedCaseMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedBoundedCaseMaskedTablePackage_budget_eq_card]
  exact
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem generatedCubicClassMaskedTablePackage_budget_eq_card {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [generatedCubicClassMaskedTablePackage,
    ofGeneratedCubicIntervalTableFiniteCutoff,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]



theorem generatedCubicClassMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedCubicClassMaskedTablePackage_budget_eq_card]
  exact
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem generatedStableKeyMaskedTablePackage_budget_eq_card {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [generatedStableKeyMaskedTablePackage,
    ofGeneratedStableKeyIntervalTableFiniteCutoff,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]



theorem generatedStableKeyMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedStableKeyMaskedTablePackage_budget_eq_card]
  exact
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem generatedMinimalCubicStableKeyMaskedTablePackage_budget_eq_card
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [generatedMinimalCubicStableKeyMaskedTablePackage,
    ofGeneratedMinimalCubicStableKeyTableFiniteCutoff,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]



theorem generatedMinimalCubicStableKeyMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedMinimalCubicStableKeyMaskedTablePackage_budget_eq_card]
  exact
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem generatedBoundedCaseMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedBoundedCaseMaskedTablePackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem generatedBoundedCaseMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedBoundedCaseMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedBoundedCaseMaskedTablePackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem generatedCubicClassMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedCubicClassMaskedTablePackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem generatedCubicClassMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedCubicClassMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedCubicClassMaskedTablePackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem generatedStableKeyMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedStableKeyMaskedTablePackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem generatedStableKeyMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedStableKeyMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedStableKeyMaskedTablePackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem
    generatedMinimalCubicStableKeyMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P :=
    generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem
    generatedMinimalCubicStableKeyMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedMinimalCubicStableKeyMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P :=
    generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



noncomputable def generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    InfiniteTailMaskedTableWitnessPackage
      (Case := FiniteCutoffCase d K)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (generatedBoundedCaseMaskedTablePackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 2) (tailBound' := 0)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffCoordinate K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffCoordinate K))
      (by norm_num)



theorem generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  simp [generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope,
    generatedBoundedCaseMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofGeneratedIntervalTableFiniteCutoff,
    with_zero_tailEnvelope_and_budgets, with_tailEnvelope_and_budgets,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]

@[simp] theorem
    generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (generatedBoundedCaseMaskedTablePackage
        (d := d) K support hsaturated).certificate :=
  rfl



theorem generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_tsum_le
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [← generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_budget_eq
    (d := d) K support hsaturated]
  exact
    (generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



noncomputable def generatedCubicClassMaskedTablePackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    InfiniteTailMaskedTableWitnessPackage
      (Case := CubicClass d K.radius K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (generatedCubicClassMaskedTablePackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 2) (tailBound' := 0)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffCubicClass K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffCubicClass K))
      (by norm_num)



theorem generatedCubicClassMaskedTablePackage_replacedTailEnvelope_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  simp [generatedCubicClassMaskedTablePackage_replacedTailEnvelope,
    generatedCubicClassMaskedTablePackage,
    ofGeneratedCubicIntervalTableFiniteCutoff,
    with_zero_tailEnvelope_and_budgets, with_tailEnvelope_and_budgets,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]

@[simp] theorem
    generatedCubicClassMaskedTablePackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (generatedCubicClassMaskedTablePackage
        (d := d) K support hsaturated).certificate :=
  rfl



theorem generatedCubicClassMaskedTablePackage_replacedTailEnvelope_tsum_le
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [← generatedCubicClassMaskedTablePackage_replacedTailEnvelope_budget_eq
    (d := d) K support hsaturated]
  exact
    (generatedCubicClassMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



noncomputable def generatedStableKeyMaskedTablePackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (generatedStableKeyMaskedTablePackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 2) (tailBound' := 0)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffStableKey K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffStableKey K))
      (by norm_num)



theorem generatedStableKeyMaskedTablePackage_replacedTailEnvelope_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  simp [generatedStableKeyMaskedTablePackage_replacedTailEnvelope,
    generatedStableKeyMaskedTablePackage,
    ofGeneratedStableKeyIntervalTableFiniteCutoff,
    with_zero_tailEnvelope_and_budgets, with_tailEnvelope_and_budgets,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]

@[simp] theorem
    generatedStableKeyMaskedTablePackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (generatedStableKeyMaskedTablePackage
        (d := d) K support hsaturated).certificate :=
  rfl



theorem generatedStableKeyMaskedTablePackage_replacedTailEnvelope_tsum_le
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [← generatedStableKeyMaskedTablePackage_replacedTailEnvelope_budget_eq
    (d := d) K support hsaturated]
  exact
    (generatedStableKeyMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



noncomputable def
    generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (generatedMinimalCubicStableKeyMaskedTablePackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 2) (tailBound' := 0)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffMinimalCubicStableKey K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffMinimalCubicStableKey K))
      (by norm_num)



theorem
    generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  simp [generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope,
    generatedMinimalCubicStableKeyMaskedTablePackage,
    ofGeneratedMinimalCubicStableKeyTableFiniteCutoff,
    with_zero_tailEnvelope_and_budgets, with_tailEnvelope_and_budgets,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]

@[simp] theorem
    generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (generatedMinimalCubicStableKeyMaskedTablePackage
        (d := d) K support hsaturated).certificate :=
  rfl



theorem
    generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_tsum_le
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_budget_eq
      (d := d) K support hsaturated]
  exact
    (generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound

end InfiniteTailMaskedGeneratedTablePackageExample

end Exact3D
end StatMech
