/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.InfiniteTailMaskedStableKeyPackage
import Code.Exact3D.InfiniteTailStableKeyPackageExample
import Code.Exact3D.FiniteWitnessPackageExample
import Code.Exact3D.GeneratedTableTailBridgeExample
import Code.Exact3D.StableKeyTailBridgeExample

open scoped BigOperators









namespace StatMech
namespace Exact3D
namespace InfiniteTailMaskedStableKeyPackageExample

open BoundedPolymerCase
open BoundedPolymerCase.StableKeyCertificateExample
open BoundedPolymerCase.StableKeyTailBridgeExample
open BoundedPolymerCase.GeneratedTableTailBridgeExample
open InfiniteTailStableKeyPackageExample
open InfiniteTailMaskedTableWitnessPackage



noncomputable def rawRowsZeroMaskedTablePackage {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey
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
    (by intro _ _; simp)
    (by intro _ _; simp [zeroSplit])
    (by simp)
    (by simp)



noncomputable def minimalCubicRowsZeroMaskedTablePackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic
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
    (by intro _ _; simp)
    (by intro _ _; simp [zeroSplit])
    (by simp)
    (by simp)



noncomputable def rawZeroOneRowsIndicatorMaskedTablePackage {d : ℕ}
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
  InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey
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
    (by intro _ _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)



noncomputable def minimalCubicZeroOneRowsIndicatorMaskedTablePackage
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
  InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic
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
    (by intro _ _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)


theorem rawRowsZeroMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroMaskedTablePackage (d := d) K).certificate.FiniteChecks :=
  (rawRowsZeroMaskedTablePackage (d := d) K).finiteChecks


theorem minimalCubicRowsZeroMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroMaskedTablePackage
      (d := d) K).certificate.FiniteChecks :=
  (minimalCubicRowsZeroMaskedTablePackage (d := d) K).finiteChecks


theorem rawZeroOneRowsIndicatorMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (rawZeroOneRowsIndicatorMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks



theorem minimalCubicZeroOneRowsIndicatorMaskedTablePackage_finiteChecks
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks


theorem rawRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroMaskedTablePackage
      (d := d) K).tableCertifiedTotalBound = 0 := by
  norm_num [rawRowsZeroMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]



theorem minimalCubicRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroMaskedTablePackage
      (d := d) K).tableCertifiedTotalBound = 0 := by
  norm_num [minimalCubicRowsZeroMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]



theorem rawZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [rawZeroOneRowsIndicatorMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]



theorem minimalCubicZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]



theorem rawZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [rawZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey])).finiteBound =
      2 :=
  rfl



theorem rawZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [rawZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [rawZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey, with_larger_finiteBound,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]



theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).finiteBound =
      2 :=
  rfl



theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic, with_larger_finiteBound,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]



theorem rawZeroOneRowsIndicatorMaskedTablePackage_relaxedPrefixBudget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_prefixTailBound
        (prefixTailBound' := 1) (by
          norm_num [rawZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) + 1 := by
  simp [rawZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey, with_larger_prefixTailBound,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]



theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedPrefixBudget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_prefixTailBound
        (prefixTailBound' := 1) (by
          norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) + 1 := by
  simp [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    with_larger_prefixTailBound, tableCertifiedTotalBound,
    tablePrefixBudget, tableFiniteBudget]



theorem rawZeroOneRowsIndicatorMaskedTablePackage_relaxedTailBudget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_tailBound
        (tailBound' := 1) (by
          norm_num [rawZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) + 1 := by
  simp [rawZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey, with_larger_tailBound,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]



theorem minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedTailBudget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_tailBound
        (tailBound' := 1) (by
          norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) + 1 := by
  simp [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic, with_larger_tailBound,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]



noncomputable def rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
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
  (rawZeroOneRowsIndicatorMaskedTablePackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 2) (tailBound' := 0)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffStableKey K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffStableKey K))
      (by norm_num)



theorem
    rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  simp [rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope,
    rawZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey,
    with_zero_tailEnvelope_and_budgets, with_tailEnvelope_and_budgets,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]

@[simp] theorem
    rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (rawZeroOneRowsIndicatorMaskedTablePackage
        (d := d) K support hsaturated).certificate :=
  rfl



theorem
    rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_tsum_le
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [← rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq
    (d := d) K support hsaturated]
  exact
    (rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



noncomputable def
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
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
  (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 2) (tailBound' := 0)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffMinimalCubicStableKey K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffMinimalCubicStableKey K))
      (by norm_num)



theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  simp [minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope,
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    with_zero_tailEnvelope_and_budgets, with_tailEnvelope_and_budgets,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]

@[simp] theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
        (d := d) K support hsaturated).certificate :=
  rfl



theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_tsum_le
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq
      (d := d) K support hsaturated]
  exact
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem rawRowsZeroMaskedTablePackage_tailTotalTsum_le_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroMaskedTablePackage (d := d) K).tailTotalTsum ≤ 0 := by
  rw [← rawRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero
    (d := d) K]
  exact
    (rawRowsZeroMaskedTablePackage
      (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound



theorem minimalCubicRowsZeroMaskedTablePackage_tailTotalTsum_le_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroMaskedTablePackage
      (d := d) K).tailTotalTsum ≤ 0 := by
  rw [← minimalCubicRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero
    (d := d) K]
  exact
    (minimalCubicRowsZeroMaskedTablePackage
      (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound



theorem rawZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← rawZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card
    (d := d) K support hsaturated]
  exact
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← minimalCubicZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card
    (d := d) K support hsaturated]
  exact
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound



theorem rawRowsZeroMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroMaskedTablePackage (d := d) K).tailRemainderSum = 0 := by
  let P := rawRowsZeroMaskedTablePackage (d := d) K
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem rawRowsZeroMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroMaskedTablePackage (d := d) K).tailTotalTsum =
      (rawRowsZeroMaskedTablePackage (d := d) K).tailPrefixSum := by
  let P := rawRowsZeroMaskedTablePackage (d := d) K
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem minimalCubicRowsZeroMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroMaskedTablePackage
      (d := d) K).tailRemainderSum = 0 := by
  let P := minimalCubicRowsZeroMaskedTablePackage (d := d) K
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem minimalCubicRowsZeroMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroMaskedTablePackage (d := d) K).tailTotalTsum =
      (minimalCubicRowsZeroMaskedTablePackage
        (d := d) K).tailPrefixSum := by
  let P := minimalCubicRowsZeroMaskedTablePackage (d := d) K
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem rawZeroOneRowsIndicatorMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := rawZeroOneRowsIndicatorMaskedTablePackage
    (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem rawZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (rawZeroOneRowsIndicatorMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := rawZeroOneRowsIndicatorMaskedTablePackage
    (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)



theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P :=
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)



theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P :=
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)

end InfiniteTailMaskedStableKeyPackageExample

end Exact3D
end StatMech
