/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FiniteWitnessStableKeyPackage
import Code.Exact3D.FiniteWitnessPackageExample
import Code.Exact3D.StableKeyTailBridgeExample

open scoped BigOperators










namespace StatMech
namespace Exact3D
namespace FiniteWitnessStableKeyPackageExample

open BoundedPolymerCase
open BoundedPolymerCase.StableKeyCertificateExample
open BoundedPolymerCase.StableKeyTailBridgeExample



noncomputable def rawRowsIndicatorTailPackage {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    FiniteWitnessPackage (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  FiniteWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey
    (finiteBound := (1 : ℝ))
    (tailEnvelopeBound := (support.card : ℝ) * ((1 : ℝ) / 10))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (indicatorTailSplit (d := d) K support)
    (rawRows d K.radius K.maxDegree K.maxRange)
    zeroInterval (fun _ => (0 : ℝ)) support ∅
    (fun _ => (1 : ℝ) / 10)
    (by simp)
    (indicatorTailSplit_total_zero_off_support K support)
    (indicatorTailSplit_total_nonneg K support)
    (indicatorTailSplit_additive K support)
    (rawRows_cover d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_finiteContribution_eq_zero K support)
    (rawRows_row_sound d K.radius K.maxDegree K.maxRange)
    (rawRows_row_upper_one d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_tailEnvelopeOn K support)
    (by simp [Finset.sum_const, nsmul_eq_mul])



noncomputable def minimalCubicRowsIndicatorTailPackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    FiniteWitnessPackage (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  FiniteWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic
    (finiteBound := (1 : ℝ))
    (tailEnvelopeBound := (support.card : ℝ) * ((1 : ℝ) / 10))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (indicatorTailSplit (d := d) K support)
    (minimalCubicRows d K.radius K.maxDegree K.maxRange)
    zeroInterval (fun _ => (0 : ℝ)) support ∅
    (fun _ => (1 : ℝ) / 10)
    (by simp)
    (indicatorTailSplit_total_zero_off_support K support)
    (indicatorTailSplit_total_nonneg K support)
    (indicatorTailSplit_additive K support)
    (minimalCubicRows_cover d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_finiteContribution_eq_zero K support)
    (minimalCubicRows_row_sound d K.radius K.maxDegree K.maxRange)
    (minimalCubicRows_row_upper_one d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_tailEnvelopeOn K support)
    (by simp [Finset.sum_const, nsmul_eq_mul])


theorem rawRowsIndicatorTailPackage_finiteChecks {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (rawRowsIndicatorTailPackage (d := d) K support).certificate.FiniteChecks :=
  (rawRowsIndicatorTailPackage (d := d) K support).finiteChecks



theorem minimalCubicRowsIndicatorTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    RGCertificate.FiniteChecks
      ((minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate) :=
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).finiteChecks


theorem rawRowsIndicatorTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (rawRowsIndicatorTailPackage
      (d := d) K support).certificate.FiniteCaseChecks :=
  (rawRowsIndicatorTailPackage (d := d) K support).finiteCaseChecks


theorem rawRowsIndicatorTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (rawRowsIndicatorTailPackage
      (d := d) K support).certificate.TailBounds :=
  (rawRowsIndicatorTailPackage (d := d) K support).tailBounds


theorem rawRowsIndicatorTailPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (rawRowsIndicatorTailPackage
      (d := d) K support).certificate.FixedPointEnclosure :=
  (rawRowsIndicatorTailPackage (d := d) K support).fixedPointEnclosure


theorem rawRowsIndicatorTailPackage_linearizationEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (rawRowsIndicatorTailPackage
      (d := d) K support).certificate.LinearizationEnclosure :=
  (rawRowsIndicatorTailPackage (d := d) K support).linearizationEnclosure


theorem rawRowsIndicatorTailPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (rawRowsIndicatorTailPackage
      (d := d) K support).certificate.HyperbolicSplitting :=
  (rawRowsIndicatorTailPackage (d := d) K support).hyperbolicSplitting


theorem rawRowsIndicatorTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (rawRowsIndicatorTailPackage
      (d := d) K support).certificate.OrbitEntry :=
  (rawRowsIndicatorTailPackage (d := d) K support).orbitEntry


theorem minimalCubicRowsIndicatorTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (minimalCubicRowsIndicatorTailPackage
      (d := d) K support).certificate.FiniteCaseChecks :=
  (minimalCubicRowsIndicatorTailPackage
    (d := d) K support).finiteCaseChecks


theorem minimalCubicRowsIndicatorTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (minimalCubicRowsIndicatorTailPackage
      (d := d) K support).certificate.TailBounds :=
  (minimalCubicRowsIndicatorTailPackage
    (d := d) K support).tailBounds


theorem minimalCubicRowsIndicatorTailPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (minimalCubicRowsIndicatorTailPackage
      (d := d) K support).certificate.FixedPointEnclosure :=
  (minimalCubicRowsIndicatorTailPackage
    (d := d) K support).fixedPointEnclosure


theorem minimalCubicRowsIndicatorTailPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (minimalCubicRowsIndicatorTailPackage
      (d := d) K support).certificate.LinearizationEnclosure :=
  (minimalCubicRowsIndicatorTailPackage
    (d := d) K support).linearizationEnclosure


theorem minimalCubicRowsIndicatorTailPackage_hyperbolicSplitting
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (minimalCubicRowsIndicatorTailPackage
      (d := d) K support).certificate.HyperbolicSplitting :=
  (minimalCubicRowsIndicatorTailPackage
    (d := d) K support).hyperbolicSplitting


theorem minimalCubicRowsIndicatorTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (minimalCubicRowsIndicatorTailPackage
      (d := d) K support).certificate.OrbitEntry :=
  (minimalCubicRowsIndicatorTailPackage
    (d := d) K support).orbitEntry


theorem rawRowsIndicatorTailPackage_tailPrefixSum_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (rawRowsIndicatorTailPackage (d := d) K support).tailPrefixSum = 0 := by
  simp [rawRowsIndicatorTailPackage, FiniteWitnessPackage.tailPrefixSum,
    FiniteWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffStableKey,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]


theorem rawRowsIndicatorTailPackage_tailBudget_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (rawRowsIndicatorTailPackage (d := d) K support).tailBudget =
      (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
  simp [rawRowsIndicatorTailPackage, FiniteWitnessPackage.tailBudget,
    FiniteWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffStableKey,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem rawRowsIndicatorTailPackage_tailCertifiedTotalBound_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (rawRowsIndicatorTailPackage (d := d) K support).tailCertifiedTotalBound =
      (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
  rw [FiniteWitnessPackage.tailCertifiedTotalBound,
    rawRowsIndicatorTailPackage_tailPrefixSum_eq K support,
    rawRowsIndicatorTailPackage_tailBudget_eq K support]
  ring


theorem minimalCubicRowsIndicatorTailPackage_tailPrefixSum_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (minimalCubicRowsIndicatorTailPackage (d := d) K support).tailPrefixSum =
      0 := by
  simp [minimalCubicRowsIndicatorTailPackage, FiniteWitnessPackage.tailPrefixSum,
    FiniteWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem minimalCubicRowsIndicatorTailPackage_tailBudget_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (minimalCubicRowsIndicatorTailPackage (d := d) K support).tailBudget =
      (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
  simp [minimalCubicRowsIndicatorTailPackage, FiniteWitnessPackage.tailBudget,
    FiniteWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem minimalCubicRowsIndicatorTailPackage_tailCertifiedTotalBound_eq {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (minimalCubicRowsIndicatorTailPackage (d := d) K support).tailCertifiedTotalBound =
      (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
  rw [FiniteWitnessPackage.tailCertifiedTotalBound,
    minimalCubicRowsIndicatorTailPackage_tailPrefixSum_eq K support,
    minimalCubicRowsIndicatorTailPackage_tailBudget_eq K support]
  ring


theorem rawRowsIndicatorTailPackage_singleton_tailCertifiedTotalBound_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsIndicatorTailPackage (d := d) K
      (singletonEmptySupport (d := d) K)).tailCertifiedTotalBound =
      (11 : ℝ) / 10 := by
  rw [rawRowsIndicatorTailPackage_tailCertifiedTotalBound_eq]
  norm_num



theorem rawRowsIndicatorTailPackage_singleton_tail_tsum_le_11_div_10
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (∑' a,
      (rawRowsIndicatorTailPackage (d := d) K
        (singletonEmptySupport (d := d) K)).tailCertificate.weight a) ≤
      (11 : ℝ) / 10 := by
  rw [← rawRowsIndicatorTailPackage_singleton_tailCertifiedTotalBound_eq
    (d := d) K]
  exact (rawRowsIndicatorTailPackage (d := d) K
    (singletonEmptySupport (d := d) K)).tail_tsum_le_certifiedTotalBound



theorem minimalCubicRowsIndicatorTailPackage_singleton_tailCertifiedTotalBound_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsIndicatorTailPackage (d := d) K
      (singletonEmptySupport (d := d) K)).tailCertifiedTotalBound =
      (11 : ℝ) / 10 := by
  rw [minimalCubicRowsIndicatorTailPackage_tailCertifiedTotalBound_eq]
  norm_num



theorem minimalCubicRowsIndicatorTailPackage_singleton_tail_tsum_le_11_div_10
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (∑' a,
      (minimalCubicRowsIndicatorTailPackage (d := d) K
        (singletonEmptySupport (d := d) K)).tailCertificate.weight a) ≤
      (11 : ℝ) / 10 := by
  rw [← minimalCubicRowsIndicatorTailPackage_singleton_tailCertifiedTotalBound_eq
    (d := d) K]
  exact (minimalCubicRowsIndicatorTailPackage (d := d) K
    (singletonEmptySupport (d := d) K)).tail_tsum_le_certifiedTotalBound


theorem rawRowsIndicatorTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((rawRowsIndicatorTailPackage (d := d) K support).certificate)
        correlationLength) :
    RGCertificate.Valid
      ((rawRowsIndicatorTailPackage (d := d) K support).certificate)
      correlationLength :=
  (rawRowsIndicatorTailPackage (d := d) K support).valid_of_bridge hbridge



theorem rawRowsIndicatorTailPackage_hasCriticalNu_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((rawRowsIndicatorTailPackage (d := d) K support).certificate)
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (rawRowsIndicatorTailPackage (d := d) K support).certificate.predictedExponent := by
  simpa using
    FiniteWitnessPackage.hasCriticalNu_of_bridge
      (rawRowsIndicatorTailPackage (d := d) K support) hbridge



theorem minimalCubicRowsIndicatorTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate)
        correlationLength) :
    RGCertificate.Valid
      ((minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate)
      correlationLength :=
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).valid_of_bridge
    hbridge



theorem minimalCubicRowsIndicatorTailPackage_hasCriticalNu_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (correlationLength : ℝ → ℝ)
    (hbridge :
      RGCertificate.RGToExponentBridge
        ((minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate)
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.predictedExponent := by
  simpa using
    FiniteWitnessPackage.hasCriticalNu_of_bridge
      (minimalCubicRowsIndicatorTailPackage (d := d) K support) hbridge



theorem rawRowsIndicatorTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (rawRowsIndicatorTailPackage
          (d := d) K support).certificate.predictedExponent) :
    (rawRowsIndicatorTailPackage
      (d := d) K support).certificate.RGToExponentBridge correlationLength :=
  (rawRowsIndicatorTailPackage
    (d := d) K support).rgToExponentBridge_of_hasCriticalNu hν



theorem rawRowsIndicatorTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (rawRowsIndicatorTailPackage
          (d := d) K support).certificate.predictedExponent) :
    (rawRowsIndicatorTailPackage
      (d := d) K support).certificate.Valid correlationLength :=
  (rawRowsIndicatorTailPackage
    (d := d) K support).valid_of_hasCriticalNu hν



theorem
    minimalCubicRowsIndicatorTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (minimalCubicRowsIndicatorTailPackage
          (d := d) K support).certificate.predictedExponent) :
    (minimalCubicRowsIndicatorTailPackage
      (d := d) K support).certificate.RGToExponentBridge correlationLength :=
  (minimalCubicRowsIndicatorTailPackage
    (d := d) K support).rgToExponentBridge_of_hasCriticalNu hν



theorem minimalCubicRowsIndicatorTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (minimalCubicRowsIndicatorTailPackage
          (d := d) K support).certificate.predictedExponent) :
    (minimalCubicRowsIndicatorTailPackage
      (d := d) K support).certificate.Valid correlationLength :=
  (minimalCubicRowsIndicatorTailPackage
    (d := d) K support).valid_of_hasCriticalNu hν

end FiniteWitnessStableKeyPackageExample
end Exact3D
end StatMech
