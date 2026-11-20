/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.InfiniteTailWitnessPackage
import Code.Exact3D.InfiniteTailSummabilityExample
import Code.Exact3D.FiniteWitnessPackageExample

open scoped BigOperators









namespace StatMech
namespace Exact3D
namespace InfiniteTailWitnessPackageExample



noncomputable def geometricTailWitnessPackage :
    InfiniteTailWitnessPackage (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) where
  nStable := 1
  scale := FiniteWitnessPackageExample.exampleScale
  thermal := 3
  thermal_gt_one := by norm_num
  stable := FiniteWitnessPackageExample.stableZeroWitness
  tailCertificate :=
    InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificate



theorem geometricTailWitnessPackage_finiteChecks :
    geometricTailWitnessPackage.certificate.FiniteChecks :=
  geometricTailWitnessPackage.finiteChecks



theorem geometricTailWitnessPackage_finiteCaseChecks :
    geometricTailWitnessPackage.certificate.FiniteCaseChecks :=
  geometricTailWitnessPackage.finiteCaseChecks



theorem geometricTailWitnessPackage_tailBounds :
    geometricTailWitnessPackage.certificate.TailBounds :=
  geometricTailWitnessPackage.tailBounds



theorem geometricTailWitnessPackage_fixedPointEnclosure :
    geometricTailWitnessPackage.certificate.FixedPointEnclosure :=
  geometricTailWitnessPackage.fixedPointEnclosure



theorem geometricTailWitnessPackage_linearizationEnclosure :
    geometricTailWitnessPackage.certificate.LinearizationEnclosure :=
  geometricTailWitnessPackage.linearizationEnclosure



theorem geometricTailWitnessPackage_hyperbolicSplitting :
    geometricTailWitnessPackage.certificate.HyperbolicSplitting :=
  geometricTailWitnessPackage.hyperbolicSplitting


theorem geometricTailWitnessPackage_orbitEntry :
    geometricTailWitnessPackage.certificate.OrbitEntry :=
  geometricTailWitnessPackage.orbitEntry


theorem geometricTailWitnessPackage_tailCertifiedTotalBound_eq_one :
    geometricTailWitnessPackage.tailCertifiedTotalBound = 1 := by
  norm_num [geometricTailWitnessPackage,
    InfiniteTailWitnessPackage.tailCertifiedTotalBound,
    InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.tailBudget,
    TailSummability.InfiniteTailCertificate.prefixSum,
    InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificate]


theorem geometricTailWitnessPackage_tail_tsum_le_one :
    (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) ≤ 1 := by
  rw [← geometricTailWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact geometricTailWitnessPackage.tail_tsum_le_certifiedTotalBound



theorem geometricTailWitnessPackage_tail_tsum_le_two :
    (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) ≤ 2 :=
  geometricTailWitnessPackage.tail_tsum_le_of_certifiedTotalBound_le
    (by
      rw [geometricTailWitnessPackage_tailCertifiedTotalBound_eq_one]
      norm_num)



theorem geometricTailWitnessPackage_tailTotalTsum_le_one :
    geometricTailWitnessPackage.tailTotalTsum ≤ 1 := by
  rw [← geometricTailWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact geometricTailWitnessPackage.tailTotalTsum_le_certifiedTotalBound



theorem geometricTailWitnessPackage_tailTotalTsum_le_two :
    geometricTailWitnessPackage.tailTotalTsum ≤ 2 := by
  simpa [geometricTailWitnessPackage,
    InfiniteTailWitnessPackage.tailPrefixSum,
    TailSummability.InfiniteTailCertificate.prefixSum,
    InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificate] using
    geometricTailWitnessPackage.tailTotalTsum_le_prefix_add_of_tailBudget_le
      (tailBound' := 2) (by norm_num [geometricTailWitnessPackage,
        InfiniteTailWitnessPackage.tailBudget,
        InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificate])



theorem geometricTailWitnessPackage_tailTotalTsum_split :
    geometricTailWitnessPackage.tailTotalTsum =
      geometricTailWitnessPackage.tailPrefixSum +
        geometricTailWitnessPackage.tailRemainderSum :=
  geometricTailWitnessPackage.tailTotalTsum_eq_prefix_add_remainder


theorem geometricTailWitnessPackage_tailTotalTsum_eq_tsum :
    geometricTailWitnessPackage.tailTotalTsum =
      (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) :=
  geometricTailWitnessPackage.tailTotalTsum_eq_tsum


theorem geometricTailWitnessPackage_summable_tailContribution :
    Summable geometricTailWitnessPackage.tailContribution :=
  geometricTailWitnessPackage.summable_tailContribution


theorem geometricTailWitnessPackage_tailContribution_nonneg (n : ℕ) :
    0 ≤ geometricTailWitnessPackage.tailContribution n :=
  geometricTailWitnessPackage.tailContribution_nonneg n


theorem geometricTailWitnessPackage_tailPrefixSum_nonneg :
    0 ≤ geometricTailWitnessPackage.tailPrefixSum :=
  geometricTailWitnessPackage.tailPrefixSum_nonneg


theorem geometricTailWitnessPackage_tailBudget_nonneg :
    0 ≤ geometricTailWitnessPackage.tailBudget :=
  geometricTailWitnessPackage.tailBudget_nonneg


theorem geometricTailWitnessPackage_tailCertifiedTotalBound_nonneg :
    0 ≤ geometricTailWitnessPackage.tailCertifiedTotalBound :=
  geometricTailWitnessPackage.tailCertifiedTotalBound_nonneg


theorem geometricTailWitnessPackage_tail_tsum_nonneg :
    0 ≤
      (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) :=
  geometricTailWitnessPackage.tail_tsum_nonneg


theorem geometricTailWitnessPackage_tailTotalTsum_nonneg :
    0 ≤ geometricTailWitnessPackage.tailTotalTsum :=
  geometricTailWitnessPackage.tailTotalTsum_nonneg



theorem geometricTailWitnessPackage_tailRemainderSum_le_tailBudget :
    geometricTailWitnessPackage.tailRemainderSum ≤
      geometricTailWitnessPackage.tailBudget :=
  geometricTailWitnessPackage.tailRemainderSum_le_tailBudget


theorem geometricTailWitnessPackage_tailRemainderSum_nonneg :
    0 ≤ geometricTailWitnessPackage.tailRemainderSum :=
  geometricTailWitnessPackage.tailRemainderSum_nonneg


theorem geometricTailWitnessPackage_stable_fixedPoint_mem :
    FiniteContraction.ClosedBall
      geometricTailWitnessPackage.stable.contraction.center
      geometricTailWitnessPackage.stable.contraction.radius
      geometricTailWitnessPackage.stable.fixedPoint :=
  geometricTailWitnessPackage.stable_fixedPoint_mem


theorem geometricTailWitnessPackage_stable_exists_unique_fixedPoint :
    ∃! p : Fin geometricTailWitnessPackage.nStable → ℝ,
      geometricTailWitnessPackage.stable.map p = p :=
  geometricTailWitnessPackage.stable_exists_unique_fixedPoint


theorem geometricTailWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricTailWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    geometricTailWitnessPackage.certificate.Valid correlationLength :=
  geometricTailWitnessPackage.valid_of_bridge hbridge



theorem geometricTailWitnessPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricTailWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_bridge hbridge



theorem geometricTailWitnessPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricTailWitnessPackage.certificate.predictedExponent) :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      correlationLength :=
  geometricTailWitnessPackage.rgToExponentBridge_of_hasCriticalNu hν



theorem geometricTailWitnessPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricTailWitnessPackage.certificate.predictedExponent) :
    geometricTailWitnessPackage.certificate.Valid correlationLength :=
  geometricTailWitnessPackage.valid_of_hasCriticalNu hν



noncomputable def geometricTailWitnessPackageFromEnvelope :
    InfiniteTailWitnessPackage (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailWitnessPackage.ofTailEnvelope
    (α := ℕ) (thermal := 3)
    (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale
    (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (∅ : Finset ℕ)
    InfiniteTailSummabilityExample.geometricHalfTailWeight
    InfiniteTailSummabilityExample.geometricHalfTailWeight
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
    (by
      intro _ _
      rfl)
    InfiniteTailSummabilityExample.geometricHalfTailWeight_summable
    (by
      rw [InfiniteTailSummabilityExample.geometricHalfTailWeight_tsum_eq_one])



theorem geometricTailWitnessPackageFromEnvelope_finiteChecks :
    geometricTailWitnessPackageFromEnvelope.certificate.FiniteChecks :=
  geometricTailWitnessPackageFromEnvelope.finiteChecks



theorem geometricTailWitnessPackageFromEnvelope_finiteCaseChecks :
    geometricTailWitnessPackageFromEnvelope.certificate.FiniteCaseChecks :=
  geometricTailWitnessPackageFromEnvelope.finiteCaseChecks



theorem geometricTailWitnessPackageFromEnvelope_tailBounds :
    geometricTailWitnessPackageFromEnvelope.certificate.TailBounds :=
  geometricTailWitnessPackageFromEnvelope.tailBounds



theorem geometricTailWitnessPackageFromEnvelope_fixedPointEnclosure :
    geometricTailWitnessPackageFromEnvelope.certificate.FixedPointEnclosure :=
  geometricTailWitnessPackageFromEnvelope.fixedPointEnclosure



theorem geometricTailWitnessPackageFromEnvelope_linearizationEnclosure :
    geometricTailWitnessPackageFromEnvelope.certificate.LinearizationEnclosure :=
  geometricTailWitnessPackageFromEnvelope.linearizationEnclosure



theorem geometricTailWitnessPackageFromEnvelope_hyperbolicSplitting :
    geometricTailWitnessPackageFromEnvelope.certificate.HyperbolicSplitting :=
  geometricTailWitnessPackageFromEnvelope.hyperbolicSplitting


theorem geometricTailWitnessPackageFromEnvelope_orbitEntry :
    geometricTailWitnessPackageFromEnvelope.certificate.OrbitEntry :=
  geometricTailWitnessPackageFromEnvelope.orbitEntry


theorem geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_eq_one :
    geometricTailWitnessPackageFromEnvelope.tailCertifiedTotalBound = 1 := by
  norm_num [geometricTailWitnessPackageFromEnvelope,
    InfiniteTailWitnessPackage.ofTailEnvelope,
    InfiniteTailWitnessPackage.tailCertifiedTotalBound,
    InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.tailBudget,
    TailSummability.InfiniteTailCertificate.of_tailEnvelope,
    TailSummability.InfiniteTailCertificate.prefixSum]



theorem geometricTailWitnessPackageFromEnvelope_tail_tsum_le_one :
    (∑' n : ℕ,
      geometricTailWitnessPackageFromEnvelope.tailCertificate.weight n) ≤
      1 := by
  rw [← geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_eq_one]
  exact geometricTailWitnessPackageFromEnvelope.tail_tsum_le_certifiedTotalBound



theorem geometricTailWitnessPackageFromEnvelope_tailTotalTsum_le_one :
    geometricTailWitnessPackageFromEnvelope.tailTotalTsum ≤ 1 := by
  rw [← geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_eq_one]
  exact
    geometricTailWitnessPackageFromEnvelope.tailTotalTsum_le_certifiedTotalBound



theorem geometricTailWitnessPackageFromEnvelope_tailTotalTsum_split :
    geometricTailWitnessPackageFromEnvelope.tailTotalTsum =
      geometricTailWitnessPackageFromEnvelope.tailPrefixSum +
        geometricTailWitnessPackageFromEnvelope.tailRemainderSum :=
  geometricTailWitnessPackageFromEnvelope.tailTotalTsum_eq_prefix_add_remainder



theorem geometricTailWitnessPackageFromEnvelope_tailTotalTsum_eq_tsum :
    geometricTailWitnessPackageFromEnvelope.tailTotalTsum =
      (∑' n : ℕ,
        geometricTailWitnessPackageFromEnvelope.tailCertificate.weight n) :=
  geometricTailWitnessPackageFromEnvelope.tailTotalTsum_eq_tsum


theorem geometricTailWitnessPackageFromEnvelope_summable_tailContribution :
    Summable geometricTailWitnessPackageFromEnvelope.tailContribution :=
  geometricTailWitnessPackageFromEnvelope.summable_tailContribution


theorem geometricTailWitnessPackageFromEnvelope_tailContribution_nonneg
    (n : ℕ) :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailContribution n :=
  geometricTailWitnessPackageFromEnvelope.tailContribution_nonneg n


theorem geometricTailWitnessPackageFromEnvelope_tailPrefixSum_nonneg :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailPrefixSum :=
  geometricTailWitnessPackageFromEnvelope.tailPrefixSum_nonneg


theorem geometricTailWitnessPackageFromEnvelope_tailBudget_nonneg :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailBudget :=
  geometricTailWitnessPackageFromEnvelope.tailBudget_nonneg


theorem geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_nonneg :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailCertifiedTotalBound :=
  geometricTailWitnessPackageFromEnvelope.tailCertifiedTotalBound_nonneg


theorem geometricTailWitnessPackageFromEnvelope_tail_tsum_nonneg :
    0 ≤
      (∑' n : ℕ,
        geometricTailWitnessPackageFromEnvelope.tailCertificate.weight n) :=
  geometricTailWitnessPackageFromEnvelope.tail_tsum_nonneg


theorem geometricTailWitnessPackageFromEnvelope_tailTotalTsum_nonneg :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailTotalTsum :=
  geometricTailWitnessPackageFromEnvelope.tailTotalTsum_nonneg



theorem geometricTailWitnessPackageFromEnvelope_tailRemainderSum_le_tailBudget :
    geometricTailWitnessPackageFromEnvelope.tailRemainderSum ≤
      geometricTailWitnessPackageFromEnvelope.tailBudget :=
  geometricTailWitnessPackageFromEnvelope.tailRemainderSum_le_tailBudget


theorem geometricTailWitnessPackageFromEnvelope_tailRemainderSum_nonneg :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailRemainderSum :=
  geometricTailWitnessPackageFromEnvelope.tailRemainderSum_nonneg


theorem geometricTailWitnessPackageFromEnvelope_stable_fixedPoint_mem :
    FiniteContraction.ClosedBall
      geometricTailWitnessPackageFromEnvelope.stable.contraction.center
      geometricTailWitnessPackageFromEnvelope.stable.contraction.radius
      geometricTailWitnessPackageFromEnvelope.stable.fixedPoint :=
  geometricTailWitnessPackageFromEnvelope.stable_fixedPoint_mem


theorem geometricTailWitnessPackageFromEnvelope_stable_exists_unique_fixedPoint :
    ∃! p : Fin geometricTailWitnessPackageFromEnvelope.nStable → ℝ,
      geometricTailWitnessPackageFromEnvelope.stable.map p = p :=
  geometricTailWitnessPackageFromEnvelope.stable_exists_unique_fixedPoint



theorem geometricTailWitnessPackageFromEnvelope_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricTailWitnessPackageFromEnvelope.certificate.RGToExponentBridge
        correlationLength) :
    geometricTailWitnessPackageFromEnvelope.certificate.Valid
      correlationLength :=
  geometricTailWitnessPackageFromEnvelope.valid_of_bridge hbridge



theorem geometricTailWitnessPackageFromEnvelope_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricTailWitnessPackageFromEnvelope.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      geometricTailWitnessPackageFromEnvelope.certificate.predictedExponent :=
  geometricTailWitnessPackageFromEnvelope.hasCriticalNu_of_bridge hbridge



theorem
    geometricTailWitnessPackageFromEnvelope_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricTailWitnessPackageFromEnvelope.certificate.predictedExponent) :
    geometricTailWitnessPackageFromEnvelope.certificate.RGToExponentBridge
      correlationLength :=
  geometricTailWitnessPackageFromEnvelope.rgToExponentBridge_of_hasCriticalNu
    hν



theorem geometricTailWitnessPackageFromEnvelope_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricTailWitnessPackageFromEnvelope.certificate.predictedExponent) :
    geometricTailWitnessPackageFromEnvelope.certificate.Valid
      correlationLength :=
  geometricTailWitnessPackageFromEnvelope.valid_of_hasCriticalNu hν



noncomputable def geometricTailWitnessPackageFromMaskedEnvelope :
    InfiniteTailWitnessPackage (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailWitnessPackage.ofMaskedTailEnvelope
    (α := ℕ) (thermal := 3)
    (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale
    (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    ({0} : Finset ℕ)
    InfiniteTailSummabilityExample.geometricHalfTailWeight
    InfiniteTailSummabilityExample.geometricHalfTailWeight
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
    (by
      intro n _
      exact InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg n)
    (by
      intro _ _
      exact le_rfl)
    (by
      refine
        InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_summable.congr
          ?_
      intro n
      simp [InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight])
    (by
      convert
        InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_tsum_le_one
        using 1)



theorem geometricTailWitnessPackageFromMaskedEnvelope_finiteChecks :
    geometricTailWitnessPackageFromMaskedEnvelope.certificate.FiniteChecks :=
  geometricTailWitnessPackageFromMaskedEnvelope.finiteChecks


theorem geometricTailWitnessPackageFromMaskedEnvelope_tailBudget_eq_one :
    geometricTailWitnessPackageFromMaskedEnvelope.tailBudget = 1 :=
  rfl



theorem
    geometricTailWitnessPackageFromMaskedEnvelope_tailTotalTsum_le_prefix_add_one :
    geometricTailWitnessPackageFromMaskedEnvelope.tailTotalTsum ≤
      geometricTailWitnessPackageFromMaskedEnvelope.tailPrefixSum + 1 := by
  have hbudget :
      geometricTailWitnessPackageFromMaskedEnvelope.tailBudget ≤ 1 := by
    rw [geometricTailWitnessPackageFromMaskedEnvelope_tailBudget_eq_one]
  exact
    InfiniteTailWitnessPackage.tailTotalTsum_le_prefix_add_of_tailBudget_le
      geometricTailWitnessPackageFromMaskedEnvelope hbudget


noncomputable def geometricContributionSplit : ContributionSplit ℕ where
  finiteContribution := fun _ => 0
  tailContribution := InfiniteTailSummabilityExample.geometricHalfTailWeight
  totalContribution := InfiniteTailSummabilityExample.geometricHalfTailWeight



noncomputable def geometricContributionSplitMaskedTailEnvelopeWitnessPackage :
    InfiniteTailWitnessPackage (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailWitnessPackage.ofContributionSplitMaskedTailEnvelope
    (α := ℕ) (thermal := 3)
    (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale
    (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    geometricContributionSplit
    ({0} : Finset ℕ)
    InfiniteTailSummabilityExample.geometricHalfTailWeight
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
    (by
      intro n
      simp [geometricContributionSplit])
    (by
      intro n _
      simp [geometricContributionSplit])
    (by
      intro n _
      exact InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg n)
    (by
      intro _ _
      exact le_rfl)
    (by
      refine
        InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_summable.congr
          ?_
      intro n
      simp [InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight])
    (by
      convert
        InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_tsum_le_one
        using 1)



theorem geometricContributionSplitMaskedTailEnvelopeWitnessPackage_finiteChecks :
    RGCertificate.FiniteChecks
      geometricContributionSplitMaskedTailEnvelopeWitnessPackage.certificate :=
  geometricContributionSplitMaskedTailEnvelopeWitnessPackage.finiteChecks


theorem
    geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailBudget_eq_one :
    geometricContributionSplitMaskedTailEnvelopeWitnessPackage.tailBudget = 1 :=
  rfl



theorem
    geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailTotalTsum_le_prefix_add_one :
    geometricContributionSplitMaskedTailEnvelopeWitnessPackage.tailTotalTsum ≤
      geometricContributionSplitMaskedTailEnvelopeWitnessPackage.tailPrefixSum +
        1 := by
  have hbudget :
      geometricContributionSplitMaskedTailEnvelopeWitnessPackage.tailBudget ≤
        1 := by
    rw
      [geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailBudget_eq_one]
  exact
    InfiniteTailWitnessPackage.tailTotalTsum_le_prefix_add_of_tailBudget_le
      geometricContributionSplitMaskedTailEnvelopeWitnessPackage hbudget



noncomputable def geometricContributionSplitWitnessPackage :
    InfiniteTailWitnessPackage (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailWitnessPackage.ofContributionSplitInfiniteTail
    (α := ℕ) (thermal := 3)
    (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale
    (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    geometricContributionSplit
    (∅ : Finset ℕ)
    InfiniteTailSummabilityExample.geometricHalfTailWeight
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
    (by
      intro _ _
      rfl)
    InfiniteTailSummabilityExample.geometricHalfTailWeight_summable
    (by
      rw [InfiniteTailSummabilityExample.geometricHalfTailWeight_tsum_eq_one])



theorem geometricContributionSplitWitnessPackage_finiteChecks :
    geometricContributionSplitWitnessPackage.certificate.FiniteChecks :=
  geometricContributionSplitWitnessPackage.finiteChecks



theorem geometricContributionSplitWitnessPackage_finiteCaseChecks :
    geometricContributionSplitWitnessPackage.certificate.FiniteCaseChecks :=
  geometricContributionSplitWitnessPackage.finiteCaseChecks



theorem geometricContributionSplitWitnessPackage_tailBounds :
    geometricContributionSplitWitnessPackage.certificate.TailBounds :=
  geometricContributionSplitWitnessPackage.tailBounds



theorem geometricContributionSplitWitnessPackage_fixedPointEnclosure :
    geometricContributionSplitWitnessPackage.certificate.FixedPointEnclosure :=
  geometricContributionSplitWitnessPackage.fixedPointEnclosure



theorem geometricContributionSplitWitnessPackage_linearizationEnclosure :
    geometricContributionSplitWitnessPackage.certificate.LinearizationEnclosure :=
  geometricContributionSplitWitnessPackage.linearizationEnclosure



theorem geometricContributionSplitWitnessPackage_hyperbolicSplitting :
    geometricContributionSplitWitnessPackage.certificate.HyperbolicSplitting :=
  geometricContributionSplitWitnessPackage.hyperbolicSplitting



theorem geometricContributionSplitWitnessPackage_orbitEntry :
    geometricContributionSplitWitnessPackage.certificate.OrbitEntry :=
  geometricContributionSplitWitnessPackage.orbitEntry



theorem geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_eq_one :
    geometricContributionSplitWitnessPackage.tailCertifiedTotalBound = 1 := by
  norm_num [geometricContributionSplitWitnessPackage,
    InfiniteTailWitnessPackage.ofContributionSplitInfiniteTail,
    InfiniteTailWitnessPackage.ofTailEnvelope,
    InfiniteTailWitnessPackage.tailCertifiedTotalBound,
    InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.tailBudget,
    TailSummability.InfiniteTailCertificate.of_tailEnvelope,
    TailSummability.InfiniteTailCertificate.prefixSum,
    geometricContributionSplit]



theorem geometricContributionSplitWitnessPackage_tail_tsum_le_one :
    (∑' n : ℕ,
      geometricContributionSplitWitnessPackage.tailCertificate.weight n) ≤
      1 := by
  rw [← geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact geometricContributionSplitWitnessPackage.tail_tsum_le_certifiedTotalBound



theorem geometricContributionSplitWitnessPackage_tailTotalTsum_le_one :
    geometricContributionSplitWitnessPackage.tailTotalTsum ≤ 1 := by
  rw [← geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact
    geometricContributionSplitWitnessPackage.tailTotalTsum_le_certifiedTotalBound



theorem geometricContributionSplitWitnessPackage_tailTotalTsum_split :
    geometricContributionSplitWitnessPackage.tailTotalTsum =
      geometricContributionSplitWitnessPackage.tailPrefixSum +
        geometricContributionSplitWitnessPackage.tailRemainderSum :=
  geometricContributionSplitWitnessPackage.tailTotalTsum_eq_prefix_add_remainder



theorem geometricContributionSplitWitnessPackage_tailTotalTsum_eq_tsum :
    geometricContributionSplitWitnessPackage.tailTotalTsum =
      (∑' n : ℕ,
        geometricContributionSplitWitnessPackage.tailCertificate.weight n) :=
  geometricContributionSplitWitnessPackage.tailTotalTsum_eq_tsum


theorem geometricContributionSplitWitnessPackage_summable_tailContribution :
    Summable geometricContributionSplitWitnessPackage.tailContribution :=
  geometricContributionSplitWitnessPackage.summable_tailContribution



theorem geometricContributionSplitWitnessPackage_tailContribution_nonneg
    (n : ℕ) :
    0 ≤ geometricContributionSplitWitnessPackage.tailContribution n :=
  geometricContributionSplitWitnessPackage.tailContribution_nonneg n


theorem geometricContributionSplitWitnessPackage_tailPrefixSum_nonneg :
    0 ≤ geometricContributionSplitWitnessPackage.tailPrefixSum :=
  geometricContributionSplitWitnessPackage.tailPrefixSum_nonneg


theorem geometricContributionSplitWitnessPackage_tailBudget_nonneg :
    0 ≤ geometricContributionSplitWitnessPackage.tailBudget :=
  geometricContributionSplitWitnessPackage.tailBudget_nonneg


theorem geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_nonneg :
    0 ≤ geometricContributionSplitWitnessPackage.tailCertifiedTotalBound :=
  geometricContributionSplitWitnessPackage.tailCertifiedTotalBound_nonneg


theorem geometricContributionSplitWitnessPackage_tail_tsum_nonneg :
    0 ≤
      (∑' n : ℕ,
        geometricContributionSplitWitnessPackage.tailCertificate.weight n) :=
  geometricContributionSplitWitnessPackage.tail_tsum_nonneg


theorem geometricContributionSplitWitnessPackage_tailTotalTsum_nonneg :
    0 ≤ geometricContributionSplitWitnessPackage.tailTotalTsum :=
  geometricContributionSplitWitnessPackage.tailTotalTsum_nonneg



theorem
    geometricContributionSplitWitnessPackage_tailRemainderSum_le_tailBudget :
    geometricContributionSplitWitnessPackage.tailRemainderSum ≤
      geometricContributionSplitWitnessPackage.tailBudget :=
  geometricContributionSplitWitnessPackage.tailRemainderSum_le_tailBudget


theorem geometricContributionSplitWitnessPackage_tailRemainderSum_nonneg :
    0 ≤ geometricContributionSplitWitnessPackage.tailRemainderSum :=
  geometricContributionSplitWitnessPackage.tailRemainderSum_nonneg



theorem geometricContributionSplitWitnessPackage_stable_fixedPoint_mem :
    FiniteContraction.ClosedBall
      geometricContributionSplitWitnessPackage.stable.contraction.center
      geometricContributionSplitWitnessPackage.stable.contraction.radius
      geometricContributionSplitWitnessPackage.stable.fixedPoint :=
  geometricContributionSplitWitnessPackage.stable_fixedPoint_mem


theorem
    geometricContributionSplitWitnessPackage_stable_exists_unique_fixedPoint :
    ∃! p : Fin geometricContributionSplitWitnessPackage.nStable → ℝ,
      geometricContributionSplitWitnessPackage.stable.map p = p :=
  geometricContributionSplitWitnessPackage.stable_exists_unique_fixedPoint



theorem geometricContributionSplitWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricContributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    geometricContributionSplitWitnessPackage.certificate.Valid
      correlationLength :=
  geometricContributionSplitWitnessPackage.valid_of_bridge hbridge



theorem geometricContributionSplitWitnessPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricContributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      geometricContributionSplitWitnessPackage.certificate.predictedExponent :=
  geometricContributionSplitWitnessPackage.hasCriticalNu_of_bridge hbridge



theorem
    geometricContributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricContributionSplitWitnessPackage.certificate.predictedExponent) :
    geometricContributionSplitWitnessPackage.certificate.RGToExponentBridge
      correlationLength :=
  geometricContributionSplitWitnessPackage.rgToExponentBridge_of_hasCriticalNu
    hν



theorem geometricContributionSplitWitnessPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricContributionSplitWitnessPackage.certificate.predictedExponent) :
    geometricContributionSplitWitnessPackage.certificate.Valid
      correlationLength :=
  geometricContributionSplitWitnessPackage.valid_of_hasCriticalNu hν




noncomputable def geometricContributionSplitTailEnvelopeWitnessPackage :
    InfiniteTailWitnessPackage (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailWitnessPackage.ofContributionSplitTailEnvelope
    (α := ℕ) (thermal := 3)
    (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale
    (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    geometricContributionSplit
    (∅ : Finset ℕ)
    InfiniteTailSummabilityExample.geometricHalfTailWeight
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
    (by
      intro n
      simp [geometricContributionSplit])
    (by
      intro n _
      simp [geometricContributionSplit])
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
    (by
      intro _ _
      rfl)
    InfiniteTailSummabilityExample.geometricHalfTailWeight_summable
    (by
      rw [InfiniteTailSummabilityExample.geometricHalfTailWeight_tsum_eq_one])



theorem geometricContributionSplitTailEnvelopeWitnessPackage_finiteChecks :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.FiniteChecks :=
  geometricContributionSplitTailEnvelopeWitnessPackage.finiteChecks



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_finiteCaseChecks :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.FiniteCaseChecks :=
  geometricContributionSplitTailEnvelopeWitnessPackage.finiteCaseChecks



theorem geometricContributionSplitTailEnvelopeWitnessPackage_tailBounds :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.TailBounds :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailBounds



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_fixedPointEnclosure :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.FixedPointEnclosure :=
  geometricContributionSplitTailEnvelopeWitnessPackage.fixedPointEnclosure



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_linearizationEnclosure :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.LinearizationEnclosure :=
  geometricContributionSplitTailEnvelopeWitnessPackage.linearizationEnclosure



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_hyperbolicSplitting :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.HyperbolicSplitting :=
  geometricContributionSplitTailEnvelopeWitnessPackage.hyperbolicSplitting



theorem geometricContributionSplitTailEnvelopeWitnessPackage_orbitEntry :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.OrbitEntry :=
  geometricContributionSplitTailEnvelopeWitnessPackage.orbitEntry



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_eq_one :
    geometricContributionSplitTailEnvelopeWitnessPackage.tailCertifiedTotalBound =
      1 := by
  norm_num [geometricContributionSplitTailEnvelopeWitnessPackage,
    InfiniteTailWitnessPackage.ofContributionSplitTailEnvelope,
    InfiniteTailWitnessPackage.tailCertifiedTotalBound,
    InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.tailBudget,
    ContributionSplit.infiniteTailCertificate_of_tailEnvelope_off_prefix,
    TailSummability.InfiniteTailCertificate.of_tailEnvelope,
    TailSummability.InfiniteTailCertificate.prefixSum,
    geometricContributionSplit]



theorem geometricContributionSplitTailEnvelopeWitnessPackage_tail_tsum_le_one :
    (∑' n : ℕ,
      geometricContributionSplitTailEnvelopeWitnessPackage.tailCertificate.weight
        n) ≤ 1 := by
  rw [←
    geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact
    geometricContributionSplitTailEnvelopeWitnessPackage.tail_tsum_le_certifiedTotalBound



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_le_one :
    geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum ≤
      1 := by
  rw [←
    geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact
    geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum_le_certifiedTotalBound



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_split :
    geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum =
      geometricContributionSplitTailEnvelopeWitnessPackage.tailPrefixSum +
        geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum_eq_prefix_add_remainder



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_eq_tsum :
    geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum =
      (∑' n : ℕ,
        geometricContributionSplitTailEnvelopeWitnessPackage.tailCertificate.weight n) :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum_eq_tsum


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_summable_tailContribution :
    Summable
      geometricContributionSplitTailEnvelopeWitnessPackage.tailContribution :=
  geometricContributionSplitTailEnvelopeWitnessPackage.summable_tailContribution


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailContribution_nonneg
    (n : ℕ) :
    0 ≤
      geometricContributionSplitTailEnvelopeWitnessPackage.tailContribution n :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailContribution_nonneg n


theorem geometricContributionSplitTailEnvelopeWitnessPackage_tailPrefixSum_nonneg :
    0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailPrefixSum :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailPrefixSum_nonneg


theorem geometricContributionSplitTailEnvelopeWitnessPackage_tailBudget_nonneg :
    0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailBudget :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailBudget_nonneg


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_nonneg :
    0 ≤
      geometricContributionSplitTailEnvelopeWitnessPackage.tailCertifiedTotalBound :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailCertifiedTotalBound_nonneg


theorem geometricContributionSplitTailEnvelopeWitnessPackage_tail_tsum_nonneg :
    0 ≤
      (∑' n : ℕ,
        geometricContributionSplitTailEnvelopeWitnessPackage.tailCertificate.weight n) :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tail_tsum_nonneg


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_nonneg :
    0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum_nonneg



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailRemainderSum_le_tailBudget :
    geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum ≤
      geometricContributionSplitTailEnvelopeWitnessPackage.tailBudget :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum_le_tailBudget


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailRemainderSum_nonneg :
    0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum_nonneg


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_stable_fixedPoint_mem :
    FiniteContraction.ClosedBall
      geometricContributionSplitTailEnvelopeWitnessPackage.stable.contraction.center
      geometricContributionSplitTailEnvelopeWitnessPackage.stable.contraction.radius
      geometricContributionSplitTailEnvelopeWitnessPackage.stable.fixedPoint :=
  geometricContributionSplitTailEnvelopeWitnessPackage.stable_fixedPoint_mem


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_stable_exists_unique_fixedPoint :
    ∃! p :
      Fin geometricContributionSplitTailEnvelopeWitnessPackage.nStable → ℝ,
      geometricContributionSplitTailEnvelopeWitnessPackage.stable.map p = p :=
  geometricContributionSplitTailEnvelopeWitnessPackage.stable_exists_unique_fixedPoint



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricContributionSplitTailEnvelopeWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.Valid
      correlationLength :=
  geometricContributionSplitTailEnvelopeWitnessPackage.valid_of_bridge hbridge



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricContributionSplitTailEnvelopeWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      geometricContributionSplitTailEnvelopeWitnessPackage.certificate.predictedExponent :=
  geometricContributionSplitTailEnvelopeWitnessPackage.hasCriticalNu_of_bridge
    hbridge



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricContributionSplitTailEnvelopeWitnessPackage.certificate.predictedExponent) :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.RGToExponentBridge
      correlationLength :=
  geometricContributionSplitTailEnvelopeWitnessPackage.rgToExponentBridge_of_hasCriticalNu
    hν



theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricContributionSplitTailEnvelopeWitnessPackage.certificate.predictedExponent) :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.Valid
      correlationLength :=
  geometricContributionSplitTailEnvelopeWitnessPackage.valid_of_hasCriticalNu
    hν



noncomputable def contributionSplitAsInfiniteTailPackage :
    InfiniteTailWitnessPackage (α := Fin 2)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailWitnessPackage.ofFiniteWitnessPackage
    FiniteWitnessPackageExample.contributionSplitWitnessPackage



theorem contributionSplitAsInfiniteTailPackage_certificate_eq :
    contributionSplitAsInfiniteTailPackage.certificate =
      FiniteWitnessPackageExample.contributionSplitWitnessPackage.certificate :=
  rfl



theorem contributionSplitAsInfiniteTailPackage_tailPrefixSum_eq :
    contributionSplitAsInfiniteTailPackage.tailPrefixSum =
      FiniteWitnessPackageExample.contributionSplitWitnessPackage.tailPrefixSum :=
  rfl



theorem contributionSplitAsInfiniteTailPackage_tailBudget_eq :
    contributionSplitAsInfiniteTailPackage.tailBudget =
      FiniteWitnessPackageExample.contributionSplitWitnessPackage.tailBudget :=
  rfl



theorem contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq_finite :
    contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound =
      FiniteWitnessPackageExample.contributionSplitWitnessPackage.tailCertifiedTotalBound :=
  rfl


theorem contributionSplitAsInfiniteTailPackage_finiteChecks :
    contributionSplitAsInfiniteTailPackage.certificate.FiniteChecks := by
  simpa [contributionSplitAsInfiniteTailPackage] using
    FiniteWitnessPackageExample.contributionSplitWitnessPackage_finiteChecks


theorem contributionSplitAsInfiniteTailPackage_finiteCaseChecks :
    contributionSplitAsInfiniteTailPackage.certificate.FiniteCaseChecks :=
  contributionSplitAsInfiniteTailPackage.finiteCaseChecks


theorem contributionSplitAsInfiniteTailPackage_tailBounds :
    contributionSplitAsInfiniteTailPackage.certificate.TailBounds :=
  contributionSplitAsInfiniteTailPackage.tailBounds


theorem contributionSplitAsInfiniteTailPackage_fixedPointEnclosure :
    contributionSplitAsInfiniteTailPackage.certificate.FixedPointEnclosure :=
  contributionSplitAsInfiniteTailPackage.fixedPointEnclosure



theorem contributionSplitAsInfiniteTailPackage_linearizationEnclosure :
    contributionSplitAsInfiniteTailPackage.certificate.LinearizationEnclosure :=
  contributionSplitAsInfiniteTailPackage.linearizationEnclosure


theorem contributionSplitAsInfiniteTailPackage_hyperbolicSplitting :
    contributionSplitAsInfiniteTailPackage.certificate.HyperbolicSplitting :=
  contributionSplitAsInfiniteTailPackage.hyperbolicSplitting


theorem contributionSplitAsInfiniteTailPackage_orbitEntry :
    contributionSplitAsInfiniteTailPackage.certificate.OrbitEntry :=
  contributionSplitAsInfiniteTailPackage.orbitEntry


theorem contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq :
    contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound =
      (11 : ℝ) / 5 := by
  norm_num [contributionSplitAsInfiniteTailPackage,
    InfiniteTailWitnessPackage.ofFiniteWitnessPackage,
    InfiniteTailWitnessPackage.tailCertifiedTotalBound,
    InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.tailBudget,
    TailSummability.InfiniteTailCertificate.prefixSum,
    TailSummability.FiniteSupportCertificate.toInfiniteTailCertificate,
    FiniteWitnessPackageExample.contributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit]



theorem contributionSplitAsInfiniteTailPackage_tailTotalTsum_le_certified :
    contributionSplitAsInfiniteTailPackage.tailTotalTsum ≤
      contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound :=
  contributionSplitAsInfiniteTailPackage.tailTotalTsum_le_certifiedTotalBound



theorem contributionSplitAsInfiniteTailPackage_tail_tsum_le_11_div_5 :
    (∑' a : Fin 2,
      contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) ≤
      (11 : ℝ) / 5 := by
  rw [← contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq]
  exact contributionSplitAsInfiniteTailPackage.tail_tsum_le_certifiedTotalBound



theorem contributionSplitAsInfiniteTailPackage_tail_tsum_le_three :
    (∑' a : Fin 2,
      contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) ≤
      (3 : ℝ) :=
  contributionSplitAsInfiniteTailPackage.tail_tsum_le_of_certifiedTotalBound_le
    (by
      rw [contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq]
      norm_num)



theorem contributionSplitAsInfiniteTailPackage_tailTotalTsum_le_11_div_5 :
    contributionSplitAsInfiniteTailPackage.tailTotalTsum ≤
      (11 : ℝ) / 5 := by
  rw [← contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq]
  exact
    contributionSplitAsInfiniteTailPackage.tailTotalTsum_le_certifiedTotalBound



theorem contributionSplitAsInfiniteTailPackage_tailTotalTsum_split :
    contributionSplitAsInfiniteTailPackage.tailTotalTsum =
      contributionSplitAsInfiniteTailPackage.tailPrefixSum +
        contributionSplitAsInfiniteTailPackage.tailRemainderSum :=
  contributionSplitAsInfiniteTailPackage.tailTotalTsum_eq_prefix_add_remainder



theorem contributionSplitAsInfiniteTailPackage_tailTotalTsum_eq_tsum :
    contributionSplitAsInfiniteTailPackage.tailTotalTsum =
      (∑' a : Fin 2,
        contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) :=
  contributionSplitAsInfiniteTailPackage.tailTotalTsum_eq_tsum


theorem contributionSplitAsInfiniteTailPackage_summable_tailContribution :
    Summable contributionSplitAsInfiniteTailPackage.tailContribution :=
  contributionSplitAsInfiniteTailPackage.summable_tailContribution



theorem contributionSplitAsInfiniteTailPackage_tailContribution_nonneg
    (a : Fin 2) :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailContribution a :=
  contributionSplitAsInfiniteTailPackage.tailContribution_nonneg a


theorem contributionSplitAsInfiniteTailPackage_tailPrefixSum_nonneg :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailPrefixSum :=
  contributionSplitAsInfiniteTailPackage.tailPrefixSum_nonneg


theorem contributionSplitAsInfiniteTailPackage_tailBudget_nonneg :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailBudget :=
  contributionSplitAsInfiniteTailPackage.tailBudget_nonneg


theorem contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_nonneg :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound :=
  contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound_nonneg


theorem contributionSplitAsInfiniteTailPackage_tail_tsum_nonneg :
    0 ≤
      (∑' a : Fin 2,
        contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) :=
  contributionSplitAsInfiniteTailPackage.tail_tsum_nonneg


theorem contributionSplitAsInfiniteTailPackage_tailTotalTsum_nonneg :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailTotalTsum :=
  contributionSplitAsInfiniteTailPackage.tailTotalTsum_nonneg



theorem contributionSplitAsInfiniteTailPackage_tailRemainderSum_le_tailBudget :
    contributionSplitAsInfiniteTailPackage.tailRemainderSum ≤
      contributionSplitAsInfiniteTailPackage.tailBudget :=
  contributionSplitAsInfiniteTailPackage.tailRemainderSum_le_tailBudget


theorem contributionSplitAsInfiniteTailPackage_tailRemainderSum_nonneg :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailRemainderSum :=
  contributionSplitAsInfiniteTailPackage.tailRemainderSum_nonneg



theorem contributionSplitAsInfiniteTailPackage_stable_fixedPoint_mem :
    FiniteContraction.ClosedBall
      contributionSplitAsInfiniteTailPackage.stable.contraction.center
      contributionSplitAsInfiniteTailPackage.stable.contraction.radius
      contributionSplitAsInfiniteTailPackage.stable.fixedPoint :=
  contributionSplitAsInfiniteTailPackage.stable_fixedPoint_mem


theorem contributionSplitAsInfiniteTailPackage_stable_exists_unique_fixedPoint :
    ∃! p : Fin contributionSplitAsInfiniteTailPackage.nStable → ℝ,
      contributionSplitAsInfiniteTailPackage.stable.map p = p :=
  contributionSplitAsInfiniteTailPackage.stable_exists_unique_fixedPoint



theorem contributionSplitAsInfiniteTailPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge
        correlationLength) :
    contributionSplitAsInfiniteTailPackage.certificate.Valid
      correlationLength :=
  contributionSplitAsInfiniteTailPackage.valid_of_bridge hbridge



theorem contributionSplitAsInfiniteTailPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      contributionSplitAsInfiniteTailPackage.certificate.predictedExponent :=
  contributionSplitAsInfiniteTailPackage.hasCriticalNu_of_bridge hbridge



theorem
    contributionSplitAsInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        contributionSplitAsInfiniteTailPackage.certificate.predictedExponent) :
    contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge
      correlationLength :=
  contributionSplitAsInfiniteTailPackage.rgToExponentBridge_of_hasCriticalNu
    hν



theorem contributionSplitAsInfiniteTailPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        contributionSplitAsInfiniteTailPackage.certificate.predictedExponent) :
    contributionSplitAsInfiniteTailPackage.certificate.Valid
      correlationLength :=
  contributionSplitAsInfiniteTailPackage.valid_of_hasCriticalNu hν

end InfiniteTailWitnessPackageExample

end Exact3D
end StatMech
