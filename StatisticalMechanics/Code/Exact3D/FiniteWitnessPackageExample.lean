/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FiniteWitnessPackage
import Code.Exact3D.TailSummabilityExample
import Code.Exact3D.ToyRG
import Code.Exact3D.Hierarchical

open scoped BigOperators










namespace StatMech
namespace Exact3D
namespace FiniteWitnessPackageExample


def exampleScale : BlockScale where
  L := 2
  one_lt := by norm_num


noncomputable def stableZeroWitness : FiniteStableWitness 1 where
  map := @FiniteContraction.zeroMap 1
  contraction :=
    FiniteContraction.zeroMap_closedBallContractionCertificate
      (n := 1) (radius := 0) (by norm_num)


theorem exampleSplit_total_nonneg :
    ∀ a : Fin 2, 0 ≤ TailSummabilityExample.exampleSplit.totalContribution a := by
  intro a
  norm_num [TailSummabilityExample.exampleSplit]



noncomputable def contributionSplitWitnessPackage :
    FiniteWitnessPackage (α := Fin 2) (ToyCriticalModel exampleScale 3) :=
  FiniteWitnessPackage.ofContributionSplitFiniteSupport
    (α := Fin 2) (Case := Unit)
    (ToyCriticalModel exampleScale 3)
    exampleScale (thermal := 3) (by norm_num)
    stableZeroWitness
    TailSummabilityExample.exampleSplit
    (Finset.univ : Finset (Fin 2)) ∅
    (T := TailSummabilityExample.exampleTable)
    (classify := TailSummabilityExample.exampleClassifier)
    (finiteBound := (1 : ℝ))
    (tailEnvelopeBound := (1 : ℝ) / 5)
    (fun _ => (1 : ℝ) / 10)
    (by simp)
    TailSummabilityExample.exampleTotal_zero_off_support
    exampleSplit_total_nonneg
    TailSummabilityExample.exampleSplit_additive
    TailSummabilityExample.exampleFiniteTableUpperBound
    TailSummabilityExample.exampleTailEnvelopeOn
    (by simpa using TailSummabilityExample.exampleTailEnvelopeSum_le)



theorem contributionSplitWitnessPackage_finiteChecks :
    contributionSplitWitnessPackage.certificate.FiniteChecks :=
  contributionSplitWitnessPackage.finiteChecks


theorem contributionSplitWitnessPackage_finiteCaseChecks :
    contributionSplitWitnessPackage.certificate.FiniteCaseChecks :=
  contributionSplitWitnessPackage.finiteCaseChecks


theorem contributionSplitWitnessPackage_tailBounds :
    contributionSplitWitnessPackage.certificate.TailBounds :=
  contributionSplitWitnessPackage.tailBounds


theorem contributionSplitWitnessPackage_fixedPointEnclosure :
    contributionSplitWitnessPackage.certificate.FixedPointEnclosure :=
  contributionSplitWitnessPackage.fixedPointEnclosure


theorem contributionSplitWitnessPackage_linearizationEnclosure :
    contributionSplitWitnessPackage.certificate.LinearizationEnclosure :=
  contributionSplitWitnessPackage.linearizationEnclosure


theorem contributionSplitWitnessPackage_hyperbolicSplitting :
    contributionSplitWitnessPackage.certificate.HyperbolicSplitting :=
  contributionSplitWitnessPackage.hyperbolicSplitting


theorem contributionSplitWitnessPackage_orbitEntry :
    contributionSplitWitnessPackage.certificate.OrbitEntry :=
  contributionSplitWitnessPackage.orbitEntry



theorem contributionSplitWitnessPackage_predictedExponent_eq :
    contributionSplitWitnessPackage.certificate.predictedExponent =
      Real.log exampleScale.toReal / Real.log 3 := by
  rfl


theorem contributionSplitWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      contributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    contributionSplitWitnessPackage.certificate.Valid correlationLength :=
  contributionSplitWitnessPackage.valid_of_bridge hbridge



theorem contributionSplitWitnessPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      contributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu (ToyCriticalModel exampleScale 3) correlationLength
      contributionSplitWitnessPackage.certificate.predictedExponent :=
  contributionSplitWitnessPackage.hasCriticalNu_of_bridge hbridge



theorem contributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu (ToyCriticalModel exampleScale 3) correlationLength
        contributionSplitWitnessPackage.certificate.predictedExponent) :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      correlationLength :=
  contributionSplitWitnessPackage.rgToExponentBridge_of_hasCriticalNu hν



theorem contributionSplitWitnessPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu (ToyCriticalModel exampleScale 3) correlationLength
        contributionSplitWitnessPackage.certificate.predictedExponent) :
    contributionSplitWitnessPackage.certificate.Valid correlationLength :=
  contributionSplitWitnessPackage.valid_of_hasCriticalNu hν



noncomputable def hierarchicalStableClosedBallCertificate :
    FiniteContraction.ClosedBallContractionCertificate
      (fun x i => RatInterval.matVec hierarchicalStableLinearization x i) :=
  FiniteContraction.closedBallContractionCertificate_of_rowSumContraction
    hierarchicalStableRowSumContraction
    hierarchicalStableLinearization_mem_intervals
    (0 : Fin 1 → ℝ)
    (radius := 0)
    (by norm_num [hierarchicalStableRowSumContraction])
    (by norm_num)
    (by
      simp [FiniteContraction.l1Dist, RatInterval.matVec,
        RatInterval.supNormVec])


noncomputable def hierarchicalStableWitness : FiniteStableWitness 1 where
  map := fun x i => RatInterval.matVec hierarchicalStableLinearization x i
  contraction := hierarchicalStableClosedBallCertificate


theorem hierarchicalStableWitness_fixedPoint_eq_zero :
    hierarchicalStableWitness.fixedPoint = (0 : Fin 1 → ℝ) := by
  have hmem := hierarchicalStableWitness.fixedPoint_mem
  unfold FiniteContraction.ClosedBall at hmem
  exact FiniteContraction.eq_of_l1Dist_eq_zero
    (le_antisymm hmem (FiniteContraction.l1Dist_nonneg _ _))



noncomputable def hierarchicalContributionSplitWitnessPackage :
    FiniteWitnessPackage (α := Fin 2) HierarchicalModel :=
  FiniteWitnessPackage.ofContributionSplitFiniteSupport
    (α := Fin 2) (Case := Unit)
    HierarchicalModel
    hierarchicalScale (thermal := hierarchicalThermalEigenvalue)
    hierarchical_thermal_gt_one
    hierarchicalStableWitness
    TailSummabilityExample.exampleSplit
    (Finset.univ : Finset (Fin 2)) ∅
    (T := TailSummabilityExample.exampleTable)
    (classify := TailSummabilityExample.exampleClassifier)
    (finiteBound := (1 : ℝ))
    (tailEnvelopeBound := (1 : ℝ) / 5)
    (fun _ => (1 : ℝ) / 10)
    (by simp)
    TailSummabilityExample.exampleTotal_zero_off_support
    exampleSplit_total_nonneg
    TailSummabilityExample.exampleSplit_additive
    TailSummabilityExample.exampleFiniteTableUpperBound
    TailSummabilityExample.exampleTailEnvelopeOn
    (by simpa using TailSummabilityExample.exampleTailEnvelopeSum_le)


theorem hierarchicalContributionSplitWitnessPackage_fixedPoint_eq :
    hierarchicalContributionSplitWitnessPackage.rgMap.map
      hierarchicalContributionSplitWitnessPackage.fixedPoint =
    hierarchicalContributionSplitWitnessPackage.fixedPoint :=
  hierarchicalContributionSplitWitnessPackage.fixedPoint_eq


theorem hierarchicalContributionSplitWitnessPackage_stable_unique :
    ∃! p : Fin 1 → ℝ, hierarchicalStableWitness.map p = p :=
  hierarchicalStableWitness.exists_unique_fixedPoint


theorem hierarchicalContributionSplitWitnessPackage_finiteChecks :
    hierarchicalContributionSplitWitnessPackage.certificate.FiniteChecks :=
  hierarchicalContributionSplitWitnessPackage.finiteChecks


theorem hierarchicalContributionSplitWitnessPackage_finiteCaseChecks :
    hierarchicalContributionSplitWitnessPackage.certificate.FiniteCaseChecks :=
  hierarchicalContributionSplitWitnessPackage.finiteCaseChecks


theorem hierarchicalContributionSplitWitnessPackage_tailBounds :
    hierarchicalContributionSplitWitnessPackage.certificate.TailBounds :=
  hierarchicalContributionSplitWitnessPackage.tailBounds



theorem hierarchicalContributionSplitWitnessPackage_fixedPointEnclosure :
    hierarchicalContributionSplitWitnessPackage.certificate.FixedPointEnclosure :=
  hierarchicalContributionSplitWitnessPackage.fixedPointEnclosure



theorem hierarchicalContributionSplitWitnessPackage_linearizationEnclosure :
    hierarchicalContributionSplitWitnessPackage.certificate.LinearizationEnclosure :=
  hierarchicalContributionSplitWitnessPackage.linearizationEnclosure



theorem hierarchicalContributionSplitWitnessPackage_hyperbolicSplitting :
    hierarchicalContributionSplitWitnessPackage.certificate.HyperbolicSplitting :=
  hierarchicalContributionSplitWitnessPackage.hyperbolicSplitting


theorem hierarchicalContributionSplitWitnessPackage_orbitEntry :
    hierarchicalContributionSplitWitnessPackage.certificate.OrbitEntry :=
  hierarchicalContributionSplitWitnessPackage.orbitEntry



theorem hierarchicalContributionSplitWitnessPackage_predictedExponent_eq :
    hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent =
      Real.log hierarchicalScale.toReal / Real.log hierarchicalThermalEigenvalue := by
  rfl



theorem hierarchicalContributionSplitWitnessPackage_tail_bound :
    (∑' a, hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) ≤
      (∑ a ∈ hierarchicalContributionSplitWitnessPackage.tailCertificate.finitePrefix,
        hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) +
        hierarchicalContributionSplitWitnessPackage.tailCertificate.tailBound :=
  hierarchicalContributionSplitWitnessPackage.tail_tsum_le_prefix_add_tailBound



theorem contributionSplitWitnessPackage_tail_bound_concrete :
    (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤
      (11 : ℝ) / 5 := by
  have h := contributionSplitWitnessPackage.tail_tsum_le_prefix_add_tailBound
  norm_num [contributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit] at h ⊢



theorem contributionSplitWitnessPackage_tailCertifiedTotalBound_eq :
    contributionSplitWitnessPackage.tailCertifiedTotalBound = (11 : ℝ) / 5 := by
  norm_num [FiniteWitnessPackage.tailCertifiedTotalBound,
    FiniteWitnessPackage.tailPrefixSum, FiniteWitnessPackage.tailBudget,
    contributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit]



theorem contributionSplitWitnessPackage_tail_tsum_le_certifiedTotalBound :
    (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤
      contributionSplitWitnessPackage.tailCertifiedTotalBound :=
  contributionSplitWitnessPackage.tail_tsum_le_certifiedTotalBound



theorem contributionSplitWitnessPackage_tail_tsum_le_three_from_totalBound :
    (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤
      (3 : ℝ) :=
  contributionSplitWitnessPackage.tail_tsum_le_of_certifiedTotalBound_le
    (by
      rw [contributionSplitWitnessPackage_tailCertifiedTotalBound_eq]
      norm_num)



theorem contributionSplitWitnessPackage_tailTotalTsum_le_certifiedTotalBound :
    contributionSplitWitnessPackage.tailTotalTsum ≤
      contributionSplitWitnessPackage.tailCertifiedTotalBound :=
  contributionSplitWitnessPackage.tailTotalTsum_le_certifiedTotalBound



theorem contributionSplitWitnessPackage_tailTotalTsum_split :
    contributionSplitWitnessPackage.tailTotalTsum =
      contributionSplitWitnessPackage.tailPrefixSum +
        contributionSplitWitnessPackage.tailRemainderSum :=
  contributionSplitWitnessPackage.tailTotalTsum_eq_prefix_add_remainder



noncomputable def contributionSplitWitnessPackageRelaxedTailBudget :
    FiniteWitnessPackage (α := Fin 2) (ToyCriticalModel exampleScale 3) :=
  contributionSplitWitnessPackage.with_larger_tailBudget
    (tailBound' := (3 : ℝ))
    (by
      norm_num [FiniteWitnessPackage.tailBudget, contributionSplitWitnessPackage,
        FiniteWitnessPackage.ofContributionSplitFiniteSupport,
        ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn])



theorem contributionSplitWitnessPackageRelaxedTailBudget_totalBound_eq :
    contributionSplitWitnessPackageRelaxedTailBudget.tailCertifiedTotalBound =
      (3 : ℝ) := by
  norm_num [contributionSplitWitnessPackageRelaxedTailBudget,
    FiniteWitnessPackage.with_larger_tailBudget,
    TailSummability.FiniteSupportCertificate.with_larger_tailBound,
    FiniteWitnessPackage.tailCertifiedTotalBound,
    FiniteWitnessPackage.tailPrefixSum, FiniteWitnessPackage.tailBudget,
    contributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]



theorem contributionSplitWitnessPackage_tail_tsum_le_three :
    (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤
      (3 : ℝ) := by
  have h :=
    contributionSplitWitnessPackage.tail_tsum_le_prefix_add_of_tailBudget_le
      (tailBound' := (3 : ℝ))
      (by
        norm_num [FiniteWitnessPackage.tailBudget, contributionSplitWitnessPackage,
          FiniteWitnessPackage.ofContributionSplitFiniteSupport,
          ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn])
  have hprefix : contributionSplitWitnessPackage.tailPrefixSum = 0 := by
    norm_num [FiniteWitnessPackage.tailPrefixSum, contributionSplitWitnessPackage,
      FiniteWitnessPackage.ofContributionSplitFiniteSupport,
      ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
      TailSummabilityExample.exampleSplit]
  simpa [hprefix] using h



noncomputable def contributionSplitWitnessPackageCoarserTailEnvelope :
    FiniteWitnessPackage (α := Fin 2) (ToyCriticalModel exampleScale 3) :=
  contributionSplitWitnessPackage.with_tailEnvelope_and_tailBudget
    (fun _ : Fin 2 => (3 : ℝ) / 2)
    (tailBound' := (3 : ℝ))
    (by
      intro a ha hprefix
      norm_num)
    (by
      intro a ha hprefix
      norm_num [contributionSplitWitnessPackage,
        FiniteWitnessPackage.ofContributionSplitFiniteSupport,
        ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
        TailSummabilityExample.exampleSplit])
    (by
      norm_num [contributionSplitWitnessPackage,
        FiniteWitnessPackage.ofContributionSplitFiniteSupport,
        ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn])



theorem contributionSplitWitnessPackageCoarserTailEnvelope_totalBound_eq :
    contributionSplitWitnessPackageCoarserTailEnvelope.tailCertifiedTotalBound =
      (3 : ℝ) := by
  norm_num [contributionSplitWitnessPackageCoarserTailEnvelope,
    FiniteWitnessPackage.with_tailEnvelope_and_tailBudget,
    TailSummability.FiniteSupportCertificate.with_tailEnvelope_and_tailBound,
    FiniteWitnessPackage.tailCertifiedTotalBound,
    FiniteWitnessPackage.tailPrefixSum, FiniteWitnessPackage.tailBudget,
    contributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit]



theorem contributionSplitWitnessPackageCoarserTailEnvelope_certificate_eq :
    contributionSplitWitnessPackageCoarserTailEnvelope.certificate =
      contributionSplitWitnessPackage.certificate := by
  simp [contributionSplitWitnessPackageCoarserTailEnvelope]



theorem hierarchicalContributionSplitWitnessPackage_tail_bound_concrete :
    (∑' a, hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) ≤
      (11 : ℝ) / 5 := by
  have h := hierarchicalContributionSplitWitnessPackage.tail_tsum_le_prefix_add_tailBound
  norm_num [hierarchicalContributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit] at h ⊢



theorem hierarchicalContributionSplitWitnessPackage_tailCertifiedTotalBound_eq :
    hierarchicalContributionSplitWitnessPackage.tailCertifiedTotalBound =
      (11 : ℝ) / 5 := by
  norm_num [FiniteWitnessPackage.tailCertifiedTotalBound,
    FiniteWitnessPackage.tailPrefixSum, FiniteWitnessPackage.tailBudget,
    hierarchicalContributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit]



theorem hierarchicalContributionSplitWitnessPackage_tail_tsum_le_certifiedTotalBound :
    (∑' a, hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) ≤
      hierarchicalContributionSplitWitnessPackage.tailCertifiedTotalBound :=
  hierarchicalContributionSplitWitnessPackage.tail_tsum_le_certifiedTotalBound



theorem hierarchicalContributionSplitWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid correlationLength :=
  hierarchicalContributionSplitWitnessPackage.valid_of_bridge hbridge



theorem hierarchicalContributionSplitWitnessPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu HierarchicalModel correlationLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent :=
  hierarchicalContributionSplitWitnessPackage.hasCriticalNu_of_bridge hbridge



theorem
    hierarchicalContributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu HierarchicalModel correlationLength
        hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent) :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      correlationLength :=
  hierarchicalContributionSplitWitnessPackage.rgToExponentBridge_of_hasCriticalNu
    hν



theorem hierarchicalContributionSplitWitnessPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu HierarchicalModel correlationLength
        hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent) :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid
      correlationLength :=
  hierarchicalContributionSplitWitnessPackage.valid_of_hasCriticalNu hν

end FiniteWitnessPackageExample
end Exact3D
end StatMech
