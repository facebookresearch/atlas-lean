/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.InfiniteTailMaskedTableWitnessPackage
import Code.Exact3D.InfiniteTailSummabilityExample
import Code.Exact3D.FiniteWitnessPackageExample

open scoped BigOperators









namespace StatMech
namespace Exact3D
namespace InfiniteTailMaskedTableWitnessPackageExample


noncomputable def geometricSplit : ContributionSplit ℕ where
  finiteContribution := fun _ => 0
  tailContribution := InfiniteTailSummabilityExample.geometricHalfTailWeight
  totalContribution := InfiniteTailSummabilityExample.geometricHalfTailWeight


def zeroTable : RatInterval.CaseTable Unit where
  cases := Finset.univ
  interval := fun _ => RatInterval.point 0


def zeroClassifier (_ : ℕ) : Unit := ()


theorem geometricSplit_additive : geometricSplit.Additive := by
  intro n
  simp [geometricSplit]


theorem geometricSplit_total_nonneg :
    ∀ n : ℕ, 0 ≤ geometricSplit.totalContribution n :=
  InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg


theorem zeroFiniteTableUpperBound :
    FiniteTableUpperBound zeroTable zeroClassifier
      geometricSplit.finiteContribution 0 where
  covers := by
    intro n
    simp [zeroTable, zeroClassifier]
  sound := by
    intro n
    norm_num [RatInterval.CaseTable.Sound, zeroTable, zeroClassifier,
      geometricSplit, RatInterval.point, RatInterval.MemR]
  intervalUpper_le := by
    intro c _
    cases c
    norm_num [zeroTable, RatInterval.point]


theorem geometricTailEnvelopeOnPrefix :
    geometricSplit.TailEnvelopeOn ({0} : Finset ℕ)
      InfiniteTailSummabilityExample.geometricHalfTailWeight := by
  intro n _
  exact le_rfl


theorem geometricPrefixTailEnvelopeSum_le_one :
    (∑ n ∈ ({0} : Finset ℕ),
      InfiniteTailSummabilityExample.geometricHalfTailWeight n) ≤ 1 := by
  norm_num [InfiniteTailSummabilityExample.geometricHalfTailWeight]


theorem geometricSplit_finite_zero_off_prefix :
    ∀ n : ℕ, n ∉ ({0} : Finset ℕ) →
      geometricSplit.finiteContribution n = 0 := by
  intro n _
  rfl




noncomputable def geometricMaskedTableWitnessPackage :
    InfiniteTailMaskedTableWitnessPackage (Case := Unit) (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) where
  nStable := 1
  scale := FiniteWitnessPackageExample.exampleScale
  thermal := 3
  thermal_gt_one := by norm_num
  stable := FiniteWitnessPackageExample.stableZeroWitness
  S := geometricSplit
  finitePrefix := {0}
  table := zeroTable
  classify := zeroClassifier
  finiteBound := 0
  prefixTailBound := 1
  tailBound := 1
  tailEnvelope := InfiniteTailSummabilityExample.geometricHalfTailWeight
  total_nonneg := geometricSplit_total_nonneg
  additive := geometricSplit_additive
  finiteTable := zeroFiniteTableUpperBound
  tailEnvelopeOnPrefix := geometricTailEnvelopeOnPrefix
  prefixTailEnvelopeSum_le := geometricPrefixTailEnvelopeSum_le_one
  finite_zero_off_prefix := geometricSplit_finite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := by
    intro n _
    exact InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg n
  tail_le_tailEnvelope_off_prefix := by
    intro _ _
    exact le_rfl
  summable_masked_tailEnvelope := by
    refine
      InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_summable.congr
        ?_
    intro n
    simp [InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight]
  masked_tailEnvelope_tsum_le := by
    convert
      InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_tsum_le_one
      using 1


theorem geometricMaskedTableWitnessPackage_finiteChecks :
    geometricMaskedTableWitnessPackage.certificate.FiniteChecks :=
  geometricMaskedTableWitnessPackage.finiteChecks


theorem geometricMaskedTableWitnessPackage_tailBudget_eq_one :
    geometricMaskedTableWitnessPackage.tailBudget = 1 :=
  rfl


theorem geometricMaskedTableWitnessPackage_tableCertifiedTotalBound_eq_two :
    geometricMaskedTableWitnessPackage.tableCertifiedTotalBound = 2 := by
  norm_num [geometricMaskedTableWitnessPackage,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]



theorem geometricMaskedTableWitnessPackage_tailTotalTsum_le_two :
    geometricMaskedTableWitnessPackage.tailTotalTsum ≤ 2 := by
  rw [← geometricMaskedTableWitnessPackage_tableCertifiedTotalBound_eq_two]
  exact
    geometricMaskedTableWitnessPackage.tailTotalTsum_le_tableCertifiedTotalBound



theorem geometricMaskedTableWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricMaskedTableWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    geometricMaskedTableWitnessPackage.certificate.Valid correlationLength :=
  geometricMaskedTableWitnessPackage.valid_of_bridge hbridge

end InfiniteTailMaskedTableWitnessPackageExample

end Exact3D
end StatMech
