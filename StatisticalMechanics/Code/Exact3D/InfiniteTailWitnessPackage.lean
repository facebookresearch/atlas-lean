/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FiniteWitnessPackage
import Code.Exact3D.InfiniteTailSummability

open scoped BigOperators









namespace StatMech
namespace Exact3D




structure InfiniteTailWitnessPackage {ι α : Type*} [DecidableEq α]
    (M : CriticalModel ι) where
  nStable : ℕ
  scale : BlockScale
  thermal : ℝ
  thermal_gt_one : 1 < thermal
  stable : FiniteStableWitness nStable
  tailCertificate : TailSummability.InfiniteTailCertificate α

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}



noncomputable def ofFiniteWitnessPackage
    (W : FiniteWitnessPackage (α := α) M) :
    InfiniteTailWitnessPackage (α := α) M where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  tailCertificate := W.tailCertificate.toInfiniteTailCertificate





noncomputable def ofTailEnvelope
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (finitePrefix : Finset α) (weight tailEnvelope : α → ℝ)
    {tailBound : ℝ}
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope a)
    (hweight_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
    (hsummable_tailEnvelope : Summable tailEnvelope)
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope a) ≤ tailBound) :
    InfiniteTailWitnessPackage (α := α) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  tailCertificate :=
    TailSummability.InfiniteTailCertificate.of_tailEnvelope
      finitePrefix weight tailEnvelope hweight_nonneg henvelope_nonneg
      hweight_le_tailEnvelope hsummable_tailEnvelope htailEnvelope_tsum_le





noncomputable def ofMaskedTailEnvelope
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (finitePrefix : Finset α) (weight tailEnvelope : α → ℝ)
    {tailBound : ℝ}
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (henvelope_nonneg_off :
      ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (hweight_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    InfiniteTailWitnessPackage (α := α) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  tailCertificate :=
    TailSummability.InfiniteTailCertificate.of_masked_tailEnvelope
      finitePrefix weight tailEnvelope hweight_nonneg henvelope_nonneg_off
      hweight_le_tailEnvelope hsummable_masked hmasked_tsum_le






noncomputable def ofContributionSplitInfiniteTail
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit α) (finitePrefix : Finset α)
    (totalEnvelope : α → ℝ) {tailBound : ℝ}
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (henvelope_nonneg : ∀ a, 0 ≤ totalEnvelope a)
    (htotal_le_totalEnvelope :
      ∀ a, a ∉ finitePrefix → S.totalContribution a ≤ totalEnvelope a)
    (hsummable_totalEnvelope : Summable totalEnvelope)
    (htotalEnvelope_tsum_le : (∑' a, totalEnvelope a) ≤ tailBound) :
    InfiniteTailWitnessPackage (α := α) M :=
  ofTailEnvelope M scale hthermal stable finitePrefix S.totalContribution
    totalEnvelope htotal_nonneg henvelope_nonneg htotal_le_totalEnvelope
    hsummable_totalEnvelope htotalEnvelope_tsum_le




noncomputable def ofContributionSplitTailEnvelope
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit α) (finitePrefix : Finset α)
    (tailEnvelope : α → ℝ) {tailBound : ℝ}
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_tailEnvelope : Summable tailEnvelope)
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope a) ≤ tailBound) :
    InfiniteTailWitnessPackage (α := α) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  tailCertificate :=
    S.infiniteTailCertificate_of_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le




noncomputable def ofContributionSplitMaskedTailEnvelope
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit α) (finitePrefix : Finset α)
    (tailEnvelope : α → ℝ) {tailBound : ℝ}
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg_off :
      ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    InfiniteTailWitnessPackage (α := α) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  tailCertificate :=
    S.infiniteTailCertificate_of_masked_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le


abbrev State (W : InfiniteTailWitnessPackage (α := α) M) : Type :=
  ℝ × (Fin W.nStable → ℝ)


abbrev hamiltonian (W : InfiniteTailWitnessPackage (α := α) M) :
    EffectiveHamiltonian where
  carrier := W.State



noncomputable def rgMap (W : InfiniteTailWitnessPackage (α := α) M) :
    BlockSpinMap W.hamiltonian where
  scale := W.scale
  map := fun x => (W.thermal * x.1, W.stable.map x.2)


@[simp] theorem rgMap_scale
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.rgMap.scale = W.scale :=
  rfl



noncomputable def fixedPoint (W : InfiniteTailWitnessPackage (α := α) M) :
    W.State :=
  (0, W.stable.fixedPoint)


theorem fixedPoint_eq (W : InfiniteTailWitnessPackage (α := α) M) :
    W.rgMap.map W.fixedPoint = W.fixedPoint := by
  apply Prod.ext
  · simp [rgMap, fixedPoint]
  · simpa [rgMap, fixedPoint] using W.stable.fixedPoint_isFixed


noncomputable def fixedPointData
    (W : InfiniteTailWitnessPackage (α := α) M) :
    RGFixedPointData W.hamiltonian W.rgMap where
  fixedPoint := W.fixedPoint
  fixedPoint_eq := W.fixedPoint_eq
  thermalEigenvalue := W.thermal
  thermal_gt_one := W.thermal_gt_one


noncomputable def certificate
    (W : InfiniteTailWitnessPackage (α := α) M) :
    RGCertificate M where
  H := W.hamiltonian
  R := W.rgMap
  fixedPointData := W.fixedPointData


@[simp] theorem certificate_scale_eq
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.scale = W.scale :=
  rfl


@[simp] theorem certificate_thermalEigenvalue_eq
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.thermalEigenvalue = W.thermal :=
  rfl


@[simp] theorem certificate_fixedPoint_eq
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.fixedPointData.fixedPoint = W.fixedPoint :=
  rfl



theorem certificate_predictedExponent_eq
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.predictedExponent = predictedNu W.scale W.thermal :=
  rfl




def retarget {κ : Type*} (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) : InfiniteTailWitnessPackage (α := α) N where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  tailCertificate := W.tailCertificate

@[simp] theorem retarget_certificate {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).certificate = W.certificate.retarget N :=
  rfl


@[simp] theorem ofFiniteWitnessPackage_certificate
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).certificate = W.certificate :=
  rfl



theorem ofFiniteWitnessPackage_rgToExponentBridge
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (ofFiniteWitnessPackage W).certificate.RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem ofFiniteWitnessPackage_valid
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (ofFiniteWitnessPackage W).certificate.Valid correlationLength := by
  simpa using hvalid



theorem ofFiniteWitnessPackage_hasCriticalNu
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (ofFiniteWitnessPackage W).certificate.predictedExponent := by
  simpa using hν

@[simp] theorem ofFiniteWitnessPackage_retarget {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (ofFiniteWitnessPackage W).retarget N =
      ofFiniteWitnessPackage (W.retarget N) :=
  rfl



theorem retarget_rgToExponentBridge {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    (W.retarget N).certificate.RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc



theorem retarget_valid {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength)
    (hβc : M.betaC = N.betaC) :
    (W.retarget N).certificate.Valid correlationLength := by
  simpa using hvalid.retarget hβc



theorem retarget_hasCriticalNu {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength
      ((W.retarget N).certificate).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc



theorem retarget_rgToExponentBridge_iff {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    W.certificate.RGToExponentBridge correlationLength ↔
      (W.retarget N).certificate.RGToExponentBridge correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := W.certificate) (N := N) hβc)



theorem retarget_valid_iff {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    W.certificate.Valid correlationLength ↔
      (W.retarget N).certificate.Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := W.certificate) (N := N) hβc)



theorem retarget_hasCriticalNu_iff {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent ↔
      HasCriticalNu N correlationLength
        ((W.retarget N).certificate).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := W.certificate) (N := N) hβc)


theorem fixedPointEnclosure (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.FixedPointEnclosure := by
  simpa [certificate, fixedPointData, RGCertificate.FixedPointEnclosure] using
    W.fixedPoint_eq



theorem finiteChecks (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.FiniteChecks where
  finiteCaseChecks := trivial
  tailBounds := trivial
  fixedPointEnclosure := W.fixedPointEnclosure
  linearizationEnclosure := W.certificate.linearizationEnclosure_of_thermal_gt_one
  hyperbolicSplitting := W.certificate.hyperbolicSplitting_of_thermal_gt_one
  orbitEntry := trivial



theorem finiteCaseChecks (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.FiniteCaseChecks :=
  W.finiteChecks.finiteCaseChecks



theorem tailBounds (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.TailBounds :=
  W.finiteChecks.tailBounds



theorem linearizationEnclosure
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.LinearizationEnclosure :=
  W.finiteChecks.linearizationEnclosure



theorem hyperbolicSplitting
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.HyperbolicSplitting :=
  W.finiteChecks.hyperbolicSplitting



theorem orbitEntry (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.OrbitEntry :=
  W.finiteChecks.orbitEntry



noncomputable def tailPrefixSum
    (W : InfiniteTailWitnessPackage (α := α) M) : ℝ :=
  W.tailCertificate.prefixSum


def tailBudget (W : InfiniteTailWitnessPackage (α := α) M) : ℝ :=
  W.tailCertificate.tailBound



noncomputable def tailCertifiedTotalBound
    (W : InfiniteTailWitnessPackage (α := α) M) : ℝ :=
  W.tailPrefixSum + W.tailBudget



def tailContribution
    (W : InfiniteTailWitnessPackage (α := α) M) : α → ℝ :=
  W.tailCertificate.weight


theorem summable_tailContribution
    (W : InfiniteTailWitnessPackage (α := α) M) :
    Summable W.tailContribution := by
  simpa [tailContribution] using W.tailCertificate.summable_weight


theorem summable_tailWeight
    (W : InfiniteTailWitnessPackage (α := α) M) :
    Summable W.tailCertificate.tailWeight :=
  W.tailCertificate.summable_tail


noncomputable def tailTotalTsum
    (W : InfiniteTailWitnessPackage (α := α) M) : ℝ :=
  ∑' a, W.tailContribution a



noncomputable def tailRemainderSum
    (W : InfiniteTailWitnessPackage (α := α) M) : ℝ :=
  ∑' a, W.tailCertificate.tailWeight a


@[simp] theorem retarget_tailPrefixSum {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailPrefixSum = W.tailPrefixSum :=
  rfl


@[simp] theorem retarget_tailBudget {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailBudget = W.tailBudget :=
  rfl


@[simp] theorem retarget_tailCertifiedTotalBound {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailCertifiedTotalBound =
      W.tailCertifiedTotalBound :=
  rfl


@[simp] theorem retarget_tailContribution {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailContribution = W.tailContribution :=
  rfl


@[simp] theorem retarget_tailTotalTsum {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailTotalTsum = W.tailTotalTsum :=
  rfl


@[simp] theorem retarget_tailRemainderSum {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailRemainderSum = W.tailRemainderSum :=
  rfl


@[simp] theorem retarget_predictedExponent {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).certificate.predictedExponent =
      W.certificate.predictedExponent :=
  rfl


theorem tailTotalTsum_eq_tsum
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.tailTotalTsum = ∑' a, W.tailCertificate.weight a :=
  rfl


theorem tailContribution_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) (a : α) :
    0 ≤ W.tailContribution a :=
  W.tailCertificate.weight_nonneg a


theorem tailContribution_decomposition
    (W : InfiniteTailWitnessPackage (α := α) M) (a : α) :
    W.tailContribution a =
      W.tailCertificate.prefixWeight a + W.tailCertificate.tailWeight a := by
  simpa [tailContribution] using W.tailCertificate.decomposition a



theorem tailTotalTsum_eq_prefix_add_remainder
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.tailTotalTsum = W.tailPrefixSum + W.tailRemainderSum := by
  simpa [tailTotalTsum, tailContribution, tailPrefixSum,
    tailRemainderSum] using
    W.tailCertificate.tsum_weight_eq_prefixSum_add_tail



theorem tailRemainderSum_le_tailBudget
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.tailRemainderSum ≤ W.tailBudget := by
  simpa [tailRemainderSum, tailBudget] using
    W.tailCertificate.tail_tsum_le


theorem tailRemainderSum_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ W.tailRemainderSum := by
  simpa [tailRemainderSum] using
    W.tailCertificate.tail_tsum_nonneg



theorem tailRemainderSum_eq_zero_of_tailBudget_eq_zero
    (W : InfiniteTailWitnessPackage (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailRemainderSum = 0 :=
  le_antisymm (by simpa [hbudget] using W.tailRemainderSum_le_tailBudget)
    W.tailRemainderSum_nonneg



theorem tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero
    (W : InfiniteTailWitnessPackage (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailTotalTsum = W.tailPrefixSum := by
  rw [W.tailTotalTsum_eq_prefix_add_remainder,
    W.tailRemainderSum_eq_zero_of_tailBudget_eq_zero hbudget, add_zero]


theorem tail_tsum_le_prefix_add_tailBound
    (W : InfiniteTailWitnessPackage (α := α) M) :
    (∑' a, W.tailCertificate.weight a) ≤
      W.tailCertificate.prefixSum + W.tailCertificate.tailBound :=
  W.tailCertificate.tsum_weight_le_prefixSum_add_tailBound



theorem tail_tsum_le_certifiedTotalBound
    (W : InfiniteTailWitnessPackage (α := α) M) :
    (∑' a, W.tailCertificate.weight a) ≤ W.tailCertifiedTotalBound := by
  simpa [tailCertifiedTotalBound, tailPrefixSum, tailBudget] using
    W.tail_tsum_le_prefix_add_tailBound



theorem tail_tsum_le_of_certifiedTotalBound_le
    (W : InfiniteTailWitnessPackage (α := α) M) {B : ℝ}
    (hB : W.tailCertifiedTotalBound ≤ B) :
    (∑' a, W.tailCertificate.weight a) ≤ B :=
  le_trans W.tail_tsum_le_certifiedTotalBound hB


theorem tailTotalTsum_le_certifiedTotalBound
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.tailTotalTsum ≤ W.tailCertifiedTotalBound := by
  simpa [tailTotalTsum, tailContribution] using
    W.tail_tsum_le_certifiedTotalBound



theorem tailTotalTsum_le_of_certifiedTotalBound_le
    (W : InfiniteTailWitnessPackage (α := α) M) {B : ℝ}
    (hB : W.tailCertifiedTotalBound ≤ B) :
    W.tailTotalTsum ≤ B :=
  le_trans W.tailTotalTsum_le_certifiedTotalBound hB



theorem tail_tsum_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (∑' a, W.tailCertificate.weight a) ≤
      W.tailPrefixSum + tailBound' := by
  calc
    (∑' a, W.tailCertificate.weight a) ≤
        W.tailPrefixSum + W.tailBudget := by
      simpa [tailPrefixSum, tailBudget] using
        W.tail_tsum_le_prefix_add_tailBound
    _ ≤ W.tailPrefixSum + tailBound' :=
      add_le_add (le_refl W.tailPrefixSum) hle



theorem tailTotalTsum_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailTotalTsum ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailTotalTsum, tailContribution] using
    W.tail_tsum_le_prefix_add_of_tailBudget_le hle


theorem tailRemainderSum_le_of_tailBudget_le
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailRemainderSum ≤ tailBound' :=
  le_trans W.tailRemainderSum_le_tailBudget hle


theorem tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailCertifiedTotalBound ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailCertifiedTotalBound] using
    add_le_add (le_refl W.tailPrefixSum) hle

@[simp] theorem ofFiniteWitnessPackage_tailPrefixSum
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailPrefixSum = W.tailPrefixSum := by
  rfl

@[simp] theorem ofFiniteWitnessPackage_tailBudget
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailBudget = W.tailBudget := by
  rfl

@[simp] theorem ofFiniteWitnessPackage_tailCertifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailCertifiedTotalBound =
      W.tailCertifiedTotalBound := by
  rfl

@[simp] theorem ofFiniteWitnessPackage_tailContribution
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailContribution = W.tailContribution :=
  rfl

@[simp] theorem ofFiniteWitnessPackage_tailTotalTsum
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailTotalTsum = W.tailTotalTsum :=
  rfl



theorem ofFiniteWitnessPackage_tailRemainderSum
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailRemainderSum = W.tailRemainderSum := by
  have hInf :=
    (ofFiniteWitnessPackage W).tailTotalTsum_eq_prefix_add_remainder
  have hFin := W.tailTotalTsum_eq_prefix_add_remainder
  rw [ofFiniteWitnessPackage_tailTotalTsum,
    ofFiniteWitnessPackage_tailPrefixSum] at hInf
  linarith


theorem tailPrefixSum_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ W.tailPrefixSum := by
  simpa [tailPrefixSum] using W.tailCertificate.prefixSum_nonneg


theorem tailBudget_nonneg (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ W.tailBudget := by
  simpa [tailBudget] using W.tailCertificate.tailBound_nonneg


theorem tailCertifiedTotalBound_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ W.tailCertifiedTotalBound :=
  add_nonneg W.tailPrefixSum_nonneg W.tailBudget_nonneg


theorem tail_tsum_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ ∑' a, W.tailCertificate.weight a :=
  W.tailCertificate.tsum_weight_nonneg


theorem tailTotalTsum_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ W.tailTotalTsum := by
  simpa [tailTotalTsum, tailContribution] using W.tail_tsum_nonneg


def with_larger_tailBudget
    (W : InfiniteTailWitnessPackage (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    InfiniteTailWitnessPackage (α := α) M where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  tailCertificate :=
    W.tailCertificate.with_larger_tailBound (by
      simpa [tailBudget] using hle)

@[simp] theorem with_larger_tailBudget_tailBudget
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailBudget = tailBound' :=
  rfl

@[simp] theorem with_larger_tailBudget_tailPrefixSum
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem with_larger_tailBudget_tailCertifiedTotalBound
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailCertifiedTotalBound =
      W.tailPrefixSum + tailBound' :=
  rfl


@[simp] theorem with_larger_tailBudget_tailContribution
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailContribution =
      W.tailContribution :=
  rfl


@[simp] theorem with_larger_tailBudget_tailTotalTsum
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailTotalTsum =
      W.tailTotalTsum :=
  rfl


@[simp] theorem with_larger_tailBudget_tailRemainderSum
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailRemainderSum =
      W.tailRemainderSum :=
  rfl

@[simp] theorem with_larger_tailBudget_certificate
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).certificate = W.certificate :=
  rfl



theorem with_larger_tailBudget_rgToExponentBridge
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_larger_tailBudget hle).certificate.RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem with_larger_tailBudget_valid
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_larger_tailBudget hle).certificate.Valid correlationLength := by
  simpa using hvalid



theorem with_larger_tailBudget_hasCriticalNu
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_larger_tailBudget hle).certificate.predictedExponent := by
  simpa using hν


theorem stable_fixedPoint_mem
    (W : InfiniteTailWitnessPackage (α := α) M) :
    FiniteContraction.ClosedBall
      W.stable.contraction.center W.stable.contraction.radius
      W.stable.fixedPoint :=
  W.stable.fixedPoint_mem


theorem stable_exists_unique_fixedPoint
    (W : InfiniteTailWitnessPackage (α := α) M) :
    ∃! p : Fin W.nStable → ℝ, W.stable.map p = p :=
  W.stable.exists_unique_fixedPoint



theorem valid_of_bridge
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.finiteChecks.valid_of_bridge hbridge



theorem hasCriticalNu_of_bridge
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_bridge hbridge).hasCriticalNu



theorem rgToExponentBridge_of_bridge_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred



theorem valid_of_bridge_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_bridge_congr_predictedExponent hpred hbridge)



theorem hasCriticalNu_of_bridge_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_bridge_congr_predictedExponent hpred hbridge).hasCriticalNu



theorem rgToExponentBridge_of_hasCriticalNu
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.RGToExponentBridge correlationLength := by
  simpa [RGCertificate.RGToExponentBridge] using hν



theorem valid_of_hasCriticalNu
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_hasCriticalNu hν)

end InfiniteTailWitnessPackage

end Exact3D
end StatMech
