/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.InfiniteTailTableWitnessPackage

open scoped BigOperators










namespace StatMech
namespace Exact3D





structure InfiniteTailMaskedTableWitnessPackage {ι Case α : Type*}
    [DecidableEq Case] [DecidableEq α] (M : CriticalModel ι) where
  nStable : ℕ
  scale : BlockScale
  thermal : ℝ
  thermal_gt_one : 1 < thermal
  stable : FiniteStableWitness nStable
  S : ContributionSplit α
  finitePrefix : Finset α
  table : RatInterval.CaseTable Case
  classify : α → Case
  finiteBound : ℝ
  prefixTailBound : ℝ
  tailBound : ℝ
  tailEnvelope : α → ℝ
  total_nonneg : ∀ a, 0 ≤ S.totalContribution a
  additive : S.Additive
  finiteTable :
    FiniteTableUpperBound table classify S.finiteContribution finiteBound
  tailEnvelopeOnPrefix : S.TailEnvelopeOn finitePrefix tailEnvelope
  prefixTailEnvelopeSum_le :
    (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound
  finite_zero_off_prefix :
    ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0
  tailEnvelope_nonneg_off_prefix :
    ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a
  tail_le_tailEnvelope_off_prefix :
    ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a
  summable_masked_tailEnvelope :
    Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a)
  masked_tailEnvelope_tsum_le :
    (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤ tailBound

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]
variable {M : CriticalModel ι}




def retarget {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) N where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  S := W.S
  finitePrefix := W.finitePrefix
  table := W.table
  classify := W.classify
  finiteBound := W.finiteBound
  prefixTailBound := W.prefixTailBound
  tailBound := W.tailBound
  tailEnvelope := W.tailEnvelope
  total_nonneg := W.total_nonneg
  additive := W.additive
  finiteTable := W.finiteTable
  tailEnvelopeOnPrefix := W.tailEnvelopeOnPrefix
  prefixTailEnvelopeSum_le := W.prefixTailEnvelopeSum_le
  finite_zero_off_prefix := W.finite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := W.tailEnvelope_nonneg_off_prefix
  tail_le_tailEnvelope_off_prefix := W.tail_le_tailEnvelope_off_prefix
  summable_masked_tailEnvelope := W.summable_masked_tailEnvelope
  masked_tailEnvelope_tsum_le := W.masked_tailEnvelope_tsum_le



noncomputable def toWitnessPackage
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    InfiniteTailWitnessPackage (α := α) M :=
  InfiniteTailWitnessPackage.ofContributionSplitMaskedTailEnvelope
    M W.scale W.thermal_gt_one W.stable W.S W.finitePrefix W.tailEnvelope
    W.total_nonneg W.additive W.finite_zero_off_prefix
    W.tailEnvelope_nonneg_off_prefix W.tail_le_tailEnvelope_off_prefix
    W.summable_masked_tailEnvelope W.masked_tailEnvelope_tsum_le

@[simp] theorem retarget_toWitnessPackage {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).toWitnessPackage = W.toWitnessPackage.retarget N :=
  rfl


noncomputable def certificate
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    RGCertificate M :=
  W.toWitnessPackage.certificate

@[simp] theorem certificate_scale_eq
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.scale = W.scale :=
  rfl

@[simp] theorem certificate_thermalEigenvalue_eq
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.thermalEigenvalue = W.thermal :=
  rfl



theorem certificate_predictedExponent_eq
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.predictedExponent = predictedNu W.scale W.thermal :=
  rfl

@[simp] theorem retarget_certificate {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).certificate = W.certificate.retarget N :=
  rfl

@[simp] theorem retarget_finiteBound {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).finiteBound = W.finiteBound :=
  rfl

@[simp] theorem retarget_prefixTailBound {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).prefixTailBound = W.prefixTailBound :=
  rfl

@[simp] theorem retarget_tailBound {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailBound = W.tailBound :=
  rfl



theorem retarget_rgToExponentBridge {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    (W.retarget N).certificate.RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc



theorem retarget_valid {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength)
    (hβc : M.betaC = N.betaC) :
    (W.retarget N).certificate.Valid correlationLength := by
  simpa using hvalid.retarget hβc



theorem retarget_hasCriticalNu {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength
      ((W.retarget N).certificate).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc



theorem retarget_rgToExponentBridge_iff {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    W.certificate.RGToExponentBridge correlationLength ↔
      (W.retarget N).certificate.RGToExponentBridge correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := W.certificate) (N := N) hβc)



theorem retarget_valid_iff {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    W.certificate.Valid correlationLength ↔
      (W.retarget N).certificate.Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := W.certificate) (N := N) hβc)



theorem retarget_hasCriticalNu_iff {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent ↔
      HasCriticalNu N correlationLength
        ((W.retarget N).certificate).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := W.certificate) (N := N) hβc)


theorem finiteChecks
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.FiniteChecks :=
  W.toWitnessPackage.finiteChecks


theorem finiteCaseChecks
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.FiniteCaseChecks :=
  W.toWitnessPackage.finiteCaseChecks


theorem tailBounds
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.TailBounds :=
  W.toWitnessPackage.tailBounds


theorem fixedPointEnclosure
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.FixedPointEnclosure :=
  W.toWitnessPackage.fixedPointEnclosure


theorem linearizationEnclosure
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.LinearizationEnclosure :=
  W.toWitnessPackage.linearizationEnclosure


theorem hyperbolicSplitting
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.HyperbolicSplitting :=
  W.toWitnessPackage.hyperbolicSplitting


theorem orbitEntry
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.OrbitEntry :=
  W.toWitnessPackage.orbitEntry


noncomputable def tailPrefixSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.toWitnessPackage.tailPrefixSum


noncomputable def tailBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.toWitnessPackage.tailBudget

@[simp] theorem tailBudget_eq_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailBudget = W.tailBound :=
  rfl


noncomputable def tailCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.tailPrefixSum + W.tailBudget


noncomputable def tailContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    α → ℝ :=
  W.toWitnessPackage.tailContribution


noncomputable def tailTotalTsum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.toWitnessPackage.tailTotalTsum


noncomputable def tailRemainderSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.toWitnessPackage.tailRemainderSum

@[simp] theorem retarget_tailPrefixSum {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem retarget_tailBudget {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailBudget = W.tailBudget :=
  rfl

@[simp] theorem retarget_tailCertifiedTotalBound {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailCertifiedTotalBound = W.tailCertifiedTotalBound :=
  rfl

@[simp] theorem retarget_tailContribution {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailContribution = W.tailContribution :=
  rfl

@[simp] theorem retarget_tailTotalTsum {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailTotalTsum = W.tailTotalTsum :=
  rfl

@[simp] theorem retarget_tailRemainderSum {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailRemainderSum = W.tailRemainderSum :=
  rfl

@[simp] theorem retarget_predictedExponent {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).certificate.predictedExponent =
      W.certificate.predictedExponent :=
  rfl


theorem summable_tailContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    Summable W.tailContribution := by
  simpa [tailContribution] using W.toWitnessPackage.summable_tailContribution


theorem tailContribution_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (a : α) :
    0 ≤ W.tailContribution a :=
  W.toWitnessPackage.tailContribution_nonneg a


theorem tailPrefixSum_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailPrefixSum := by
  simpa [tailPrefixSum] using W.toWitnessPackage.tailPrefixSum_nonneg


theorem tailBudget_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailBudget := by
  simpa [tailBudget] using W.toWitnessPackage.tailBudget_nonneg


theorem tailCertifiedTotalBound_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailCertifiedTotalBound := by
  simpa [tailCertifiedTotalBound, tailPrefixSum, tailBudget] using
    W.toWitnessPackage.tailCertifiedTotalBound_nonneg



theorem tailTotalTsum_eq_tsum_totalContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum = ∑' a, W.S.totalContribution a := by
  rfl


theorem tailTotalTsum_eq_tsum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum = ∑' a, W.tailContribution a := by
  rfl



theorem tailTotalTsum_eq_prefix_add_remainder
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum = W.tailPrefixSum + W.tailRemainderSum := by
  simpa [tailTotalTsum, tailPrefixSum, tailRemainderSum] using
    W.toWitnessPackage.tailTotalTsum_eq_prefix_add_remainder


theorem tail_tsum_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ ∑' a, W.tailContribution a := by
  simpa [tailContribution] using W.toWitnessPackage.tail_tsum_nonneg


theorem tailTotalTsum_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailTotalTsum := by
  simpa [tailTotalTsum] using W.toWitnessPackage.tailTotalTsum_nonneg



theorem tail_tsum_le_prefix_add_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tailPrefixSum + W.tailBudget := by
  simpa [tailContribution, tailPrefixSum, tailBudget] using
    W.toWitnessPackage.tail_tsum_le_prefix_add_tailBound



theorem tailRemainderSum_le_tailBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailRemainderSum ≤ W.tailBudget := by
  simpa [tailRemainderSum, tailBudget] using
    W.toWitnessPackage.tailRemainderSum_le_tailBudget


theorem tailRemainderSum_le_of_tailBudget_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    W.tailRemainderSum ≤ tailBound' :=
  le_trans W.tailRemainderSum_le_tailBudget hle


theorem tailRemainderSum_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailRemainderSum := by
  simpa [tailRemainderSum] using
    W.toWitnessPackage.tailRemainderSum_nonneg



theorem tailRemainderSum_eq_zero_of_tailBudget_eq_zero
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailRemainderSum = 0 := by
  have htailBound : W.tailBound = 0 := by
    simpa [tailBudget] using hbudget
  exact
    le_antisymm (by
      simpa [htailBound] using W.tailRemainderSum_le_tailBudget)
      W.tailRemainderSum_nonneg



theorem tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailTotalTsum = W.tailPrefixSum := by
  rw [W.tailTotalTsum_eq_prefix_add_remainder,
    W.tailRemainderSum_eq_zero_of_tailBudget_eq_zero hbudget, add_zero]



theorem tail_tsum_le_certifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tailCertifiedTotalBound := by
  simpa [tailContribution, tailCertifiedTotalBound, tailPrefixSum,
    tailBudget] using W.toWitnessPackage.tail_tsum_le_certifiedTotalBound



theorem tail_tsum_le_of_certifiedTotalBound_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tailCertifiedTotalBound ≤ B) :
    (∑' a, W.tailContribution a) ≤ B :=
  le_trans W.tail_tsum_le_certifiedTotalBound hB



theorem tailTotalTsum_le_certifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum ≤ W.tailCertifiedTotalBound := by
  simpa [tailTotalTsum, tailCertifiedTotalBound, tailPrefixSum, tailBudget] using
    W.toWitnessPackage.tailTotalTsum_le_certifiedTotalBound



theorem tailTotalTsum_le_of_certifiedTotalBound_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tailCertifiedTotalBound ≤ B) :
    W.tailTotalTsum ≤ B :=
  le_trans W.tailTotalTsum_le_certifiedTotalBound hB



theorem tail_tsum_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    (∑' a, W.tailContribution a) ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailContribution, tailPrefixSum, tailBudget] using
    W.toWitnessPackage.tail_tsum_le_prefix_add_of_tailBudget_le hle



theorem tailTotalTsum_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    W.tailTotalTsum ≤ W.tailPrefixSum + tailBound' := by
  simpa [W.tailTotalTsum_eq_tsum] using
    W.tail_tsum_le_prefix_add_of_tailBudget_le hle



theorem tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    W.tailCertifiedTotalBound ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailCertifiedTotalBound] using
    add_le_add (le_refl W.tailPrefixSum) hle


noncomputable def tableFiniteBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  (W.finitePrefix.card : ℝ) * W.finiteBound



noncomputable def tablePrefixBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.tableFiniteBudget + W.prefixTailBound



noncomputable def tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.tablePrefixBudget + W.tailBound

@[simp] theorem tableCertifiedTotalBound_eq
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tableCertifiedTotalBound = W.tablePrefixBudget + W.tailBound :=
  rfl

@[simp] theorem retarget_tableFiniteBudget {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tableFiniteBudget = W.tableFiniteBudget :=
  rfl

@[simp] theorem retarget_tablePrefixBudget {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tablePrefixBudget = W.tablePrefixBudget :=
  rfl

@[simp] theorem retarget_tableCertifiedTotalBound {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tableCertifiedTotalBound =
      W.tableCertifiedTotalBound :=
  rfl





theorem tableCertifiedTotalBound_nonneg_of_component_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (hfinite : 0 ≤ W.finiteBound) (hprefix : 0 ≤ W.prefixTailBound) :
    0 ≤ W.tableCertifiedTotalBound := by
  have hcard : 0 ≤ (W.finitePrefix.card : ℝ) := by positivity
  have hfiniteBudget : 0 ≤ W.tableFiniteBudget := by
    exact mul_nonneg hcard hfinite
  have hprefixBudget : 0 ≤ W.tablePrefixBudget := by
    exact add_nonneg hfiniteBudget hprefix
  exact add_nonneg hprefixBudget (by
    simpa [tailBudget] using W.tailBudget_nonneg)


theorem tableTailBound_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailBound := by
  simpa [tailBudget] using W.tailBudget_nonneg


theorem tableCertifiedTotalBound_le_of_component_bounds
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' prefixTailBound' tailBound' : ℝ}
    (hfinite : W.finiteBound ≤ finiteBound')
    (hprefix : W.prefixTailBound ≤ prefixTailBound')
    (htail : W.tailBound ≤ tailBound') :
    W.tableCertifiedTotalBound ≤
      (W.finitePrefix.card : ℝ) * finiteBound' +
        prefixTailBound' + tailBound' := by
  have hcard : 0 ≤ (W.finitePrefix.card : ℝ) := by positivity
  have hfiniteBudget :
      (W.finitePrefix.card : ℝ) * W.finiteBound ≤
        (W.finitePrefix.card : ℝ) * finiteBound' :=
    mul_le_mul_of_nonneg_left hfinite hcard
  exact add_le_add (add_le_add hfiniteBudget hprefix) htail



theorem tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixBound tailBound' : ℝ}
    (hprefix : W.tablePrefixBudget ≤ prefixBound)
    (htail : W.tailBound ≤ tailBound') :
    W.tableCertifiedTotalBound ≤ prefixBound + tailBound' := by
  simpa [tableCertifiedTotalBound_eq] using add_le_add hprefix htail



theorem tailPrefixSum_le_tablePrefixBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailPrefixSum ≤ W.tablePrefixBudget := by
  simpa [tailPrefixSum, tablePrefixBudget, tableFiniteBudget,
    toWitnessPackage, InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.ofContributionSplitMaskedTailEnvelope,
    ContributionSplit.infiniteTailCertificate_of_masked_tailEnvelope_off_prefix,
    TailSummability.InfiniteTailCertificate.of_masked_tailEnvelope,
    TailSummability.InfiniteTailCertificate.of_tailEnvelope,
    TailSummability.InfiniteTailCertificate.prefixSum] using
    (W.S.total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn
      W.finitePrefix W.tailEnvelope W.additive W.finiteTable
      W.tailEnvelopeOnPrefix W.prefixTailEnvelopeSum_le)



theorem finiteContribution_le_finiteBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (a : α) :
    W.S.finiteContribution a ≤ W.finiteBound :=
  finite_le_of_tableUpperBound W.finiteTable a



theorem tablePrefixBudget_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tablePrefixBudget :=
  le_trans W.tailPrefixSum_nonneg W.tailPrefixSum_le_tablePrefixBudget



theorem tailCertifiedTotalBound_le_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailCertifiedTotalBound ≤ W.tableCertifiedTotalBound := by
  change W.tailPrefixSum + W.tailBudget ≤ W.tablePrefixBudget + W.tailBound
  rw [W.tailBudget_eq_tailBound]
  exact add_le_add W.tailPrefixSum_le_tablePrefixBudget (le_refl W.tailBound)



theorem tail_tsum_le_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tableCertifiedTotalBound :=
  le_trans W.tail_tsum_le_certifiedTotalBound
    W.tailCertifiedTotalBound_le_tableCertifiedTotalBound



theorem tail_tsum_le_of_tableCertifiedTotalBound_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tableCertifiedTotalBound ≤ B) :
    (∑' a, W.tailContribution a) ≤ B :=
  le_trans W.tail_tsum_le_tableCertifiedTotalBound hB



theorem tail_tsum_le_tablePrefixBudget_add_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tablePrefixBudget + W.tailBound := by
  simpa [tableCertifiedTotalBound_eq] using
    W.tail_tsum_le_tableCertifiedTotalBound



theorem tailTotalTsum_le_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum ≤ W.tableCertifiedTotalBound :=
  le_trans W.tailTotalTsum_le_certifiedTotalBound
    W.tailCertifiedTotalBound_le_tableCertifiedTotalBound



theorem tableCertifiedTotalBound_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tableCertifiedTotalBound :=
  le_trans W.tailTotalTsum_nonneg W.tailTotalTsum_le_tableCertifiedTotalBound



theorem tailTotalTsum_le_tablePrefixBudget_add_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum ≤ W.tablePrefixBudget + W.tailBound := by
  simpa [tableCertifiedTotalBound_eq] using
    W.tailTotalTsum_le_tableCertifiedTotalBound



theorem tailTotalTsum_le_of_tableCertifiedTotalBound_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tableCertifiedTotalBound ≤ B) :
    W.tailTotalTsum ≤ B :=
  le_trans W.tailTotalTsum_le_tableCertifiedTotalBound hB





def with_tailEnvelope_and_budgets
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  S := W.S
  finitePrefix := W.finitePrefix
  table := W.table
  classify := W.classify
  finiteBound := W.finiteBound
  prefixTailBound := prefixTailBound'
  tailBound := tailBound'
  tailEnvelope := tailEnvelope'
  total_nonneg := W.total_nonneg
  additive := W.additive
  finiteTable := W.finiteTable
  tailEnvelopeOnPrefix := htailOnPrefix
  prefixTailEnvelopeSum_le := hprefixSum
  finite_zero_off_prefix := W.finite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := henvelope_nonneg_off
  tail_le_tailEnvelope_off_prefix := htail_le_tailEnvelope
  summable_masked_tailEnvelope := hsummable_masked
  masked_tailEnvelope_tsum_le := hmasked_tsum_le





def with_zero_tailEnvelope_and_budgets
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M :=
  W.with_tailEnvelope_and_budgets (fun _ => (0 : ℝ))
    htailOnPrefix
    (by simpa using hprefix_nonneg)
    (by intro _ _; simp)
    htail_nonpos
    (by simp)
    (by simpa using htailBound_nonneg)

@[simp] theorem with_tailEnvelope_and_budgets_finiteBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).finiteBound = W.finiteBound :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_prefixTailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).prefixTailBound = prefixTailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tailBound = tailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailEnvelope
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tailEnvelope = tailEnvelope' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tailBudget = tailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailPrefixSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tailCertifiedTotalBound =
      W.tailPrefixSum + tailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tailContribution = W.tailContribution :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailTotalTsum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tailTotalTsum = W.tailTotalTsum :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tailRemainderSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tailRemainderSum = W.tailRemainderSum :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tableFiniteBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tableFiniteBudget = W.tableFiniteBudget :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tablePrefixBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tablePrefixBudget =
      W.tableFiniteBudget + prefixTailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tableCertifiedTotalBound =
      (W.finitePrefix.card : ℝ) * W.finiteBound +
        prefixTailBound' + tailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_budgets_certificate
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).certificate = W.certificate :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_finiteBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).finiteBound = W.finiteBound :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_prefixTailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).prefixTailBound = prefixTailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailBound = tailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailEnvelope
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailEnvelope = (fun _ => (0 : ℝ)) :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailBudget = tailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailPrefixSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailCertifiedTotalBound =
      W.tailPrefixSum + tailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailTotalTsum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailTotalTsum =
      W.tailTotalTsum :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tailRemainderSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tailRemainderSum =
      W.tailRemainderSum :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tableFiniteBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tableFiniteBudget =
      W.tableFiniteBudget :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tablePrefixBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tablePrefixBudget =
      W.tableFiniteBudget + prefixTailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).tableCertifiedTotalBound =
      (W.finitePrefix.card : ℝ) * W.finiteBound +
        prefixTailBound' + tailBound' :=
  rfl

@[simp] theorem with_zero_tailEnvelope_and_budgets_certificate
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).certificate = W.certificate :=
  rfl




theorem with_tailEnvelope_and_budgets_rgToExponentBridge
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge




theorem with_tailEnvelope_and_budgets_valid
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).certificate.Valid correlationLength := by
  simpa using hvalid




theorem with_tailEnvelope_and_budgets_hasCriticalNu
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum
        henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
        hmasked_tsum_le).certificate.predictedExponent := by
  simpa using hν



theorem with_zero_tailEnvelope_and_budgets_rgToExponentBridge
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge



theorem with_zero_tailEnvelope_and_budgets_valid
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
      htail_nonpos htailBound_nonneg).certificate.Valid
        correlationLength := by
  simpa using hvalid



theorem with_zero_tailEnvelope_and_budgets_hasCriticalNu
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg
        htail_nonpos htailBound_nonneg).certificate.predictedExponent := by
  simpa using hν


def with_larger_finiteBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  S := W.S
  finitePrefix := W.finitePrefix
  table := W.table
  classify := W.classify
  finiteBound := finiteBound'
  prefixTailBound := W.prefixTailBound
  tailBound := W.tailBound
  tailEnvelope := W.tailEnvelope
  total_nonneg := W.total_nonneg
  additive := W.additive
  finiteTable :=
    { covers := W.finiteTable.covers
      sound := W.finiteTable.sound
      intervalUpper_le := fun c hc =>
        le_trans (W.finiteTable.intervalUpper_le c hc) hle }
  tailEnvelopeOnPrefix := W.tailEnvelopeOnPrefix
  prefixTailEnvelopeSum_le := W.prefixTailEnvelopeSum_le
  finite_zero_off_prefix := W.finite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := W.tailEnvelope_nonneg_off_prefix
  tail_le_tailEnvelope_off_prefix := W.tail_le_tailEnvelope_off_prefix
  summable_masked_tailEnvelope := W.summable_masked_tailEnvelope
  masked_tailEnvelope_tsum_le := W.masked_tailEnvelope_tsum_le

@[simp] theorem with_larger_finiteBound_finiteBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).finiteBound = finiteBound' :=
  rfl

@[simp] theorem with_larger_finiteBound_prefixTailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).prefixTailBound =
      W.prefixTailBound :=
  rfl

@[simp] theorem with_larger_finiteBound_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailBound = W.tailBound :=
  rfl

@[simp] theorem with_larger_finiteBound_tailBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailBudget = W.tailBudget :=
  rfl

@[simp] theorem with_larger_finiteBound_tableFiniteBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tableFiniteBudget =
      (W.finitePrefix.card : ℝ) * finiteBound' :=
  rfl

@[simp] theorem with_larger_finiteBound_tablePrefixBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tablePrefixBudget =
      (W.finitePrefix.card : ℝ) * finiteBound' + W.prefixTailBound :=
  rfl

@[simp] theorem with_larger_finiteBound_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tableCertifiedTotalBound =
      (W.finitePrefix.card : ℝ) * finiteBound' +
        W.prefixTailBound + W.tailBound :=
  rfl

@[simp] theorem with_larger_finiteBound_toWitnessPackage
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).toWitnessPackage =
      W.toWitnessPackage :=
  rfl

@[simp] theorem with_larger_finiteBound_certificate
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).certificate = W.certificate :=
  rfl

@[simp] theorem with_larger_finiteBound_tailContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_larger_finiteBound_tailPrefixSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailPrefixSum =
      W.tailPrefixSum :=
  rfl

@[simp] theorem with_larger_finiteBound_tailCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailCertifiedTotalBound =
      W.tailCertifiedTotalBound :=
  rfl

@[simp] theorem with_larger_finiteBound_tailTotalTsum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailTotalTsum =
      W.tailTotalTsum :=
  rfl

@[simp] theorem with_larger_finiteBound_tailRemainderSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
    (W.with_larger_finiteBound hle).tailRemainderSum =
      W.tailRemainderSum :=
  rfl



theorem with_larger_finiteBound_rgToExponentBridge
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_larger_finiteBound hle).certificate.RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem with_larger_finiteBound_valid
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_larger_finiteBound hle).certificate.Valid correlationLength := by
  simpa using hvalid



theorem with_larger_finiteBound_hasCriticalNu
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_larger_finiteBound hle).certificate.predictedExponent := by
  simpa using hν


def with_larger_prefixTailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  S := W.S
  finitePrefix := W.finitePrefix
  table := W.table
  classify := W.classify
  finiteBound := W.finiteBound
  prefixTailBound := prefixTailBound'
  tailBound := W.tailBound
  tailEnvelope := W.tailEnvelope
  total_nonneg := W.total_nonneg
  additive := W.additive
  finiteTable := W.finiteTable
  tailEnvelopeOnPrefix := W.tailEnvelopeOnPrefix
  prefixTailEnvelopeSum_le := le_trans W.prefixTailEnvelopeSum_le hle
  finite_zero_off_prefix := W.finite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := W.tailEnvelope_nonneg_off_prefix
  tail_le_tailEnvelope_off_prefix := W.tail_le_tailEnvelope_off_prefix
  summable_masked_tailEnvelope := W.summable_masked_tailEnvelope
  masked_tailEnvelope_tsum_le := W.masked_tailEnvelope_tsum_le

@[simp] theorem with_larger_prefixTailBound_finiteBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).finiteBound = W.finiteBound :=
  rfl

@[simp] theorem with_larger_prefixTailBound_prefixTailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).prefixTailBound =
      prefixTailBound' :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailBound = W.tailBound :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailBudget = W.tailBudget :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tableFiniteBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tableFiniteBudget =
      W.tableFiniteBudget :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tablePrefixBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tablePrefixBudget =
      W.tableFiniteBudget + prefixTailBound' :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tableCertifiedTotalBound =
      (W.finitePrefix.card : ℝ) * W.finiteBound +
        prefixTailBound' + W.tailBound :=
  rfl

@[simp] theorem with_larger_prefixTailBound_toWitnessPackage
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).toWitnessPackage =
      W.toWitnessPackage :=
  rfl

@[simp] theorem with_larger_prefixTailBound_certificate
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).certificate = W.certificate :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailPrefixSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailPrefixSum =
      W.tailPrefixSum :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailCertifiedTotalBound =
      W.tailCertifiedTotalBound :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailTotalTsum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailTotalTsum =
      W.tailTotalTsum :=
  rfl

@[simp] theorem with_larger_prefixTailBound_tailRemainderSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
    (W.with_larger_prefixTailBound hle).tailRemainderSum =
      W.tailRemainderSum :=
  rfl



theorem with_larger_prefixTailBound_rgToExponentBridge
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_larger_prefixTailBound hle).certificate.RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem with_larger_prefixTailBound_valid
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_larger_prefixTailBound hle).certificate.Valid
      correlationLength := by
  simpa using hvalid



theorem with_larger_prefixTailBound_hasCriticalNu
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_larger_prefixTailBound hle).certificate.predictedExponent := by
  simpa using hν


def with_larger_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  S := W.S
  finitePrefix := W.finitePrefix
  table := W.table
  classify := W.classify
  finiteBound := W.finiteBound
  prefixTailBound := W.prefixTailBound
  tailBound := tailBound'
  tailEnvelope := W.tailEnvelope
  total_nonneg := W.total_nonneg
  additive := W.additive
  finiteTable := W.finiteTable
  tailEnvelopeOnPrefix := W.tailEnvelopeOnPrefix
  prefixTailEnvelopeSum_le := W.prefixTailEnvelopeSum_le
  finite_zero_off_prefix := W.finite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := W.tailEnvelope_nonneg_off_prefix
  tail_le_tailEnvelope_off_prefix := W.tail_le_tailEnvelope_off_prefix
  summable_masked_tailEnvelope := W.summable_masked_tailEnvelope
  masked_tailEnvelope_tsum_le := le_trans W.masked_tailEnvelope_tsum_le hle

@[simp] theorem with_larger_tailBound_finiteBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).finiteBound = W.finiteBound :=
  rfl

@[simp] theorem with_larger_tailBound_prefixTailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).prefixTailBound =
      W.prefixTailBound :=
  rfl

@[simp] theorem with_larger_tailBound_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailBound = tailBound' :=
  rfl

@[simp] theorem with_larger_tailBound_tailBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailBudget = tailBound' :=
  rfl

@[simp] theorem with_larger_tailBound_tailPrefixSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem with_larger_tailBound_tailCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailCertifiedTotalBound =
      W.tailPrefixSum + tailBound' :=
  rfl

@[simp] theorem with_larger_tailBound_tableFiniteBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tableFiniteBudget =
      W.tableFiniteBudget :=
  rfl

@[simp] theorem with_larger_tailBound_tablePrefixBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tablePrefixBudget =
      W.tablePrefixBudget :=
  rfl

@[simp] theorem with_larger_tailBound_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tableCertifiedTotalBound =
      (W.finitePrefix.card : ℝ) * W.finiteBound +
        W.prefixTailBound + tailBound' :=
  rfl

@[simp] theorem with_larger_tailBound_tailContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_larger_tailBound_tailTotalTsum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailTotalTsum = W.tailTotalTsum :=
  rfl

@[simp] theorem with_larger_tailBound_tailRemainderSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).tailRemainderSum =
      W.tailRemainderSum :=
  rfl

@[simp] theorem with_larger_tailBound_certificate
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    (W.with_larger_tailBound hle).certificate = W.certificate :=
  rfl



theorem with_larger_tailBound_rgToExponentBridge
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_larger_tailBound hle).certificate.RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem with_larger_tailBound_valid
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_larger_tailBound hle).certificate.Valid correlationLength := by
  simpa using hvalid



theorem with_larger_tailBound_hasCriticalNu
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_larger_tailBound hle).certificate.predictedExponent := by
  simpa using hν


theorem valid_of_bridge
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.toWitnessPackage.valid_of_bridge hbridge


theorem hasCriticalNu_of_bridge
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.toWitnessPackage.hasCriticalNu_of_bridge hbridge



theorem rgToExponentBridge_of_bridge_congr_predictedExponent
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.toWitnessPackage.rgToExponentBridge_of_bridge_congr_predictedExponent
    hpred hbridge




theorem valid_of_bridge_congr_predictedExponent
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_bridge_congr_predictedExponent hpred hbridge)



theorem hasCriticalNu_of_bridge_congr_predictedExponent
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.toWitnessPackage.hasCriticalNu_of_bridge_congr_predictedExponent
    hpred hbridge


theorem rgToExponentBridge_of_hasCriticalNu
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.toWitnessPackage.rgToExponentBridge_of_hasCriticalNu hν


theorem valid_of_hasCriticalNu
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.Valid correlationLength :=
  W.toWitnessPackage.valid_of_hasCriticalNu hν

end InfiniteTailMaskedTableWitnessPackage

end Exact3D
end StatMech
