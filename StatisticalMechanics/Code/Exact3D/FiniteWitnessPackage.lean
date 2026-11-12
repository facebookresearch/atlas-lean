/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.Certificate
import Code.Exact3D.FixedPointSkeleton
import Code.Exact3D.FiniteDimensionalRG
import Code.Exact3D.FiniteSupportCertificateConsequences
import Code.Exact3D.TailSummabilitySkeleton

open scoped BigOperators











namespace StatMech
namespace Exact3D

namespace RGCertificate




structure FiniteChecks {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) : Prop where
  finiteCaseChecks : C.FiniteCaseChecks
  tailBounds : C.TailBounds
  fixedPointEnclosure : C.FixedPointEnclosure
  linearizationEnclosure : C.LinearizationEnclosure
  hyperbolicSplitting : C.HyperbolicSplitting
  orbitEntry : C.OrbitEntry



theorem FiniteChecks.valid_of_bridge {ι : Type*} {M : CriticalModel ι}
    {C : RGCertificate M} {correlationLength : ℝ → ℝ}
    (h : C.FiniteChecks)
    (hbridge : C.RGToExponentBridge correlationLength) :
    C.Valid correlationLength where
  finiteCaseChecks := h.finiteCaseChecks
  tailBounds := h.tailBounds
  fixedPointEnclosure := h.fixedPointEnclosure
  linearizationEnclosure := h.linearizationEnclosure
  hyperbolicSplitting := h.hyperbolicSplitting
  orbitEntry := h.orbitEntry
  bridge := hbridge



theorem FiniteChecks.hasCriticalNu_of_bridge {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (h : C.FiniteChecks)
    (hbridge : C.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength C.predictedExponent :=
  (h.valid_of_bridge hbridge).hasCriticalNu



theorem FiniteChecks.rgToExponentBridge_of_hasCriticalNu {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (_h : C.FiniteChecks)
    (hν : HasCriticalNu M correlationLength C.predictedExponent) :
    C.RGToExponentBridge correlationLength :=
  C.bridge_of_hasCriticalNu correlationLength hν



theorem FiniteChecks.valid_of_hasCriticalNu {ι : Type*} {M : CriticalModel ι}
    {C : RGCertificate M} {correlationLength : ℝ → ℝ}
    (h : C.FiniteChecks)
    (hν : HasCriticalNu M correlationLength C.predictedExponent) :
    C.Valid correlationLength :=
  h.valid_of_bridge (h.rgToExponentBridge_of_hasCriticalNu hν)

end RGCertificate



structure FiniteStableWitness (n : ℕ) where
  map : (Fin n → ℝ) → Fin n → ℝ
  contraction : FiniteContraction.ClosedBallContractionCertificate map

namespace FiniteStableWitness


noncomputable def fixedPoint {n : ℕ} (S : FiniteStableWitness n) :
    Fin n → ℝ :=
  S.contraction.fixedPoint


theorem fixedPoint_isFixed {n : ℕ} (S : FiniteStableWitness n) :
    S.map S.fixedPoint = S.fixedPoint :=
  S.contraction.fixedPoint_isFixed


theorem exists_unique_fixedPoint {n : ℕ} (S : FiniteStableWitness n) :
    ∃! p : Fin n → ℝ, S.map p = p :=
  S.contraction.exists_unique_fixedPoint


theorem fixedPoint_mem {n : ℕ} (S : FiniteStableWitness n) :
    FiniteContraction.ClosedBall
      S.contraction.center S.contraction.radius S.fixedPoint :=
  S.contraction.fixedPoint_mem_selected

end FiniteStableWitness




structure FiniteWitnessPackage {ι α : Type*} [DecidableEq α]
    (M : CriticalModel ι) where
  nStable : ℕ
  scale : BlockScale
  thermal : ℝ
  thermal_gt_one : 1 < thermal
  stable : FiniteStableWitness nStable
  tailCertificate : TailSummability.FiniteSupportCertificate α

namespace FiniteWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}





noncomputable def ofContributionSplitFiniteSupport
    {Case : Type*} [DecidableEq Case]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit α) (support finitePrefix : Finset α)
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {finiteBound tailEnvelopeBound : ℝ} (tailEnvelope : α → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    FiniteWitnessPackage (α := α) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  tailCertificate :=
    S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
      support finitePrefix tailEnvelope hprefix hzero hnonneg hadd hfinite htail
      htailSum


abbrev State (W : FiniteWitnessPackage (α := α) M) : Type :=
  ℝ × (Fin W.nStable → ℝ)


abbrev hamiltonian (W : FiniteWitnessPackage (α := α) M) :
    EffectiveHamiltonian where
  carrier := W.State



noncomputable def rgMap (W : FiniteWitnessPackage (α := α) M) :
    BlockSpinMap W.hamiltonian where
  scale := W.scale
  map := fun x => (W.thermal * x.1, W.stable.map x.2)


@[simp] theorem rgMap_scale (W : FiniteWitnessPackage (α := α) M) :
    W.rgMap.scale = W.scale :=
  rfl



noncomputable def fixedPoint (W : FiniteWitnessPackage (α := α) M) :
    W.State :=
  (0, W.stable.fixedPoint)


theorem fixedPoint_eq (W : FiniteWitnessPackage (α := α) M) :
    W.rgMap.map W.fixedPoint = W.fixedPoint := by
  apply Prod.ext
  · simp [rgMap, fixedPoint]
  · simpa [rgMap, fixedPoint] using W.stable.fixedPoint_isFixed


noncomputable def fixedPointData (W : FiniteWitnessPackage (α := α) M) :
    RGFixedPointData W.hamiltonian W.rgMap where
  fixedPoint := W.fixedPoint
  fixedPoint_eq := W.fixedPoint_eq
  thermalEigenvalue := W.thermal
  thermal_gt_one := W.thermal_gt_one


noncomputable def certificate (W : FiniteWitnessPackage (α := α) M) :
    RGCertificate M where
  H := W.hamiltonian
  R := W.rgMap
  fixedPointData := W.fixedPointData


@[simp] theorem certificate_scale_eq
    (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.scale = W.scale :=
  rfl


@[simp] theorem certificate_thermalEigenvalue_eq
    (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.thermalEigenvalue = W.thermal :=
  rfl


@[simp] theorem certificate_fixedPoint_eq
    (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.fixedPointData.fixedPoint = W.fixedPoint :=
  rfl



theorem certificate_predictedExponent_eq
    (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.predictedExponent = predictedNu W.scale W.thermal :=
  rfl




def retarget {κ : Type*} (W : FiniteWitnessPackage (α := α) M)
    (N : CriticalModel κ) : FiniteWitnessPackage (α := α) N where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  tailCertificate := W.tailCertificate

@[simp] theorem retarget_certificate {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).certificate = W.certificate.retarget N :=
  rfl



theorem retarget_rgToExponentBridge {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    (W.retarget N).certificate.RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc



theorem retarget_valid {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength)
    (hβc : M.betaC = N.betaC) :
    (W.retarget N).certificate.Valid correlationLength := by
  simpa using hvalid.retarget hβc



theorem retarget_hasCriticalNu {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength
      ((W.retarget N).certificate).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc



theorem retarget_rgToExponentBridge_iff {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    W.certificate.RGToExponentBridge correlationLength ↔
      (W.retarget N).certificate.RGToExponentBridge correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := W.certificate) (N := N) hβc)



theorem retarget_valid_iff {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    W.certificate.Valid correlationLength ↔
      (W.retarget N).certificate.Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := W.certificate) (N := N) hβc)



theorem retarget_hasCriticalNu_iff {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent ↔
      HasCriticalNu N correlationLength
        ((W.retarget N).certificate).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := W.certificate) (N := N) hβc)


theorem fixedPointEnclosure (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.FixedPointEnclosure := by
  simpa [certificate, fixedPointData, RGCertificate.FixedPointEnclosure] using
    W.fixedPoint_eq



theorem finiteChecks (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.FiniteChecks where
  finiteCaseChecks := trivial
  tailBounds := trivial
  fixedPointEnclosure := W.fixedPointEnclosure
  linearizationEnclosure := W.certificate.linearizationEnclosure_of_thermal_gt_one
  hyperbolicSplitting := W.certificate.hyperbolicSplitting_of_thermal_gt_one
  orbitEntry := trivial



theorem finiteCaseChecks (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.FiniteCaseChecks :=
  W.finiteChecks.finiteCaseChecks



theorem tailBounds (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.TailBounds :=
  W.finiteChecks.tailBounds



theorem linearizationEnclosure (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.LinearizationEnclosure :=
  W.finiteChecks.linearizationEnclosure



theorem hyperbolicSplitting (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.HyperbolicSplitting :=
  W.finiteChecks.hyperbolicSplitting



theorem orbitEntry (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.OrbitEntry :=
  W.finiteChecks.orbitEntry



noncomputable def tailPrefixSum (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  ∑ a ∈ W.tailCertificate.finitePrefix, W.tailCertificate.weight a


def tailBudget (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  W.tailCertificate.tailBound



noncomputable def tailCertifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  W.tailPrefixSum + W.tailBudget


def tailContribution (W : FiniteWitnessPackage (α := α) M) : α → ℝ :=
  W.tailCertificate.weight


noncomputable def tailTotalTsum
    (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  ∑' a, W.tailContribution a


def tailSupport (W : FiniteWitnessPackage (α := α) M) : Finset α :=
  W.tailCertificate.tailSupport


def tailSupportCard (W : FiniteWitnessPackage (α := α) M) : ℕ :=
  W.tailSupport.card


def finitePrefixCard (W : FiniteWitnessPackage (α := α) M) : ℕ :=
  W.tailCertificate.finitePrefix.card


noncomputable def tailRemainderSum
    (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  ∑ a ∈ W.tailSupport, W.tailContribution a


noncomputable def tailEnvelopeSum
    (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  ∑ a ∈ W.tailSupport, W.tailCertificate.envelope a


@[simp] theorem retarget_tailPrefixSum {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailPrefixSum = W.tailPrefixSum :=
  rfl


@[simp] theorem retarget_tailBudget {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailBudget = W.tailBudget :=
  rfl


@[simp] theorem retarget_tailCertifiedTotalBound {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailCertifiedTotalBound =
      W.tailCertifiedTotalBound :=
  rfl


@[simp] theorem retarget_tailContribution {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailContribution = W.tailContribution :=
  rfl


@[simp] theorem retarget_tailTotalTsum {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailTotalTsum = W.tailTotalTsum :=
  rfl


@[simp] theorem retarget_tailSupport {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailSupport = W.tailSupport :=
  rfl


@[simp] theorem retarget_tailRemainderSum {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailRemainderSum = W.tailRemainderSum :=
  rfl


@[simp] theorem retarget_tailEnvelopeSum {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailEnvelopeSum = W.tailEnvelopeSum :=
  rfl


@[simp] theorem retarget_predictedExponent {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).certificate.predictedExponent =
      W.certificate.predictedExponent :=
  rfl


theorem tailTotalTsum_eq_tsum
    (W : FiniteWitnessPackage (α := α) M) :
    W.tailTotalTsum = ∑' a, W.tailCertificate.weight a :=
  rfl



theorem tailTotalTsum_eq_prefix_add_remainder
    (W : FiniteWitnessPackage (α := α) M) :
    W.tailTotalTsum = W.tailPrefixSum + W.tailRemainderSum := by
  simpa [tailTotalTsum, tailContribution, tailPrefixSum,
    tailRemainderSum, tailSupport] using
    W.tailCertificate.tsum_eq_prefix_add_tail


theorem tailRemainderSum_le_tailBudget
    (W : FiniteWitnessPackage (α := α) M) :
    W.tailRemainderSum ≤ W.tailBudget := by
  simpa [tailRemainderSum, tailContribution, tailSupport, tailBudget] using
    W.tailCertificate.tail_sum_le_bound


theorem tailRemainderSum_nonneg
    (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ W.tailRemainderSum := by
  simpa [tailRemainderSum, tailContribution, tailSupport] using
    W.tailCertificate.tail_sum_nonneg



theorem tailSupport_eq_empty_of_support_subset
    (W : FiniteWitnessPackage (α := α) M)
    (hsupport_subset_prefix :
      W.tailCertificate.support ⊆ W.tailCertificate.finitePrefix) :
    W.tailSupport = ∅ := by
  simpa [tailSupport] using
    W.tailCertificate.tailSupport_eq_empty_of_support_subset
      hsupport_subset_prefix



theorem tailTotalTsum_eq_tailPrefixSum_of_support_subset
    (W : FiniteWitnessPackage (α := α) M)
    (hsupport_subset_prefix :
      W.tailCertificate.support ⊆ W.tailCertificate.finitePrefix) :
    W.tailTotalTsum = W.tailPrefixSum := by
  simpa [tailTotalTsum, tailContribution, tailPrefixSum] using
    W.tailCertificate.tsum_eq_finitePrefix_sum_of_support_subset
      hsupport_subset_prefix



theorem tailRemainderSum_eq_zero_of_support_subset
    (W : FiniteWitnessPackage (α := α) M)
    (hsupport_subset_prefix :
      W.tailCertificate.support ⊆ W.tailCertificate.finitePrefix) :
    W.tailRemainderSum = 0 := by
  simpa [tailRemainderSum, tailContribution, tailSupport] using
    W.tailCertificate.tail_sum_eq_zero_of_support_subset
      hsupport_subset_prefix


theorem tailRemainderSum_eq_zero_of_tailBudget_eq_zero
    (W : FiniteWitnessPackage (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailRemainderSum = 0 :=
  le_antisymm (by simpa [hbudget] using W.tailRemainderSum_le_tailBudget)
    W.tailRemainderSum_nonneg



theorem tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero
    (W : FiniteWitnessPackage (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailTotalTsum = W.tailPrefixSum := by
  rw [W.tailTotalTsum_eq_prefix_add_remainder,
    W.tailRemainderSum_eq_zero_of_tailBudget_eq_zero hbudget, add_zero]


theorem tailEnvelopeSum_nonneg
    (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ W.tailEnvelopeSum := by
  simpa [tailEnvelopeSum, tailSupport] using
    W.tailCertificate.envelope_tail_sum_nonneg


theorem tailEnvelopeSum_le_tailBudget
    (W : FiniteWitnessPackage (α := α) M) :
    W.tailEnvelopeSum ≤ W.tailBudget := by
  simpa [tailEnvelopeSum, tailSupport, tailBudget] using
    W.tailCertificate.envelope_tail_sum_le



theorem tail_tsum_le_prefix_add_tailBound
    (W : FiniteWitnessPackage (α := α) M) :
    (∑' a, W.tailCertificate.weight a) ≤
      (∑ a ∈ W.tailCertificate.finitePrefix,
        W.tailCertificate.weight a) + W.tailCertificate.tailBound :=
  W.tailCertificate.tsum_le_prefix_sum_add_tailBound



theorem tail_tsum_le_certifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) :
    (∑' a, W.tailCertificate.weight a) ≤ W.tailCertifiedTotalBound := by
  simpa [tailCertifiedTotalBound, tailPrefixSum, tailBudget] using
    W.tail_tsum_le_prefix_add_tailBound



theorem tail_tsum_le_of_certifiedTotalBound_le
    (W : FiniteWitnessPackage (α := α) M) {B : ℝ}
    (hB : W.tailCertifiedTotalBound ≤ B) :
    (∑' a, W.tailCertificate.weight a) ≤ B :=
  le_trans W.tail_tsum_le_certifiedTotalBound hB


theorem tailTotalTsum_le_certifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) :
    W.tailTotalTsum ≤ W.tailCertifiedTotalBound := by
  simpa [tailTotalTsum, tailContribution] using
    W.tail_tsum_le_certifiedTotalBound



theorem tailTotalTsum_le_of_certifiedTotalBound_le
    (W : FiniteWitnessPackage (α := α) M) {B : ℝ}
    (hB : W.tailCertifiedTotalBound ≤ B) :
    W.tailTotalTsum ≤ B :=
  le_trans W.tailTotalTsum_le_certifiedTotalBound hB




def with_tailEnvelope_and_tailBudget (W : FiniteWitnessPackage (α := α) M)
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    FiniteWitnessPackage (α := α) M where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  tailCertificate :=
    W.tailCertificate.with_tailEnvelope_and_tailBound envelope'
      henvelope_nonneg hweight_le henvelope_sum

@[simp] theorem with_tailEnvelope_and_tailBudget_tailBudget
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailBudget = tailBound' :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBudget_tailPrefixSum
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailPrefixSum =
        W.tailPrefixSum :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBudget_certificate
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).certificate =
        W.certificate :=
  rfl


@[simp] theorem with_tailEnvelope_and_tailBudget_tailCertifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailCertifiedTotalBound =
        W.tailPrefixSum + tailBound' :=
  rfl


@[simp] theorem with_tailEnvelope_and_tailBudget_tailContribution
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailContribution =
        W.tailContribution :=
  rfl


@[simp] theorem with_tailEnvelope_and_tailBudget_tailTotalTsum
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailTotalTsum =
        W.tailTotalTsum :=
  rfl


@[simp] theorem with_tailEnvelope_and_tailBudget_tailSupport
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailSupport =
        W.tailSupport :=
  rfl


@[simp] theorem with_tailEnvelope_and_tailBudget_tailRemainderSum
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailRemainderSum =
        W.tailRemainderSum :=
  rfl



@[simp] theorem with_tailEnvelope_and_tailBudget_tailEnvelopeSum
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).tailEnvelopeSum =
        ∑ a ∈ W.tailSupport, envelope' a :=
  rfl



theorem with_tailEnvelope_and_tailBudget_rgToExponentBridge
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge



theorem with_tailEnvelope_and_tailBudget_valid
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_tailEnvelope_and_tailBudget envelope'
      henvelope_nonneg hweight_le henvelope_sum).certificate.Valid
        correlationLength := by
  simpa using hvalid



theorem with_tailEnvelope_and_tailBudget_hasCriticalNu
    (W : FiniteWitnessPackage (α := α) M) (envelope' : α → ℝ)
    {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_tailEnvelope_and_tailBudget envelope'
        henvelope_nonneg hweight_le henvelope_sum).certificate.predictedExponent := by
  simpa using hν



def with_larger_tailBudget (W : FiniteWitnessPackage (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    FiniteWitnessPackage (α := α) M where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  tailCertificate :=
    W.tailCertificate.with_larger_tailBound (by
      simpa [tailBudget] using hle)

@[simp] theorem with_larger_tailBudget_tailBudget
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailBudget = tailBound' :=
  rfl

@[simp] theorem with_larger_tailBudget_tailPrefixSum
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem with_larger_tailBudget_tailCertifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailCertifiedTotalBound =
      W.tailPrefixSum + tailBound' :=
  rfl


@[simp] theorem with_larger_tailBudget_tailContribution
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailContribution =
      W.tailContribution :=
  rfl


@[simp] theorem with_larger_tailBudget_tailTotalTsum
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailTotalTsum =
      W.tailTotalTsum :=
  rfl


@[simp] theorem with_larger_tailBudget_tailSupport
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailSupport = W.tailSupport :=
  rfl


@[simp] theorem with_larger_tailBudget_tailRemainderSum
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailRemainderSum =
      W.tailRemainderSum :=
  rfl


@[simp] theorem with_larger_tailBudget_tailEnvelopeSum
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).tailEnvelopeSum = W.tailEnvelopeSum :=
  rfl

@[simp] theorem with_larger_tailBudget_certificate
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (W.with_larger_tailBudget hle).certificate = W.certificate :=
  rfl



theorem with_larger_tailBudget_rgToExponentBridge
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    (W.with_larger_tailBudget hle).certificate.RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem with_larger_tailBudget_valid
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hvalid : W.certificate.Valid correlationLength) :
    (W.with_larger_tailBudget hle).certificate.Valid correlationLength := by
  simpa using hvalid



theorem with_larger_tailBudget_hasCriticalNu
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound')
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    HasCriticalNu M correlationLength
      (W.with_larger_tailBudget hle).certificate.predictedExponent := by
  simpa using hν



theorem tail_tsum_le_prefix_add_of_tailBudget_le
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (∑' a, W.tailCertificate.weight a) ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailPrefixSum, tailBudget] using
    W.tailCertificate.tsum_le_prefix_sum_add_of_tailBound_le hle



theorem tailTotalTsum_le_prefix_add_of_tailBudget_le
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailTotalTsum ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailTotalTsum, tailContribution] using
    W.tail_tsum_le_prefix_add_of_tailBudget_le hle



theorem tailRemainderSum_le_of_tailBudget_le
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailRemainderSum ≤ tailBound' :=
  le_trans W.tailRemainderSum_le_tailBudget hle


theorem tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le
    (W : FiniteWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailCertifiedTotalBound ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailCertifiedTotalBound] using
    add_le_add (le_refl W.tailPrefixSum) hle


theorem tailPrefixSum_nonneg (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ W.tailPrefixSum := by
  simpa [tailPrefixSum] using W.tailCertificate.prefix_sum_nonneg


theorem tailBudget_nonneg (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ W.tailBudget := by
  simpa [tailBudget] using W.tailCertificate.tailBound_nonneg


theorem tailCertifiedTotalBound_nonneg
    (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ W.tailCertifiedTotalBound :=
  add_nonneg W.tailPrefixSum_nonneg W.tailBudget_nonneg


theorem tail_tsum_nonneg (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ ∑' a, W.tailCertificate.weight a :=
  W.tailCertificate.tsum_nonneg


theorem stable_fixedPoint_mem (W : FiniteWitnessPackage (α := α) M) :
    FiniteContraction.ClosedBall
      W.stable.contraction.center W.stable.contraction.radius
      W.stable.fixedPoint :=
  W.stable.fixedPoint_mem


theorem stable_exists_unique_fixedPoint
    (W : FiniteWitnessPackage (α := α) M) :
    ∃! p : Fin W.nStable → ℝ, W.stable.map p = p :=
  W.stable.exists_unique_fixedPoint



theorem valid_of_bridge (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.finiteChecks.valid_of_bridge hbridge



theorem hasCriticalNu_of_bridge (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_bridge hbridge).hasCriticalNu



theorem rgToExponentBridge_of_bridge_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred



theorem valid_of_bridge_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_bridge_congr_predictedExponent hpred hbridge)



theorem hasCriticalNu_of_bridge_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_bridge_congr_predictedExponent hpred hbridge).hasCriticalNu



theorem rgToExponentBridge_of_hasCriticalNu
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.RGToExponentBridge correlationLength := by
  simpa [RGCertificate.RGToExponentBridge] using hν



theorem valid_of_hasCriticalNu (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength W.certificate.predictedExponent) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_hasCriticalNu hν)

end FiniteWitnessPackage

end Exact3D
end StatMech
