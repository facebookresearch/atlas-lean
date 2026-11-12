/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.TailSummabilitySkeleton
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group

open scoped BigOperators










namespace StatMech
namespace Exact3D

namespace TailSummability

variable {α : Type*} [DecidableEq α]







structure InfiniteTailCertificate (α : Type*) [DecidableEq α] where
  finitePrefix : Finset α
  weight : α → ℝ
  prefixWeight : α → ℝ
  tailWeight : α → ℝ
  tailBound : ℝ
  prefix_eq_weight_on_prefix :
    ∀ a, a ∈ finitePrefix → prefixWeight a = weight a
  prefixWeight_zero_off_prefix :
    ∀ a, a ∉ finitePrefix → prefixWeight a = 0
  tailWeight_zero_on_prefix :
    ∀ a, a ∈ finitePrefix → tailWeight a = 0
  decomposition :
    ∀ a, weight a = prefixWeight a + tailWeight a
  prefixWeight_nonneg : ∀ a, 0 ≤ prefixWeight a
  tailWeight_nonneg : ∀ a, 0 ≤ tailWeight a
  summable_tail : Summable tailWeight
  tail_tsum_le : (∑' a, tailWeight a) ≤ tailBound

namespace InfiniteTailCertificate

variable (C : InfiniteTailCertificate α)


def prefixSum : ℝ :=
  ∑ a ∈ C.finitePrefix, C.weight a


theorem summable_prefixWeight : Summable C.prefixWeight :=
  summable_of_ne_finset_zero (s := C.finitePrefix)
    C.prefixWeight_zero_off_prefix


theorem tsum_prefixWeight_eq_prefixWeight_sum :
    (∑' a, C.prefixWeight a) =
      ∑ a ∈ C.finitePrefix, C.prefixWeight a :=
  tsum_eq_sum (s := C.finitePrefix) C.prefixWeight_zero_off_prefix


theorem prefixWeight_sum_eq_prefixSum :
    (∑ a ∈ C.finitePrefix, C.prefixWeight a) = C.prefixSum := by
  unfold prefixSum
  exact Finset.sum_congr rfl fun a ha => C.prefix_eq_weight_on_prefix a ha


theorem tsum_prefixWeight_eq_prefixSum :
    (∑' a, C.prefixWeight a) = C.prefixSum := by
  rw [C.tsum_prefixWeight_eq_prefixWeight_sum,
    C.prefixWeight_sum_eq_prefixSum]


theorem summable_weight : Summable C.weight := by
  have hsum :
      Summable (fun a => C.prefixWeight a + C.tailWeight a) :=
    C.summable_prefixWeight.add C.summable_tail
  exact hsum.congr fun a => (C.decomposition a).symm



theorem tsum_weight_eq_prefixSum_add_tail :
    (∑' a, C.weight a) =
      C.prefixSum + ∑' a, C.tailWeight a := by
  calc
    (∑' a, C.weight a) =
        ∑' a, (C.prefixWeight a + C.tailWeight a) :=
      tsum_congr C.decomposition
    _ = (∑' a, C.prefixWeight a) + ∑' a, C.tailWeight a :=
      Summable.tsum_add C.summable_prefixWeight C.summable_tail
    _ = C.prefixSum + ∑' a, C.tailWeight a := by
      rw [C.tsum_prefixWeight_eq_prefixSum]



theorem tsum_weight_le_prefixSum_add_tailBound :
    (∑' a, C.weight a) ≤ C.prefixSum + C.tailBound := by
  rw [C.tsum_weight_eq_prefixSum_add_tail]
  exact add_le_add (le_refl C.prefixSum) C.tail_tsum_le



theorem tsum_weight_le_prefixSum_add_of_tailBound_le {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (∑' a, C.weight a) ≤ C.prefixSum + tailBound' :=
  le_trans C.tsum_weight_le_prefixSum_add_tailBound
    (add_le_add (le_refl C.prefixSum) hle)


theorem prefixSum_nonneg : 0 ≤ C.prefixSum := by
  unfold prefixSum
  exact sum_nonneg_on fun a ha => by
    rw [← C.prefix_eq_weight_on_prefix a ha]
    exact C.prefixWeight_nonneg a


theorem tail_tsum_nonneg : 0 ≤ ∑' a, C.tailWeight a :=
  tsum_nonneg C.tailWeight_nonneg


theorem tsum_weight_nonneg : 0 ≤ ∑' a, C.weight a := by
  rw [C.tsum_weight_eq_prefixSum_add_tail]
  exact add_nonneg C.prefixSum_nonneg C.tail_tsum_nonneg


theorem tailBound_nonneg : 0 ≤ C.tailBound :=
  le_trans C.tail_tsum_nonneg C.tail_tsum_le


theorem weight_nonneg (a : α) : 0 ≤ C.weight a := by
  rw [C.decomposition a]
  exact add_nonneg (C.prefixWeight_nonneg a) (C.tailWeight_nonneg a)


def with_larger_tailBound {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    InfiniteTailCertificate α where
  finitePrefix := C.finitePrefix
  weight := C.weight
  prefixWeight := C.prefixWeight
  tailWeight := C.tailWeight
  tailBound := tailBound'
  prefix_eq_weight_on_prefix := C.prefix_eq_weight_on_prefix
  prefixWeight_zero_off_prefix := C.prefixWeight_zero_off_prefix
  tailWeight_zero_on_prefix := C.tailWeight_zero_on_prefix
  decomposition := C.decomposition
  prefixWeight_nonneg := C.prefixWeight_nonneg
  tailWeight_nonneg := C.tailWeight_nonneg
  summable_tail := C.summable_tail
  tail_tsum_le := le_trans C.tail_tsum_le hle

@[simp] theorem with_larger_tailBound_finitePrefix {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).finitePrefix = C.finitePrefix :=
  rfl

@[simp] theorem with_larger_tailBound_weight {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).weight = C.weight :=
  rfl

@[simp] theorem with_larger_tailBound_prefixWeight {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).prefixWeight = C.prefixWeight :=
  rfl

@[simp] theorem with_larger_tailBound_tailWeight {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).tailWeight = C.tailWeight :=
  rfl

@[simp] theorem with_larger_tailBound_tailBound {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).tailBound = tailBound' :=
  rfl

@[simp] theorem with_larger_tailBound_prefixSum {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).prefixSum = C.prefixSum :=
  rfl





noncomputable def of_tailEnvelope
    (finitePrefix : Finset α) (weight tailEnvelope : α → ℝ)
    {tailBound : ℝ}
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope a)
    (hweight_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
    (hsummable_tailEnvelope : Summable tailEnvelope)
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope a) ≤ tailBound) :
    InfiniteTailCertificate α where
  finitePrefix := finitePrefix
  weight := weight
  prefixWeight := fun a => if a ∈ finitePrefix then weight a else 0
  tailWeight := fun a => if a ∈ finitePrefix then 0 else weight a
  tailBound := tailBound
  prefix_eq_weight_on_prefix := by
    intro a ha
    simp [ha]
  prefixWeight_zero_off_prefix := by
    intro a ha
    simp [ha]
  tailWeight_zero_on_prefix := by
    intro a ha
    simp [ha]
  decomposition := by
    intro a
    by_cases ha : a ∈ finitePrefix <;> simp [ha]
  prefixWeight_nonneg := by
    intro a
    by_cases ha : a ∈ finitePrefix
    · simpa [ha] using hweight_nonneg a
    · simp [ha]
  tailWeight_nonneg := by
    intro a
    by_cases ha : a ∈ finitePrefix
    · simp [ha]
    · simpa [ha] using hweight_nonneg a
  summable_tail := by
    let tailWeight : α → ℝ :=
      fun a => if a ∈ finitePrefix then 0 else weight a
    have htail_nonneg : ∀ a, 0 ≤ tailWeight a := by
      intro a
      by_cases ha : a ∈ finitePrefix
      · simp [tailWeight, ha]
      · simpa [tailWeight, ha] using hweight_nonneg a
    have htail_le : ∀ a, tailWeight a ≤ tailEnvelope a := by
      intro a
      by_cases ha : a ∈ finitePrefix
      · simpa [tailWeight, ha] using henvelope_nonneg a
      · simpa [tailWeight, ha] using hweight_le_tailEnvelope a ha
    simpa [tailWeight] using
      Summable.of_nonneg_of_le htail_nonneg htail_le hsummable_tailEnvelope
  tail_tsum_le := by
    let tailWeight : α → ℝ :=
      fun a => if a ∈ finitePrefix then 0 else weight a
    have htail_nonneg : ∀ a, 0 ≤ tailWeight a := by
      intro a
      by_cases ha : a ∈ finitePrefix
      · simp [tailWeight, ha]
      · simpa [tailWeight, ha] using hweight_nonneg a
    have htail_le : ∀ a, tailWeight a ≤ tailEnvelope a := by
      intro a
      by_cases ha : a ∈ finitePrefix
      · simpa [tailWeight, ha] using henvelope_nonneg a
      · simpa [tailWeight, ha] using hweight_le_tailEnvelope a ha
    have htail_summable : Summable tailWeight :=
      Summable.of_nonneg_of_le htail_nonneg htail_le
        hsummable_tailEnvelope
    exact le_trans
      (by
        simpa [tailWeight] using
          Summable.tsum_le_tsum htail_le htail_summable
            hsummable_tailEnvelope)
      htailEnvelope_tsum_le





noncomputable def of_masked_tailEnvelope
    (finitePrefix : Finset α) (weight tailEnvelope : α → ℝ)
    {tailBound : ℝ}
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (hweight_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    InfiniteTailCertificate α :=
  of_tailEnvelope
    finitePrefix
    weight
    (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a)
    hweight_nonneg
    (by
      intro a
      by_cases ha : a ∈ finitePrefix
      · simp [ha]
      · simpa [ha] using henvelope_nonneg_off a ha)
    (by
      intro a ha
      simpa [ha] using hweight_le_tailEnvelope a ha)
    hsummable_masked
    hmasked_tsum_le

@[simp] theorem of_masked_tailEnvelope_finitePrefix
    (finitePrefix : Finset α) (weight tailEnvelope : α → ℝ)
    {tailBound : ℝ}
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (hweight_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    (of_masked_tailEnvelope finitePrefix weight tailEnvelope hweight_nonneg
      henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).finitePrefix = finitePrefix :=
  rfl

@[simp] theorem of_masked_tailEnvelope_weight
    (finitePrefix : Finset α) (weight tailEnvelope : α → ℝ)
    {tailBound : ℝ}
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (hweight_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    (of_masked_tailEnvelope finitePrefix weight tailEnvelope hweight_nonneg
      henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).weight = weight :=
  rfl

@[simp] theorem of_masked_tailEnvelope_tailBound
    (finitePrefix : Finset α) (weight tailEnvelope : α → ℝ)
    {tailBound : ℝ}
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (hweight_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    (of_masked_tailEnvelope finitePrefix weight tailEnvelope hweight_nonneg
      henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tailBound = tailBound :=
  rfl

end InfiniteTailCertificate

namespace FiniteSupportCertificate

variable (C : FiniteSupportCertificate α)





noncomputable def toInfiniteTailCertificate :
    InfiniteTailCertificate α where
  finitePrefix := C.finitePrefix
  weight := C.weight
  prefixWeight := fun a => if a ∈ C.finitePrefix then C.weight a else 0
  tailWeight := fun a => if a ∈ C.finitePrefix then 0 else C.weight a
  tailBound := C.tailBound
  prefix_eq_weight_on_prefix := by
    intro a ha
    simp [ha]
  prefixWeight_zero_off_prefix := by
    intro a ha
    simp [ha]
  tailWeight_zero_on_prefix := by
    intro a ha
    simp [ha]
  decomposition := by
    intro a
    by_cases ha : a ∈ C.finitePrefix <;> simp [ha]
  prefixWeight_nonneg := by
    intro a
    by_cases ha : a ∈ C.finitePrefix
    · simpa [ha] using C.weight_nonneg a
    · simp [ha]
  tailWeight_nonneg := by
    intro a
    by_cases ha : a ∈ C.finitePrefix
    · simp [ha]
    · simpa [ha] using C.weight_nonneg a
  summable_tail := by
    refine summable_of_ne_finset_zero (s := C.support) ?_
    intro a ha
    by_cases hprefix : a ∈ C.finitePrefix
    · simp [hprefix]
    · simp [hprefix, C.zero_off_support a ha]
  tail_tsum_le := by
    let tailWeight : α → ℝ :=
      fun a => if a ∈ C.finitePrefix then 0 else C.weight a
    have hzero :
        ∀ a, a ∉ C.tailSupport → tailWeight a = 0 := by
      intro a ha
      by_cases hprefix : a ∈ C.finitePrefix
      · simp [tailWeight, hprefix]
      · have hnotSupport : a ∉ C.support := by
          intro hsupport
          exact ha (by simp [FiniteSupportCertificate.tailSupport,
            hsupport, hprefix])
        simp [tailWeight, hprefix, C.zero_off_support a hnotSupport]
    have hsum_eq_weight :
        (∑ a ∈ C.tailSupport, tailWeight a) =
          ∑ a ∈ C.tailSupport, C.weight a := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      have htail := (FiniteSupportCertificate.mem_tailSupport (C := C)).1 ha
      simp [tailWeight, htail.2]
    calc
      (∑' a, (if a ∈ C.finitePrefix then 0 else C.weight a)) =
          ∑ a ∈ C.tailSupport, tailWeight a := by
        simpa [tailWeight] using tsum_eq_sum (s := C.tailSupport) hzero
      _ = ∑ a ∈ C.tailSupport, C.weight a := hsum_eq_weight
      _ ≤ C.tailBound := C.tail_sum_le_bound

@[simp] theorem toInfiniteTailCertificate_finitePrefix :
    C.toInfiniteTailCertificate.finitePrefix = C.finitePrefix :=
  rfl

@[simp] theorem toInfiniteTailCertificate_weight :
    C.toInfiniteTailCertificate.weight = C.weight :=
  rfl

@[simp] theorem toInfiniteTailCertificate_tailBound :
    C.toInfiniteTailCertificate.tailBound = C.tailBound :=
  rfl



theorem toInfiniteTailCertificate_tsum_weight_le_prefix_add_tailBound :
    (∑' a, C.toInfiniteTailCertificate.weight a) ≤
      C.toInfiniteTailCertificate.prefixSum + C.tailBound := by
  simpa using
    C.toInfiniteTailCertificate.tsum_weight_le_prefixSum_add_tailBound

end FiniteSupportCertificate

end TailSummability

namespace ContributionSplit

variable {α : Type*} [DecidableEq α]






noncomputable def infiniteTailCertificate_of_tailEnvelope_off_prefix
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
    TailSummability.InfiniteTailCertificate α :=
  TailSummability.InfiniteTailCertificate.of_tailEnvelope
    finitePrefix S.totalContribution tailEnvelope htotal_nonneg
    henvelope_nonneg
    (by
      intro a ha
      calc
        S.totalContribution a =
            S.finiteContribution a + S.tailContribution a := hadd a
        _ = S.tailContribution a := by
          rw [hfinite_zero_off_prefix a ha, zero_add]
        _ ≤ tailEnvelope a := htail_le_tailEnvelope a ha)
    hsummable_tailEnvelope htailEnvelope_tsum_le




noncomputable def infiniteTailCertificate_of_masked_tailEnvelope_off_prefix
    (S : ContributionSplit α) (finitePrefix : Finset α)
    (tailEnvelope : α → ℝ) {tailBound : ℝ}
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    TailSummability.InfiniteTailCertificate α :=
  TailSummability.InfiniteTailCertificate.of_masked_tailEnvelope
    finitePrefix S.totalContribution tailEnvelope htotal_nonneg
    henvelope_nonneg_off
    (by
      intro a ha
      calc
        S.totalContribution a =
            S.finiteContribution a + S.tailContribution a := hadd a
        _ = S.tailContribution a := by
          rw [hfinite_zero_off_prefix a ha, zero_add]
        _ ≤ tailEnvelope a := htail_le_tailEnvelope a ha)
    hsummable_masked hmasked_tsum_le



theorem tsum_total_le_prefixSum_add_tailBound_of_tailEnvelope_off_prefix
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
    (∑' a, S.totalContribution a) ≤
      (S.infiniteTailCertificate_of_tailEnvelope_off_prefix
        finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
        henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
        htailEnvelope_tsum_le).prefixSum + tailBound := by
  simpa [infiniteTailCertificate_of_tailEnvelope_off_prefix] using
    (S.infiniteTailCertificate_of_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tsum_weight_le_prefixSum_add_tailBound




theorem
    tsum_total_le_prefixSum_add_tailBound_of_masked_tailEnvelope_off_prefix
    (S : ContributionSplit α) (finitePrefix : Finset α)
    (tailEnvelope : α → ℝ) {tailBound : ℝ}
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    (∑' a, S.totalContribution a) ≤
      (S.infiniteTailCertificate_of_masked_tailEnvelope_off_prefix
        finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
        henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
        hmasked_tsum_le).prefixSum + tailBound := by
  simpa [infiniteTailCertificate_of_masked_tailEnvelope_off_prefix] using
    (S.infiniteTailCertificate_of_masked_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tsum_weight_le_prefixSum_add_tailBound





theorem tsum_total_le_card_mul_finiteBound_add_prefixTailBound_add_tailBound
    {β : Type*} (S : ContributionSplit β) (finitePrefix : Finset β)
    {Case : Type*} [DecidableEq Case]
    {T : RatInterval.CaseTable Case} {classify : β → Case}
    {finiteBound prefixTailBound tailBound : ℝ}
    (tailEnvelope : β → ℝ)
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite :
      FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail_on_prefix : S.TailEnvelopeOn finitePrefix tailEnvelope)
    (htailPrefixSum_le :
      (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_tailEnvelope : Summable tailEnvelope)
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (finitePrefix.card : ℝ) * finiteBound + prefixTailBound + tailBound := by
  classical
  have hprefix :
      (S.infiniteTailCertificate_of_tailEnvelope_off_prefix
        finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
        henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
        htailEnvelope_tsum_le).prefixSum ≤
          (finitePrefix.card : ℝ) * finiteBound + prefixTailBound := by
    simpa [infiniteTailCertificate_of_tailEnvelope_off_prefix,
      TailSummability.InfiniteTailCertificate.of_tailEnvelope,
      TailSummability.InfiniteTailCertificate.prefixSum] using
      (S.total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn
        finitePrefix tailEnvelope hadd hfinite htail_on_prefix
        htailPrefixSum_le)
  exact le_trans
    (S.tsum_total_le_prefixSum_add_tailBound_of_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le)
    (add_le_add hprefix (le_refl tailBound))





theorem
    tsum_total_le_card_mul_finiteBound_add_prefixTailBound_add_maskedTailBound
    {β : Type*} (S : ContributionSplit β) (finitePrefix : Finset β)
    [DecidableEq β]
    {Case : Type*} [DecidableEq Case]
    {T : RatInterval.CaseTable Case} {classify : β → Case}
    {finiteBound prefixTailBound tailBound : ℝ}
    (tailEnvelope : β → ℝ)
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite :
      FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail_on_prefix : S.TailEnvelopeOn finitePrefix tailEnvelope)
    (htailPrefixSum_le :
      (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    (∑' a, S.totalContribution a) ≤
      (finitePrefix.card : ℝ) * finiteBound + prefixTailBound + tailBound := by
  classical
  have hprefix :
      (S.infiniteTailCertificate_of_masked_tailEnvelope_off_prefix
        finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
        henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
        hmasked_tsum_le).prefixSum ≤
          (finitePrefix.card : ℝ) * finiteBound + prefixTailBound := by
    simpa [infiniteTailCertificate_of_masked_tailEnvelope_off_prefix,
      TailSummability.InfiniteTailCertificate.of_masked_tailEnvelope,
      TailSummability.InfiniteTailCertificate.prefixSum] using
      (S.total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn
        finitePrefix tailEnvelope hadd hfinite htail_on_prefix
        htailPrefixSum_le)
  exact le_trans
    (S.tsum_total_le_prefixSum_add_tailBound_of_masked_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le)
    (add_le_add hprefix (le_refl tailBound))

end ContributionSplit

end Exact3D
end StatMech
