/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.TailBoundSkeleton
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped BigOperators










namespace StatMech
namespace Exact3D

namespace TailSummability

variable {α : Type*}


theorem sum_nonneg_on {s : Finset α} {f : α → ℝ}
    (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    0 ≤ ∑ a ∈ s, f a :=
  Finset.sum_nonneg fun a ha => hf a ha

variable [DecidableEq α]



theorem sum_eq_prefix_add_tail {s front : Finset α} (hfront : front ⊆ s)
    (f : α → ℝ) :
    (∑ a ∈ s, f a) =
      (∑ a ∈ front, f a) + ∑ a ∈ s \ front, f a := by
  calc
    (∑ a ∈ s, f a) =
        (∑ a ∈ s \ front, f a) + ∑ a ∈ front, f a :=
      (Finset.sum_sdiff hfront).symm
    _ = (∑ a ∈ front, f a) + ∑ a ∈ s \ front, f a := by
      rw [add_comm]


theorem tail_sum_nonneg {s front : Finset α} {f : α → ℝ}
    (hf : ∀ a, a ∈ s → a ∉ front → 0 ≤ f a) :
    0 ≤ ∑ a ∈ s \ front, f a := by
  exact Finset.sum_nonneg fun a ha => by
    have htail : a ∈ s ∧ a ∉ front := by
      simpa using ha
    exact hf a htail.1 htail.2


theorem tail_sum_le_envelope_sum {s front : Finset α}
    {f envelope : α → ℝ}
    (henv : ∀ a, a ∈ s → a ∉ front → f a ≤ envelope a) :
    (∑ a ∈ s \ front, f a) ≤ ∑ a ∈ s \ front, envelope a := by
  exact Finset.sum_le_sum fun a ha => by
    have htail : a ∈ s ∧ a ∉ front := by
      simpa using ha
    exact henv a htail.1 htail.2



structure FiniteSupportCertificate (α : Type*) [DecidableEq α] where
  support : Finset α
  finitePrefix : Finset α
  finitePrefix_subset_support : finitePrefix ⊆ support
  weight : α → ℝ
  envelope : α → ℝ
  tailBound : ℝ
  zero_off_support : ∀ a, a ∉ support → weight a = 0
  weight_nonneg : ∀ a, 0 ≤ weight a
  envelope_nonneg_on_tail : ∀ a, a ∈ support → a ∉ finitePrefix → 0 ≤ envelope a
  weight_le_envelope_on_tail :
    ∀ a, a ∈ support → a ∉ finitePrefix → weight a ≤ envelope a
  envelope_tail_sum_le :
    (∑ a ∈ support \ finitePrefix, envelope a) ≤ tailBound

namespace FiniteSupportCertificate

variable (C : FiniteSupportCertificate α)



def tailSupport : Finset α :=
  C.support \ C.finitePrefix

@[simp] theorem mem_tailSupport {a : α} :
    a ∈ C.tailSupport ↔ a ∈ C.support ∧ a ∉ C.finitePrefix := by
  simp [tailSupport]


theorem summable_weight : Summable C.weight :=
  summable_of_ne_finset_zero (s := C.support) C.zero_off_support


theorem hasSum_weight :
    HasSum C.weight (∑ a ∈ C.support, C.weight a) :=
  hasSum_sum_of_ne_finset_zero (s := C.support) C.zero_off_support



theorem tsum_eq_support_sum :
    (∑' a, C.weight a) = ∑ a ∈ C.support, C.weight a :=
  tsum_eq_sum (s := C.support) C.zero_off_support



theorem support_sum_eq_prefix_add_tail :
    (∑ a ∈ C.support, C.weight a) =
      (∑ a ∈ C.finitePrefix, C.weight a) +
        ∑ a ∈ C.tailSupport, C.weight a := by
  simpa [tailSupport] using
    sum_eq_prefix_add_tail C.finitePrefix_subset_support C.weight



theorem tsum_eq_prefix_add_tail :
    (∑' a, C.weight a) =
      (∑ a ∈ C.finitePrefix, C.weight a) +
        ∑ a ∈ C.tailSupport, C.weight a := by
  rw [C.tsum_eq_support_sum, C.support_sum_eq_prefix_add_tail]


theorem prefix_sum_nonneg :
    0 ≤ ∑ a ∈ C.finitePrefix, C.weight a :=
  sum_nonneg_on fun a _ => C.weight_nonneg a


theorem tail_sum_nonneg :
    0 ≤ ∑ a ∈ C.tailSupport, C.weight a := by
  simpa [tailSupport] using
    StatMech.Exact3D.TailSummability.tail_sum_nonneg
      (s := C.support) (front := C.finitePrefix)
      (f := C.weight)
      (fun a _ _ => C.weight_nonneg a)


theorem tsum_nonneg :
    0 ≤ ∑' a, C.weight a := by
  rw [C.tsum_eq_prefix_add_tail]
  exact add_nonneg C.prefix_sum_nonneg C.tail_sum_nonneg


theorem envelope_tail_sum_nonneg :
    0 ≤ ∑ a ∈ C.tailSupport, C.envelope a := by
  simpa [tailSupport] using
    StatMech.Exact3D.TailSummability.tail_sum_nonneg
      (s := C.support) (front := C.finitePrefix)
      (f := C.envelope)
      C.envelope_nonneg_on_tail


theorem tail_sum_le_envelope_sum :
    (∑ a ∈ C.tailSupport, C.weight a) ≤
      ∑ a ∈ C.tailSupport, C.envelope a := by
  simpa [tailSupport] using
    StatMech.Exact3D.TailSummability.tail_sum_le_envelope_sum
      (s := C.support) (front := C.finitePrefix)
      (f := C.weight) (envelope := C.envelope)
      C.weight_le_envelope_on_tail


theorem tail_sum_le_bound :
    (∑ a ∈ C.tailSupport, C.weight a) ≤ C.tailBound :=
  le_trans C.tail_sum_le_envelope_sum <| by
    simpa [tailSupport] using C.envelope_tail_sum_le



theorem tailBound_nonneg : 0 ≤ C.tailBound :=
  le_trans C.envelope_tail_sum_nonneg <| by
    simpa [tailSupport] using C.envelope_tail_sum_le



def with_larger_tailBound {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    FiniteSupportCertificate α where
  support := C.support
  finitePrefix := C.finitePrefix
  finitePrefix_subset_support := C.finitePrefix_subset_support
  weight := C.weight
  envelope := C.envelope
  tailBound := tailBound'
  zero_off_support := C.zero_off_support
  weight_nonneg := C.weight_nonneg
  envelope_nonneg_on_tail := C.envelope_nonneg_on_tail
  weight_le_envelope_on_tail := C.weight_le_envelope_on_tail
  envelope_tail_sum_le := le_trans C.envelope_tail_sum_le hle

@[simp] theorem with_larger_tailBound_support {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).support = C.support :=
  rfl

@[simp] theorem with_larger_tailBound_finitePrefix {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).finitePrefix = C.finitePrefix :=
  rfl

@[simp] theorem with_larger_tailBound_weight {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).weight = C.weight :=
  rfl

@[simp] theorem with_larger_tailBound_envelope {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).envelope = C.envelope :=
  rfl

@[simp] theorem with_larger_tailBound_tailBound {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (C.with_larger_tailBound hle).tailBound = tailBound' :=
  rfl





def with_tailEnvelope_and_tailBound (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    FiniteSupportCertificate α where
  support := C.support
  finitePrefix := C.finitePrefix
  finitePrefix_subset_support := C.finitePrefix_subset_support
  weight := C.weight
  envelope := envelope'
  tailBound := tailBound'
  zero_off_support := C.zero_off_support
  weight_nonneg := C.weight_nonneg
  envelope_nonneg_on_tail := henvelope_nonneg
  weight_le_envelope_on_tail := hweight_le
  envelope_tail_sum_le := henvelope_sum

@[simp] theorem with_tailEnvelope_and_tailBound_support
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg
      hweight_le henvelope_sum).support = C.support :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBound_finitePrefix
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg
      hweight_le henvelope_sum).finitePrefix = C.finitePrefix :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBound_weight
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg
      hweight_le henvelope_sum).weight = C.weight :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBound_envelope
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg
      hweight_le henvelope_sum).envelope = envelope' :=
  rfl

@[simp] theorem with_tailEnvelope_and_tailBound_tailBound
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ C.support → a ∉ C.finitePrefix →
        C.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
    (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg
      hweight_le henvelope_sum).tailBound = tailBound' :=
  rfl


theorem tsum_le_prefix_sum_add_tailBound :
    (∑' a, C.weight a) ≤
      (∑ a ∈ C.finitePrefix, C.weight a) + C.tailBound := by
  calc
    (∑' a, C.weight a) =
        (∑ a ∈ C.finitePrefix, C.weight a) +
          ∑ a ∈ C.tailSupport, C.weight a :=
      C.tsum_eq_prefix_add_tail
    _ ≤ (∑ a ∈ C.finitePrefix, C.weight a) + C.tailBound :=
      add_le_add (le_refl _) C.tail_sum_le_bound



theorem tsum_le_prefix_sum_add_of_tailBound_le {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (∑' a, C.weight a) ≤
      (∑ a ∈ C.finitePrefix, C.weight a) + tailBound' :=
  le_trans C.tsum_le_prefix_sum_add_tailBound (add_le_add le_rfl hle)

end FiniteSupportCertificate

end TailSummability

namespace ContributionSplit

variable {α : Type*}


theorem summable_total_of_zero_off_support (S : ContributionSplit α)
    (support : Finset α)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0) :
    Summable S.totalContribution :=
  summable_of_ne_finset_zero (s := support) hzero


theorem tsum_total_eq_sum_of_zero_off_support (S : ContributionSplit α)
    (support : Finset α)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0) :
    (∑' a, S.totalContribution a) = ∑ a ∈ support, S.totalContribution a :=
  tsum_eq_sum (s := support) hzero



theorem total_le_finiteBound_add_tailEnvelopeOn
    {Case : Type*} [DecidableEq Case]
    (S : ContributionSplit α) (support : Finset α)
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {finiteBound : ℝ} (tailEnvelope : α → ℝ)
    (hadd : S.Additive)
    (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    {a : α} (ha : a ∈ support) :
    S.totalContribution a ≤ finiteBound + tailEnvelope a := by
  calc
    S.totalContribution a =
        S.finiteContribution a + S.tailContribution a := hadd a
    _ ≤ finiteBound + tailEnvelope a :=
      add_le_add (finite_le_of_tableUpperBound hfinite a) (htail a ha)






noncomputable def finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    {Case : Type*} [DecidableEq α] [DecidableEq Case]
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
    TailSummability.FiniteSupportCertificate α where
  support := support
  finitePrefix := finitePrefix
  finitePrefix_subset_support := hprefix
  weight := S.totalContribution
  envelope := fun a => finiteBound + tailEnvelope a
  tailBound := ((support \ finitePrefix).card : ℝ) * finiteBound + tailEnvelopeBound
  zero_off_support := hzero
  weight_nonneg := hnonneg
  envelope_nonneg_on_tail := by
    intro a ha _haPrefix
    exact le_trans (hnonneg a)
      (S.total_le_finiteBound_add_tailEnvelopeOn support tailEnvelope
        hadd hfinite htail ha)
  weight_le_envelope_on_tail := by
    intro a ha _haPrefix
    exact S.total_le_finiteBound_add_tailEnvelopeOn support tailEnvelope
      hadd hfinite htail ha
  envelope_tail_sum_le := by
    calc
      (∑ a ∈ support \ finitePrefix, (finiteBound + tailEnvelope a)) =
          (∑ _a ∈ support \ finitePrefix, finiteBound) +
            ∑ a ∈ support \ finitePrefix, tailEnvelope a := by
        rw [Finset.sum_add_distrib]
      _ = ((support \ finitePrefix).card : ℝ) * finiteBound +
            ∑ a ∈ support \ finitePrefix, tailEnvelope a := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((support \ finitePrefix).card : ℝ) * finiteBound +
            tailEnvelopeBound := by
        exact add_le_add (le_refl _) htailSum



theorem tsum_total_le_prefix_sum_add_tableTailBound
    {Case : Type*} [DecidableEq α] [DecidableEq Case]
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
    (∑' a, S.totalContribution a) ≤
      (∑ a ∈ finitePrefix, S.totalContribution a) +
        (((support \ finitePrefix).card : ℝ) * finiteBound +
          tailEnvelopeBound) :=
  by
    simpa [finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn] using
      (S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
        support finitePrefix tailEnvelope hprefix hzero hnonneg hadd hfinite htail
        htailSum).tsum_le_prefix_sum_add_tailBound





theorem tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    {Case : Type*} [DecidableEq Case]
    (S : ContributionSplit α) (support : Finset α)
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {finiteBound tailBound : ℝ} (tailEnvelope : α → ℝ)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hadd : S.Additive)
    (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (support.card : ℝ) * finiteBound + tailBound := by
  rw [S.tsum_total_eq_sum_of_zero_off_support support hzero]
  exact S.total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn support
    tailEnvelope hadd hfinite htail htailSum

end ContributionSplit

end Exact3D
end StatMech
