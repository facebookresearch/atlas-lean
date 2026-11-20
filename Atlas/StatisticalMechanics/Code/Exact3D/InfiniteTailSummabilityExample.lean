/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.InfiniteTailSummability
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

open scoped BigOperators









namespace StatMech
namespace Exact3D

namespace InfiniteTailSummabilityExample

open TailSummability

noncomputable section


def geometricHalfTailWeight (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ (n + 1)


theorem geometricHalfTailWeight_nonneg (n : ℕ) :
    0 ≤ geometricHalfTailWeight n := by
  unfold geometricHalfTailWeight
  exact pow_nonneg (by norm_num) _


theorem geometricHalfTailWeight_summable :
    Summable geometricHalfTailWeight := by
  have hgeom :
      Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
    summable_geometric_of_abs_lt_one (by norm_num)
  refine (hgeom.mul_left ((1 : ℝ) / 2)).congr ?_
  intro n
  unfold geometricHalfTailWeight
  rw [pow_succ']


theorem geometricHalfTailWeight_tsum_eq_one :
    (∑' n : ℕ, geometricHalfTailWeight n) = 1 := by
  have hgeom_tsum :
      (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2 := by
    rw [tsum_geometric_of_abs_lt_one (by norm_num :
      |((1 : ℝ) / 2)| < 1)]
    norm_num
  calc
    (∑' n : ℕ, geometricHalfTailWeight n) =
        ∑' n : ℕ, ((1 : ℝ) / 2) * (((1 : ℝ) / 2) ^ n) := by
      refine tsum_congr ?_
      intro n
      unfold geometricHalfTailWeight
      rw [pow_succ']
    _ = ((1 : ℝ) / 2) *
        (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) := by
      rw [tsum_mul_left]
    _ = 1 := by
      rw [hgeom_tsum]
      norm_num


def geometricHalfInfiniteTailCertificate :
    InfiniteTailCertificate ℕ where
  finitePrefix := ∅
  weight := geometricHalfTailWeight
  prefixWeight := fun _ => 0
  tailWeight := geometricHalfTailWeight
  tailBound := 1
  prefix_eq_weight_on_prefix := by
    intro _ ha
    simp at ha
  prefixWeight_zero_off_prefix := by
    intro _ _
    rfl
  tailWeight_zero_on_prefix := by
    intro _ ha
    simp at ha
  decomposition := by
    intro n
    simp
  prefixWeight_nonneg := by
    intro _
    norm_num
  tailWeight_nonneg := geometricHalfTailWeight_nonneg
  summable_tail := geometricHalfTailWeight_summable
  tail_tsum_le := by
    rw [geometricHalfTailWeight_tsum_eq_one]





def geometricHalfInfiniteTailCertificateFromEnvelope :
    InfiniteTailCertificate ℕ :=
  InfiniteTailCertificate.of_tailEnvelope
    (∅ : Finset ℕ)
    geometricHalfTailWeight
    geometricHalfTailWeight
    geometricHalfTailWeight_nonneg
    geometricHalfTailWeight_nonneg
    (by
      intro _ _
      rfl)
    geometricHalfTailWeight_summable
    (by
      rw [geometricHalfTailWeight_tsum_eq_one])


theorem geometricHalfInfiniteTailCertificate_tsum_weight_le_one :
    (∑' n : ℕ, geometricHalfInfiniteTailCertificate.weight n) ≤ 1 := by
  simpa [geometricHalfInfiniteTailCertificate,
    TailSummability.InfiniteTailCertificate.prefixSum] using
    geometricHalfInfiniteTailCertificate.tsum_weight_le_prefixSum_add_tailBound


theorem geometricHalfInfiniteTailCertificateFromEnvelope_tsum_weight_le_one :
    (∑' n : ℕ, geometricHalfInfiniteTailCertificateFromEnvelope.weight n) ≤
      1 := by
  simpa [geometricHalfInfiniteTailCertificateFromEnvelope,
    TailSummability.InfiniteTailCertificate.of_tailEnvelope,
    TailSummability.InfiniteTailCertificate.prefixSum] using
    geometricHalfInfiniteTailCertificateFromEnvelope.tsum_weight_le_prefixSum_add_tailBound


def maskedGeometricHalfTailWeight (n : ℕ) : ℝ :=
  if n ∈ ({0} : Finset ℕ) then 0 else geometricHalfTailWeight n


theorem maskedGeometricHalfTailWeight_nonneg (n : ℕ) :
    0 ≤ maskedGeometricHalfTailWeight n := by
  unfold maskedGeometricHalfTailWeight
  by_cases hn : n ∈ ({0} : Finset ℕ)
  · simp [hn]
  · simpa [hn] using geometricHalfTailWeight_nonneg n


theorem maskedGeometricHalfTailWeight_le_geometricHalfTailWeight (n : ℕ) :
    maskedGeometricHalfTailWeight n ≤ geometricHalfTailWeight n := by
  unfold maskedGeometricHalfTailWeight
  by_cases hn : n ∈ ({0} : Finset ℕ)
  · simpa [hn] using geometricHalfTailWeight_nonneg n
  · simp [hn]


theorem maskedGeometricHalfTailWeight_summable :
    Summable maskedGeometricHalfTailWeight :=
  Summable.of_nonneg_of_le maskedGeometricHalfTailWeight_nonneg
    maskedGeometricHalfTailWeight_le_geometricHalfTailWeight
    geometricHalfTailWeight_summable


theorem maskedGeometricHalfTailWeight_tsum_le_one :
    (∑' n : ℕ, maskedGeometricHalfTailWeight n) ≤ 1 :=
  le_trans
    (Summable.tsum_le_tsum
      maskedGeometricHalfTailWeight_le_geometricHalfTailWeight
      maskedGeometricHalfTailWeight_summable
      geometricHalfTailWeight_summable)
    (by rw [geometricHalfTailWeight_tsum_eq_one])


def geometricHalfInfiniteTailCertificateFromMaskedEnvelope :
    InfiniteTailCertificate ℕ :=
  InfiniteTailCertificate.of_masked_tailEnvelope
    ({0} : Finset ℕ)
    geometricHalfTailWeight
    geometricHalfTailWeight
    geometricHalfTailWeight_nonneg
    (by
      intro n _
      exact geometricHalfTailWeight_nonneg n)
    (by
      intro _ _
      exact le_rfl)
    (by
      refine maskedGeometricHalfTailWeight_summable.congr ?_
      intro n
      simp [maskedGeometricHalfTailWeight])
    (by
      convert maskedGeometricHalfTailWeight_tsum_le_one using 1)


theorem geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tailBound :
    geometricHalfInfiniteTailCertificateFromMaskedEnvelope.tailBound = 1 :=
  rfl


theorem
    geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tsum_weight_le_prefixSum_add_one :
    (∑' n : ℕ,
        geometricHalfInfiniteTailCertificateFromMaskedEnvelope.weight n) ≤
      geometricHalfInfiniteTailCertificateFromMaskedEnvelope.prefixSum + 1 := by
  simpa [geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tailBound] using
    geometricHalfInfiniteTailCertificateFromMaskedEnvelope.tsum_weight_le_prefixSum_add_tailBound



def singletonFiniteCertificate :
    FiniteSupportCertificate ℕ where
  support := {0}
  finitePrefix := {0}
  finitePrefix_subset_support := by
    intro a ha
    simpa using ha
  weight := fun n => if n = 0 then (3 : ℝ) else 0
  envelope := fun _ => 0
  tailBound := 0
  zero_off_support := by
    intro a ha
    have hne : a ≠ 0 := by
      intro h
      exact ha (by simp [h])
    simp [hne]
  weight_nonneg := by
    intro a
    by_cases h : a = 0 <;> simp [h]
  envelope_nonneg_on_tail := by
    intro _ _ _
    norm_num
  weight_le_envelope_on_tail := by
    intro a hsupport hnotPrefix
    have ha0 : a = 0 := by
      simpa using hsupport
    exact False.elim (hnotPrefix (by simp [ha0]))
  envelope_tail_sum_le := by
    simp



def singletonFiniteAsInfinite :
    InfiniteTailCertificate ℕ :=
  singletonFiniteCertificate.toInfiniteTailCertificate


theorem singletonFiniteAsInfinite_prefixSum_eq_three :
    singletonFiniteAsInfinite.prefixSum = 3 := by
  norm_num [singletonFiniteAsInfinite, singletonFiniteCertificate,
    TailSummability.InfiniteTailCertificate.prefixSum]


theorem singletonFiniteAsInfinite_tsum_weight_le_three :
    (∑' n : ℕ, singletonFiniteAsInfinite.weight n) ≤ 3 := by
  have h :=
    singletonFiniteAsInfinite.tsum_weight_le_prefixSum_add_tailBound
  rw [singletonFiniteAsInfinite_prefixSum_eq_three] at h
  norm_num [singletonFiniteAsInfinite, singletonFiniteCertificate] at h ⊢

end

end InfiniteTailSummabilityExample

end Exact3D
end StatMech
