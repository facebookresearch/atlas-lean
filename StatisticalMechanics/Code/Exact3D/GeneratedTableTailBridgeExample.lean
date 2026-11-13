/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.GeneratedTableTailBridge

open scoped BigOperators










namespace StatMech
namespace Exact3D
namespace BoundedPolymerCase
namespace GeneratedTableTailBridgeExample


def zeroOneInterval : RatInterval where
  lower := 0
  upper := 1
  lower_le_upper := by norm_num


theorem zeroOneInterval_upper_le_one :
    ((zeroOneInterval.upper : ℚ) : ℝ) ≤ 1 := by
  norm_num [zeroOneInterval]


noncomputable def keyImageIndicator {α Key : Type*} [DecidableEq Key]
    (support : Finset α) (classifier : α → Key) (k : Key) : ℝ :=
  if k ∈ support.image classifier then 1 else 0


theorem zeroOneInterval_memR_keyImageIndicator {α Key : Type*}
    [DecidableEq Key] (support : Finset α) (classifier : α → Key)
    (k : Key) :
    zeroOneInterval.MemR (keyImageIndicator support classifier k) := by
  by_cases hk : k ∈ support.image classifier
  · simp [keyImageIndicator, hk, zeroOneInterval, RatInterval.MemR]
  · simp [keyImageIndicator, hk, zeroOneInterval, RatInterval.MemR]



noncomputable def keyImageIndicatorSplit {α Key : Type*}
    [DecidableEq Key] (support : Finset α) (classifier : α → Key) :
    ContributionSplit α where
  finiteContribution := fun a => keyImageIndicator support classifier (classifier a)
  tailContribution := fun _ => 0
  totalContribution := fun a => keyImageIndicator support classifier (classifier a)


theorem keyImageIndicatorSplit_additive {α Key : Type*}
    [DecidableEq Key] (support : Finset α) (classifier : α → Key) :
    (keyImageIndicatorSplit support classifier).Additive := by
  intro a
  simp [keyImageIndicatorSplit]


theorem keyImageIndicatorSplit_total_nonneg {α Key : Type*}
    [DecidableEq Key] (support : Finset α) (classifier : α → Key) :
    ∀ a, 0 ≤ (keyImageIndicatorSplit support classifier).totalContribution a := by
  intro a
  change 0 ≤ (if classifier a ∈ support.image classifier then (1 : ℝ) else 0)
  by_cases ha : classifier a ∈ support.image classifier
  · rw [if_pos ha]
    norm_num
  · rw [if_neg ha]



theorem keyImageIndicatorSplit_zero_off_saturated_support {α Key : Type*}
    [DecidableEq Key] (support : Finset α) (classifier : α → Key)
    (hsaturated :
      ∀ a, classifier a ∈ support.image classifier → a ∈ support) :
    ∀ a, a ∉ support →
      (keyImageIndicatorSplit support classifier).totalContribution a = 0 := by
  intro a ha
  change (if classifier a ∈ support.image classifier then (1 : ℝ) else 0) = 0
  exact if_neg (fun hkey => ha (hsaturated a hkey))



theorem keyImageIndicatorSplit_finite_zero_off_saturated_support
    {α Key : Type*} [DecidableEq Key] (support : Finset α)
    (classifier : α → Key)
    (hsaturated :
      ∀ a, classifier a ∈ support.image classifier → a ∈ support) :
    ∀ a, a ∉ support →
      (keyImageIndicatorSplit support classifier).finiteContribution a = 0 := by
  intro a ha
  simpa [keyImageIndicatorSplit] using
    keyImageIndicatorSplit_zero_off_saturated_support support classifier
      hsaturated a ha


theorem keyImageIndicatorSplit_tailEnvelopeOn_zero {α Key : Type*}
    [DecidableEq Key] (support : Finset α) (classifier : α → Key) :
    (keyImageIndicatorSplit support classifier).TailEnvelopeOn support
      (fun _ => (0 : ℝ)) := by
  intro _ _
  simp [keyImageIndicatorSplit]



theorem keyImageIndicatorSplit_tailContribution_nonpos_off_support
    {α Key : Type*} [DecidableEq Key] (support : Finset α)
    (classifier : α → Key) :
    ∀ a, a ∉ support →
      (keyImageIndicatorSplit support classifier).tailContribution a ≤ 0 := by
  intro _ _
  simp [keyImageIndicatorSplit]


theorem zero_tailEnvelope_sum_le {α : Type*} (support : Finset α) :
    (∑ _a ∈ support, (0 : ℝ)) ≤ 0 := by
  simp



theorem generatedStableKeyIndicator_tsum_total_le {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (∑' a,
      (keyImageIndicatorSplit support
        (classifyFiniteCutoffStableKey K)).totalContribution a) ≤
      (support.card : ℝ) * 1 + 0 := by
  exact tsum_total_le_of_generatedStableKeyIntervalTable_finiteCutoff
    K
    (keyImageIndicatorSplit support (classifyFiniteCutoffStableKey K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffStableKey K))
    support
    (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffStableKey K) hsaturated)
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffStableKey K))
    (fun _ => rfl)
    (fun k _hk =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffStableKey K) k)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffStableKey K))
    (zero_tailEnvelope_sum_le support)



theorem generatedMinimalCubicStableKeyIndicator_tsum_total_le {d : ℕ}
    (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (∑' a,
      (keyImageIndicatorSplit support
        (classifyFiniteCutoffMinimalCubicStableKey K)).totalContribution a) ≤
      (support.card : ℝ) * 1 + 0 := by
  exact tsum_total_le_of_generatedMinimalCubicStableKeyTable_finiteCutoff
    K
    (keyImageIndicatorSplit support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffMinimalCubicStableKey K))
    support
    (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffMinimalCubicStableKey K) hsaturated)
    (keyImageIndicatorSplit_additive support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (fun _ => rfl)
    (fun k _hk =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffMinimalCubicStableKey K) k)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (zero_tailEnvelope_sum_le support)



theorem generatedBoundedCaseIndicator_tsum_total_le {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (∑' a,
      (keyImageIndicatorSplit support
        (classifyFiniteCutoffCoordinate K)).totalContribution a) ≤
      (support.card : ℝ) * 1 + 0 := by
  exact tsum_total_le_of_generatedIntervalTable_finiteCutoff
    K
    (keyImageIndicatorSplit support (classifyFiniteCutoffCoordinate K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffCoordinate K))
    support
    (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffCoordinate K) hsaturated)
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffCoordinate K))
    (fun _ => rfl)
    (fun k =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffCoordinate K) k)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffCoordinate K))
    (zero_tailEnvelope_sum_le support)


theorem generatedCubicClassIndicator_tsum_total_le {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (∑' a,
      (keyImageIndicatorSplit support
        (classifyFiniteCutoffCubicClass K)).totalContribution a) ≤
      (support.card : ℝ) * 1 + 0 := by
  exact tsum_total_le_of_generatedCubicIntervalTable_finiteCutoff
    K
    (keyImageIndicatorSplit support (classifyFiniteCutoffCubicClass K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffCubicClass K))
    support
    (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffCubicClass K) hsaturated)
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffCubicClass K))
    (fun _ => rfl)
    (fun q =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffCubicClass K) q)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffCubicClass K))
    (zero_tailEnvelope_sum_le support)



noncomputable def generatedBoundedCaseIndicator_finiteSupportCertificate
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  finiteSupportCertificate_of_generatedIntervalTable_finiteCutoff
    (finiteBound := (1 : ℝ)) (tailEnvelopeBound := (0 : ℝ))
    K
    (keyImageIndicatorSplit support (classifyFiniteCutoffCoordinate K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffCoordinate K))
    support ∅
    (fun _ => (0 : ℝ))
    (by simp)
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffCoordinate K) hsaturated)
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffCoordinate K))
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffCoordinate K))
    (fun _ => rfl)
    (fun c => zeroOneInterval_memR_keyImageIndicator support
      (classifyFiniteCutoffCoordinate K) c)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffCoordinate K))
    (by simp)



noncomputable def generatedCubicClassIndicator_finiteSupportCertificate
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  finiteSupportCertificate_of_generatedCubicIntervalTable_finiteCutoff
    (finiteBound := (1 : ℝ)) (tailEnvelopeBound := (0 : ℝ))
    K
    (keyImageIndicatorSplit support (classifyFiniteCutoffCubicClass K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffCubicClass K))
    support ∅
    (fun _ => (0 : ℝ))
    (by simp)
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffCubicClass K) hsaturated)
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffCubicClass K))
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffCubicClass K))
    (fun _ => rfl)
    (fun q => zeroOneInterval_memR_keyImageIndicator support
      (classifyFiniteCutoffCubicClass K) q)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffCubicClass K))
    (by simp)



noncomputable def generatedStableKeyIndicator_finiteSupportCertificate
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  finiteSupportCertificate_of_generatedStableKeyIntervalTable_finiteCutoff
    (finiteBound := (1 : ℝ)) (tailEnvelopeBound := (0 : ℝ))
    K
    (keyImageIndicatorSplit support (classifyFiniteCutoffStableKey K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffStableKey K))
    support ∅
    (fun _ => (0 : ℝ))
    (by simp)
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffStableKey K) hsaturated)
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffStableKey K))
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffStableKey K))
    (fun _ => rfl)
    (fun k _hk =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffStableKey K) k)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffStableKey K))
    (by simp)




noncomputable def generatedMinimalCubicStableKeyIndicator_finiteSupportCertificate
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  finiteSupportCertificate_of_generatedMinimalCubicStableKeyTable_finiteCutoff
    (finiteBound := (1 : ℝ)) (tailEnvelopeBound := (0 : ℝ))
    K
    (keyImageIndicatorSplit support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffMinimalCubicStableKey K))
    support ∅
    (fun _ => (0 : ℝ))
    (by simp)
    (keyImageIndicatorSplit_zero_off_saturated_support support
      (classifyFiniteCutoffMinimalCubicStableKey K) hsaturated)
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (keyImageIndicatorSplit_additive support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (fun _ => rfl)
    (fun k _hk =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffMinimalCubicStableKey K) k)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (by simp)

end GeneratedTableTailBridgeExample
end BoundedPolymerCase
end Exact3D
end StatMech
