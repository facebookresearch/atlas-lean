/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.InfiniteTailMaskedTableWitnessPackage
import Code.Exact3D.GeneratedTableTailBridge

open scoped BigOperators










namespace StatMech
namespace Exact3D

open BoundedPolymerCase

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι : Type*}



noncomputable def ofGeneratedIntervalTableFiniteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf : FiniteCutoffCase d K → RatInterval)
    (caseValue : FiniteCutoffCase d K → ℝ)
    (finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound prefixTailBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hvalue : ∀ c,
      S.finiteContribution c =
        caseValue (classifyFiniteCutoffCoordinate K c))
    (hcase : ∀ c, (intervalOf c).MemR (caseValue c))
    (hupper : ∀ c,
      c ∈ (generatedIntervalTable intervalOf).cases →
        ((intervalOf c).upper : ℝ) ≤ finiteBound)
    (htail_on_prefix : S.TailEnvelopeOn finitePrefix tailEnvelope)
    (htailPrefixSum_le :
      (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound)
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
    InfiniteTailMaskedTableWitnessPackage
      (Case := FiniteCutoffCase d K) (α := FiniteCutoffCoordinate d K) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  S := S
  finitePrefix := finitePrefix
  table := generatedIntervalTable intervalOf
  classify := classifyFiniteCutoffCoordinate K
  finiteBound := finiteBound
  prefixTailBound := prefixTailBound
  tailBound := tailBound
  tailEnvelope := tailEnvelope
  total_nonneg := htotal_nonneg
  additive := hadd
  finiteTable :=
    generatedIntervalTable_finiteTableUpperBound_finiteCutoff_of_caseValue
      K intervalOf S.finiteContribution caseValue hvalue hcase hupper
  tailEnvelopeOnPrefix := htail_on_prefix
  prefixTailEnvelopeSum_le := htailPrefixSum_le
  finite_zero_off_prefix := hfinite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := henvelope_nonneg_off
  tail_le_tailEnvelope_off_prefix := htail_le_tailEnvelope
  summable_masked_tailEnvelope := hsummable_masked
  masked_tailEnvelope_tsum_le := hmasked_tsum_le



noncomputable def ofGeneratedCubicIntervalTableFiniteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf : CubicClass d K.radius K.maxDegree K.maxRange → RatInterval)
    (classValue : CubicClass d K.radius K.maxDegree K.maxRange → ℝ)
    (finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound prefixTailBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hvalue : ∀ c,
      S.finiteContribution c =
        classValue (classifyFiniteCutoffCubicClass K c))
    (hclass : ∀ q, (intervalOf q).MemR (classValue q))
    (hupper : ∀ q,
      q ∈ (generatedCubicIntervalTable intervalOf).cases →
        ((intervalOf q).upper : ℝ) ≤ finiteBound)
    (htail_on_prefix : S.TailEnvelopeOn finitePrefix tailEnvelope)
    (htailPrefixSum_le :
      (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound)
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
    InfiniteTailMaskedTableWitnessPackage
      (Case := CubicClass d K.radius K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  S := S
  finitePrefix := finitePrefix
  table := generatedCubicIntervalTable intervalOf
  classify := classifyFiniteCutoffCubicClass K
  finiteBound := finiteBound
  prefixTailBound := prefixTailBound
  tailBound := tailBound
  tailEnvelope := tailEnvelope
  total_nonneg := htotal_nonneg
  additive := hadd
  finiteTable :=
    generatedCubicIntervalTable_finiteTableUpperBound_finiteCutoff_of_classValue
      K intervalOf S.finiteContribution classValue hvalue hclass hupper
  tailEnvelopeOnPrefix := htail_on_prefix
  prefixTailEnvelopeSum_le := htailPrefixSum_le
  finite_zero_off_prefix := hfinite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := henvelope_nonneg_off
  tail_le_tailEnvelope_off_prefix := htail_le_tailEnvelope
  summable_masked_tailEnvelope := hsummable_masked
  masked_tailEnvelope_tsum_le := hmasked_tsum_le



noncomputable def ofGeneratedStableKeyIntervalTableFiniteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf : StableKey K.maxDegree K.maxRange → RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound prefixTailBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hvalue : ∀ c,
      S.finiteContribution c =
        keyValue (classifyFiniteCutoffStableKey K c))
    (hkey : ∀ k,
      k ∈ (generatedStableKeyIntervalTable
          (d := d) (R := K.radius) intervalOf).cases →
        (intervalOf k).MemR (keyValue k))
    (hupper : ∀ k,
      k ∈ (generatedStableKeyIntervalTable
          (d := d) (R := K.radius) intervalOf).cases →
        ((intervalOf k).upper : ℝ) ≤ finiteBound)
    (htail_on_prefix : S.TailEnvelopeOn finitePrefix tailEnvelope)
    (htailPrefixSum_le :
      (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound)
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
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  S := S
  finitePrefix := finitePrefix
  table := generatedStableKeyIntervalTable (d := d) (R := K.radius) intervalOf
  classify := classifyFiniteCutoffStableKey K
  finiteBound := finiteBound
  prefixTailBound := prefixTailBound
  tailBound := tailBound
  tailEnvelope := tailEnvelope
  total_nonneg := htotal_nonneg
  additive := hadd
  finiteTable :=
    generatedStableKeyIntervalTable_finiteTableUpperBound_finiteCutoff_of_keyValue
      K intervalOf S.finiteContribution keyValue hvalue hkey hupper
  tailEnvelopeOnPrefix := htail_on_prefix
  prefixTailEnvelopeSum_le := htailPrefixSum_le
  finite_zero_off_prefix := hfinite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := henvelope_nonneg_off
  tail_le_tailEnvelope_off_prefix := htail_le_tailEnvelope
  summable_masked_tailEnvelope := hsummable_masked
  masked_tailEnvelope_tsum_le := hmasked_tsum_le



noncomputable def ofGeneratedMinimalCubicStableKeyTableFiniteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf : StableKey K.maxDegree K.maxRange → RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound prefixTailBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hvalue : ∀ c,
      S.finiteContribution c =
        keyValue (classifyFiniteCutoffMinimalCubicStableKey K c))
    (hkey : ∀ k,
      k ∈ (generatedMinimalCubicStableKeyTable
          (d := d) (R := K.radius) intervalOf).cases →
        (intervalOf k).MemR (keyValue k))
    (hupper : ∀ k,
      k ∈ (generatedMinimalCubicStableKeyTable
          (d := d) (R := K.radius) intervalOf).cases →
        ((intervalOf k).upper : ℝ) ≤ finiteBound)
    (htail_on_prefix : S.TailEnvelopeOn finitePrefix tailEnvelope)
    (htailPrefixSum_le :
      (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound)
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
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  S := S
  finitePrefix := finitePrefix
  table :=
    generatedMinimalCubicStableKeyTable (d := d) (R := K.radius) intervalOf
  classify := classifyFiniteCutoffMinimalCubicStableKey K
  finiteBound := finiteBound
  prefixTailBound := prefixTailBound
  tailBound := tailBound
  tailEnvelope := tailEnvelope
  total_nonneg := htotal_nonneg
  additive := hadd
  finiteTable :=
    generatedMinimalCubicStableKeyTable_finiteTableUpperBound_finiteCutoff_of_keyValue
      K intervalOf S.finiteContribution keyValue hvalue hkey hupper
  tailEnvelopeOnPrefix := htail_on_prefix
  prefixTailEnvelopeSum_le := htailPrefixSum_le
  finite_zero_off_prefix := hfinite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := henvelope_nonneg_off
  tail_le_tailEnvelope_off_prefix := htail_le_tailEnvelope
  summable_masked_tailEnvelope := hsummable_masked
  masked_tailEnvelope_tsum_le := hmasked_tsum_le

end InfiniteTailMaskedTableWitnessPackage

end Exact3D
end StatMech
