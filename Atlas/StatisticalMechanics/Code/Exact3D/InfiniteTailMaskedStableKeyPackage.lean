/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.InfiniteTailMaskedTableWitnessPackage
import Code.Exact3D.StableKeyTailBridge

open scoped BigOperators










namespace StatMech
namespace Exact3D

open BoundedPolymerCase

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι : Type*}



noncomputable def ofExternalStableKeyRowsFiniteCutoffStableKey
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound prefixTailBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hcover : ∀ c : FiniteCutoffCase d K,
      stableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      S.finiteContribution c =
        keyValue (classifyFiniteCutoffStableKey K c))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
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
  table := externalStableKeyIntervalRowTable rows fallback
  classify := classifyFiniteCutoffStableKey K
  finiteBound := finiteBound
  prefixTailBound := prefixTailBound
  tailBound := tailBound
  tailEnvelope := tailEnvelope
  total_nonneg := htotal_nonneg
  additive := hadd
  finiteTable :=
    externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffStableKey_of_keyValue
      K rows fallback S.finiteContribution keyValue hcover hvalue hrow hrowUpper
  tailEnvelopeOnPrefix := htail_on_prefix
  prefixTailEnvelopeSum_le := htailPrefixSum_le
  finite_zero_off_prefix := hfinite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := henvelope_nonneg_off
  tail_le_tailEnvelope_off_prefix := htail_le_tailEnvelope
  summable_masked_tailEnvelope := hsummable_masked
  masked_tailEnvelope_tsum_le := hmasked_tsum_le



noncomputable def ofExternalStableKeyRowsFiniteCutoffMinimalCubic
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound prefixTailBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hcover : ∀ c : FiniteCutoffCase d K,
      classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      S.finiteContribution c =
        keyValue (classifyFiniteCutoffMinimalCubicStableKey K c))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
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
  table := externalStableKeyIntervalRowTable rows fallback
  classify := classifyFiniteCutoffMinimalCubicStableKey K
  finiteBound := finiteBound
  prefixTailBound := prefixTailBound
  tailBound := tailBound
  tailEnvelope := tailEnvelope
  total_nonneg := htotal_nonneg
  additive := hadd
  finiteTable :=
    externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffMinimalCubic_of_keyValue
      K rows fallback S.finiteContribution keyValue hcover hvalue hrow hrowUpper
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
