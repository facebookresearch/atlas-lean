/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FiniteWitnessPackage
import Code.Exact3D.StableKeyTailBridge

open scoped BigOperators










namespace StatMech
namespace Exact3D

open BoundedPolymerCase

namespace FiniteWitnessPackage

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
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
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
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    FiniteWitnessPackage (α := FiniteCutoffCoordinate d K) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  tailCertificate :=
    finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffStableKey
      K S rows fallback keyValue support finitePrefix tailEnvelope hprefix hzero
      hnonneg hadd hcover hvalue hrow hrowUpper htail htailSum



noncomputable def ofExternalStableKeyRowsFiniteCutoffMinimalCubic
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
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
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    FiniteWitnessPackage (α := FiniteCutoffCoordinate d K) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  tailCertificate :=
    finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic
      K S rows fallback keyValue support finitePrefix tailEnvelope hprefix hzero
      hnonneg hadd hcover hvalue hrow hrowUpper htail htailSum

end FiniteWitnessPackage

end Exact3D
end StatMech
