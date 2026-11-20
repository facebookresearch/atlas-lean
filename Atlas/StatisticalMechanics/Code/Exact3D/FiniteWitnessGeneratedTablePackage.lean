/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FiniteWitnessPackage
import Code.Exact3D.GeneratedTableTailBridge

open scoped BigOperators











namespace StatMech
namespace Exact3D

open BoundedPolymerCase

namespace FiniteWitnessPackage

variable {ι : Type*}



noncomputable def ofGeneratedIntervalTableFiniteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf : FiniteCutoffCase d K → RatInterval)
    (caseValue : FiniteCutoffCase d K → ℝ)
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hvalue : ∀ c,
      S.finiteContribution c =
        caseValue (classifyFiniteCutoffCoordinate K c))
    (hcase : ∀ c, (intervalOf c).MemR (caseValue c))
    (hupper : ∀ c,
      c ∈ (generatedIntervalTable intervalOf).cases →
        ((intervalOf c).upper : ℝ) ≤ finiteBound)
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
    finiteSupportCertificate_of_generatedIntervalTable_finiteCutoff
      K S intervalOf caseValue support finitePrefix tailEnvelope hprefix hzero
      hnonneg hadd hvalue hcase hupper htail htailSum



noncomputable def ofGeneratedCubicIntervalTableFiniteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf : CubicClass d K.radius K.maxDegree K.maxRange → RatInterval)
    (classValue : CubicClass d K.radius K.maxDegree K.maxRange → ℝ)
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hvalue : ∀ c,
      S.finiteContribution c =
        classValue (classifyFiniteCutoffCubicClass K c))
    (hclass : ∀ q, (intervalOf q).MemR (classValue q))
    (hupper : ∀ q,
      q ∈ (generatedCubicIntervalTable intervalOf).cases →
        ((intervalOf q).upper : ℝ) ≤ finiteBound)
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
    finiteSupportCertificate_of_generatedCubicIntervalTable_finiteCutoff
      K S intervalOf classValue support finitePrefix tailEnvelope hprefix hzero
      hnonneg hadd hvalue hclass hupper htail htailSum



noncomputable def ofGeneratedStableKeyIntervalTableFiniteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf : StableKey K.maxDegree K.maxRange → RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
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
    finiteSupportCertificate_of_generatedStableKeyIntervalTable_finiteCutoff
      K S intervalOf keyValue support finitePrefix tailEnvelope hprefix hzero
      hnonneg hadd hvalue hkey hupper htail htailSum



noncomputable def ofGeneratedMinimalCubicStableKeyTableFiniteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf : StableKey K.maxDegree K.maxRange → RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
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
    finiteSupportCertificate_of_generatedMinimalCubicStableKeyTable_finiteCutoff
      K S intervalOf keyValue support finitePrefix tailEnvelope hprefix hzero
      hnonneg hadd hvalue hkey hupper htail htailSum

end FiniteWitnessPackage

end Exact3D
end StatMech
