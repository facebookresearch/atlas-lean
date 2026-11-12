/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.StableKeyTailBridge

open scoped BigOperators










namespace StatMech
namespace Exact3D
namespace BoundedPolymerCase


noncomputable def classifyFiniteCutoffCubicClass {d : ℕ} (K : TailCutoff)
    (c : FiniteCutoffCoordinate d K) :
    CubicClass d K.radius K.maxDegree K.maxRange :=
  cubicClass (classifyFiniteCutoffCoordinate K c)



theorem generatedIntervalTable_finiteTableUpperBound_finiteCutoff_of_caseValue
    {d : ℕ} (K : TailCutoff)
    (intervalOf : FiniteCutoffCase d K → RatInterval)
    (value : FiniteCutoffCoordinate d K → ℝ)
    (caseValue : FiniteCutoffCase d K → ℝ)
    {finiteBound : ℝ}
    (hvalue : ∀ c,
      value c = caseValue (classifyFiniteCutoffCoordinate K c))
    (hcase : ∀ c, (intervalOf c).MemR (caseValue c))
    (hupper : ∀ c,
      c ∈ (generatedIntervalTable intervalOf).cases →
        ((intervalOf c).upper : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound
      (generatedIntervalTable intervalOf)
      (classifyFiniteCutoffCoordinate K) value finiteBound := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact exhaustiveTable_covers d K.radius K.maxDegree K.maxRange
      (classifyFiniteCutoffCoordinate K c)
  · intro c
    rw [hvalue c]
    exact hcase (classifyFiniteCutoffCoordinate K c)
  · intro c hc
    exact hupper c hc



theorem generatedCubicIntervalTable_finiteTableUpperBound_finiteCutoff_of_classValue
    {d : ℕ} (K : TailCutoff)
    (intervalOf :
      CubicClass d K.radius K.maxDegree K.maxRange → RatInterval)
    (value : FiniteCutoffCoordinate d K → ℝ)
    (classValue :
      CubicClass d K.radius K.maxDegree K.maxRange → ℝ)
    {finiteBound : ℝ}
    (hvalue : ∀ c,
      value c = classValue (classifyFiniteCutoffCubicClass K c))
    (hclass : ∀ q, (intervalOf q).MemR (classValue q))
    (hupper : ∀ q,
      q ∈ (generatedCubicIntervalTable intervalOf).cases →
        ((intervalOf q).upper : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound
      (generatedCubicIntervalTable intervalOf)
      (classifyFiniteCutoffCubicClass K) value finiteBound := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact exhaustiveCubicClassTable_covers d K.radius K.maxDegree K.maxRange
      (classifyFiniteCutoffCoordinate K c)
  · intro c
    rw [hvalue c]
    exact hclass (classifyFiniteCutoffCubicClass K c)
  · intro q hq
    exact hupper q hq



theorem generatedStableKeyIntervalTable_finiteTableUpperBound_finiteCutoff_of_keyValue
    {d : ℕ} (K : TailCutoff)
    (intervalOf : StableKey K.maxDegree K.maxRange → RatInterval)
    (value : FiniteCutoffCoordinate d K → ℝ)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    {finiteBound : ℝ}
    (hvalue : ∀ c,
      value c = keyValue (classifyFiniteCutoffStableKey K c))
    (hkey : ∀ k,
      k ∈ (generatedStableKeyIntervalTable
          (d := d) (R := K.radius) intervalOf).cases →
        (intervalOf k).MemR (keyValue k))
    (hupper : ∀ k,
      k ∈ (generatedStableKeyIntervalTable
          (d := d) (R := K.radius) intervalOf).cases →
        ((intervalOf k).upper : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound
      (generatedStableKeyIntervalTable (d := d) (R := K.radius) intervalOf)
      (classifyFiniteCutoffStableKey K) value finiteBound := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact (generatedStableKeyIntervalTable_covers_boundedCase
      (d := d) (R := K.radius) intervalOf) (classifyFiniteCutoffCoordinate K c)
  · intro c
    rw [hvalue c]
    exact hkey (classifyFiniteCutoffStableKey K c)
      ((generatedStableKeyIntervalTable_covers_boundedCase
        (d := d) (R := K.radius) intervalOf) (classifyFiniteCutoffCoordinate K c))
  · intro k hk
    exact hupper k hk



theorem generatedMinimalCubicStableKeyTable_finiteTableUpperBound_finiteCutoff_of_keyValue
    {d : ℕ} (K : TailCutoff)
    (intervalOf : StableKey K.maxDegree K.maxRange → RatInterval)
    (value : FiniteCutoffCoordinate d K → ℝ)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    {finiteBound : ℝ}
    (hvalue : ∀ c,
      value c = keyValue (classifyFiniteCutoffMinimalCubicStableKey K c))
    (hkey : ∀ k,
      k ∈ (generatedMinimalCubicStableKeyTable
          (d := d) (R := K.radius) intervalOf).cases →
        (intervalOf k).MemR (keyValue k))
    (hupper : ∀ k,
      k ∈ (generatedMinimalCubicStableKeyTable
          (d := d) (R := K.radius) intervalOf).cases →
        ((intervalOf k).upper : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound
      (generatedMinimalCubicStableKeyTable
        (d := d) (R := K.radius) intervalOf)
      (classifyFiniteCutoffMinimalCubicStableKey K) value finiteBound := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact (generatedMinimalCubicStableKeyTable_covers_boundedCase
      (d := d) (R := K.radius) intervalOf) (classifyFiniteCutoffCoordinate K c)
  · intro c
    rw [hvalue c]
    exact hkey (classifyFiniteCutoffMinimalCubicStableKey K c)
      ((generatedMinimalCubicStableKeyTable_covers_boundedCase
        (d := d) (R := K.radius) intervalOf) (classifyFiniteCutoffCoordinate K c))
  · intro k hk
    exact hupper k hk


theorem tsum_total_le_of_generatedStableKeyIntervalTable_finiteCutoff
    {d : ℕ} (K : TailCutoff)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf : StableKey K.maxDegree K.maxRange → RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
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
    (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (support.card : ℝ) * finiteBound + tailBound :=
  ContributionSplit.tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    S support tailEnvelope hzero hadd
    (generatedStableKeyIntervalTable_finiteTableUpperBound_finiteCutoff_of_keyValue
      K intervalOf S.finiteContribution keyValue hvalue hkey hupper)
    htail htailSum



theorem tsum_total_le_of_generatedMinimalCubicStableKeyTable_finiteCutoff
    {d : ℕ} (K : TailCutoff)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf : StableKey K.maxDegree K.maxRange → RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
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
    (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (support.card : ℝ) * finiteBound + tailBound :=
  ContributionSplit.tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    S support tailEnvelope hzero hadd
    (generatedMinimalCubicStableKeyTable_finiteTableUpperBound_finiteCutoff_of_keyValue
      K intervalOf S.finiteContribution keyValue hvalue hkey hupper)
    htail htailSum


theorem tsum_total_le_of_generatedIntervalTable_finiteCutoff
    {d : ℕ} (K : TailCutoff)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf : FiniteCutoffCase d K → RatInterval)
    (caseValue : FiniteCutoffCase d K → ℝ)
    (support : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hadd : S.Additive)
    (hvalue : ∀ c,
      S.finiteContribution c =
        caseValue (classifyFiniteCutoffCoordinate K c))
    (hcase : ∀ c, (intervalOf c).MemR (caseValue c))
    (hupper : ∀ c,
      c ∈ (generatedIntervalTable intervalOf).cases →
        ((intervalOf c).upper : ℝ) ≤ finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (support.card : ℝ) * finiteBound + tailBound :=
  ContributionSplit.tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    S support tailEnvelope hzero hadd
    (generatedIntervalTable_finiteTableUpperBound_finiteCutoff_of_caseValue
      K intervalOf S.finiteContribution caseValue hvalue hcase hupper)
    htail htailSum


theorem tsum_total_le_of_generatedCubicIntervalTable_finiteCutoff
    {d : ℕ} (K : TailCutoff)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf :
      CubicClass d K.radius K.maxDegree K.maxRange → RatInterval)
    (classValue :
      CubicClass d K.radius K.maxDegree K.maxRange → ℝ)
    (support : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hadd : S.Additive)
    (hvalue : ∀ c,
      S.finiteContribution c =
        classValue (classifyFiniteCutoffCubicClass K c))
    (hclass : ∀ q, (intervalOf q).MemR (classValue q))
    (hupper : ∀ q,
      q ∈ (generatedCubicIntervalTable intervalOf).cases →
        ((intervalOf q).upper : ℝ) ≤ finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (support.card : ℝ) * finiteBound + tailBound :=
  ContributionSplit.tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    S support tailEnvelope hzero hadd
    (generatedCubicIntervalTable_finiteTableUpperBound_finiteCutoff_of_classValue
      K intervalOf S.finiteContribution classValue hvalue hclass hupper)
    htail htailSum


noncomputable def finiteSupportCertificate_of_generatedIntervalTable_finiteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
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
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (generatedIntervalTable_finiteTableUpperBound_finiteCutoff_of_caseValue
      K intervalOf S.finiteContribution caseValue hvalue hcase hupper)
    htail htailSum


noncomputable def finiteSupportCertificate_of_generatedCubicIntervalTable_finiteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (intervalOf :
      CubicClass d K.radius K.maxDegree K.maxRange → RatInterval)
    (classValue :
      CubicClass d K.radius K.maxDegree K.maxRange → ℝ)
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
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (generatedCubicIntervalTable_finiteTableUpperBound_finiteCutoff_of_classValue
      K intervalOf S.finiteContribution classValue hvalue hclass hupper)
    htail htailSum


noncomputable def finiteSupportCertificate_of_generatedStableKeyIntervalTable_finiteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
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
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (generatedStableKeyIntervalTable_finiteTableUpperBound_finiteCutoff_of_keyValue
      K intervalOf S.finiteContribution keyValue hvalue hkey hupper)
    htail htailSum



noncomputable def finiteSupportCertificate_of_generatedMinimalCubicStableKeyTable_finiteCutoff
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
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
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (generatedMinimalCubicStableKeyTable_finiteTableUpperBound_finiteCutoff_of_keyValue
      K intervalOf S.finiteContribution keyValue hvalue hkey hupper)
    htail htailSum

end BoundedPolymerCase
end Exact3D
end StatMech
