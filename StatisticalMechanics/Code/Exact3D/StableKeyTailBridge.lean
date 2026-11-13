/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.StableKeyCertificate
import Code.Exact3D.TailSummabilitySkeleton

open scoped BigOperators










namespace StatMech
namespace Exact3D


noncomputable def classifyFiniteCutoffStableKey {d : ℕ} (K : TailCutoff)
    (c : FiniteCutoffCoordinate d K) :
    BoundedPolymerCase.StableKey K.maxDegree K.maxRange :=
  BoundedPolymerCase.stableKey (classifyFiniteCutoffCoordinate K c)


noncomputable def classifyFiniteCutoffMinimalCubicStableKey {d : ℕ}
    (K : TailCutoff) (c : FiniteCutoffCoordinate d K) :
    BoundedPolymerCase.StableKey K.maxDegree K.maxRange :=
  BoundedPolymerCase.classifyByMinimalCubicStableKey
    (classifyFiniteCutoffCoordinate K c)

namespace BoundedPolymerCase



theorem intervalOfRows_upper_le_of_mem_keyFinset {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) {bound : ℝ}
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ bound)
    {k : StableKey maxDegree maxRange}
    (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
    (((intervalOfRows rows fallback k).upper : ℚ) : ℝ) ≤ bound := by
  classical
  have hex : ∃ row, row ∈ rows ∧ row.key.toKey = k := by
    simpa [stableKeyIntervalRowKeyFinset, stableKeyIntervalRowRecords,
      validRecordKeyFinset, validRecordKeyList] using hk
  rw [intervalOfRows, dif_pos hex]
  exact hrowUpper (Classical.choose hex) (Classical.choose_spec hex).1



theorem externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue
    {α : Type*} {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (classifier : α → StableKey maxDegree maxRange)
    (value : α → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    {finiteBound : ℝ}
    (hcover : ∀ a, classifier a ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ a, value a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound (externalStableKeyIntervalRowTable rows fallback)
      classifier value finiteBound := by
  classical
  have hcovsound :=
    externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue
      rows fallback classifier value keyValue hcover hvalue hrow
  refine ⟨hcovsound.1, hcovsound.2, ?_⟩
  intro k hk
  simpa [externalStableKeyIntervalRowTable, externalStableKeyIntervalTable] using
    intervalOfRows_upper_le_of_mem_keyFinset rows fallback hrowUpper
      (by
        simpa [externalStableKeyIntervalRowTable, externalStableKeyIntervalTable,
          stableKeyIntervalRowKeyFinset] using hk)



theorem externalStableKeyIntervalRowTable_finiteTableUpperBound_of_exactKeySet
    {α : Type*} {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (expected : Finset (StableKey maxDegree maxRange))
    (classifier : α → StableKey maxDegree maxRange)
    (value : α → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    {finiteBound : ℝ}
    (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
    (hcover : ∀ a, classifier a ∈ expected)
    (hvalue : ∀ a, value a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound (externalStableKeyIntervalRowTable rows fallback)
      classifier value finiteBound :=
  externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue
    rows fallback classifier value keyValue
    (StableKeyIntervalRow.classifier_mem_rows_of_exactKeySet
      hexact classifier hcover)
    hvalue hrow hrowUpper



theorem externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffMinimalCubic_of_keyValue
    {d : ℕ} (K : TailCutoff)
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (value : FiniteCutoffCoordinate d K → ℝ)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    {finiteBound : ℝ}
    (hcover : ∀ c : FiniteCutoffCase d K,
      classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      value c =
        keyValue (classifyFiniteCutoffMinimalCubicStableKey K c))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound
      (externalStableKeyIntervalRowTable rows fallback)
      (classifyFiniteCutoffMinimalCubicStableKey K) value finiteBound :=
  externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue
    rows fallback (classifyFiniteCutoffMinimalCubicStableKey K) value keyValue
    (fun c => hcover (classifyFiniteCutoffCoordinate K c))
    hvalue hrow hrowUpper


theorem externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffStableKey_of_keyValue
    {d : ℕ} (K : TailCutoff)
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (value : FiniteCutoffCoordinate d K → ℝ)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    {finiteBound : ℝ}
    (hcover : ∀ c : FiniteCutoffCase d K,
      stableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      value c =
        keyValue (classifyFiniteCutoffStableKey K c))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound
      (externalStableKeyIntervalRowTable rows fallback)
      (classifyFiniteCutoffStableKey K) value finiteBound :=
  externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue
    rows fallback (classifyFiniteCutoffStableKey K) value keyValue
    (fun c => hcover (classifyFiniteCutoffCoordinate K c))
    hvalue hrow hrowUpper




noncomputable def externalStableKeyIntervalRowTable_finiteSupportCertificate_of_keyValue
    {α : Type*} [DecidableEq α] {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (classifier : α → StableKey maxDegree maxRange)
    (S : ContributionSplit α)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (support finitePrefix : Finset α)
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : α → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hcover : ∀ a, classifier a ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ a, S.finiteContribution a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    TailSummability.FiniteSupportCertificate α :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue
      rows fallback classifier S.finiteContribution keyValue
      hcover hvalue hrow hrowUpper)
    htail htailSum



noncomputable def externalStableKeyIntervalRowTable_finiteSupportCertificate_of_exactKeySet
    {α : Type*} [DecidableEq α] {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (expected : Finset (StableKey maxDegree maxRange))
    (classifier : α → StableKey maxDegree maxRange)
    (S : ContributionSplit α)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (support finitePrefix : Finset α)
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : α → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
    (hcover : ∀ a, classifier a ∈ expected)
    (hvalue : ∀ a, S.finiteContribution a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    TailSummability.FiniteSupportCertificate α :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (externalStableKeyIntervalRowTable_finiteTableUpperBound_of_exactKeySet
      rows fallback expected classifier S.finiteContribution keyValue hexact
      hcover hvalue hrow hrowUpper)
    htail htailSum



noncomputable def finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
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
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffMinimalCubic_of_keyValue
      K rows fallback S.finiteContribution keyValue hcover hvalue hrow hrowUpper)
    htail htailSum



noncomputable def
    finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic_exactKeySet
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (expected : Finset (StableKey K.maxDegree K.maxRange))
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
    (hcover : ∀ c : FiniteCutoffCase d K,
      classifyByMinimalCubicStableKey c ∈ expected)
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
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  externalStableKeyIntervalRowTable_finiteSupportCertificate_of_exactKeySet
    rows fallback expected (classifyFiniteCutoffMinimalCubicStableKey K) S
    keyValue support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    hexact (fun c => hcover (classifyFiniteCutoffCoordinate K c)) hvalue
    hrow hrowUpper htail htailSum


noncomputable def finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffStableKey
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
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
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffStableKey_of_keyValue
      K rows fallback S.finiteContribution keyValue hcover hvalue hrow hrowUpper)
    htail htailSum



noncomputable def
    finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffStableKey_exactKeySet
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (expected : Finset (StableKey K.maxDegree K.maxRange))
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
    (hcover : ∀ c : FiniteCutoffCase d K, stableKey c ∈ expected)
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
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  externalStableKeyIntervalRowTable_finiteSupportCertificate_of_exactKeySet
    rows fallback expected (classifyFiniteCutoffStableKey K) S keyValue
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd hexact
    (fun c => hcover (classifyFiniteCutoffCoordinate K c)) hvalue hrow
    hrowUpper htail htailSum



theorem tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic
    {d : ℕ} (K : TailCutoff)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
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
    (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (support.card : ℝ) * finiteBound + tailBound :=
  ContributionSplit.tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    S support tailEnvelope hzero hadd
    (externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffMinimalCubic_of_keyValue
      K rows fallback S.finiteContribution keyValue hcover hvalue hrow hrowUpper)
    htail htailSum


theorem tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffStableKey
    {d : ℕ} (K : TailCutoff)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
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
    (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (support.card : ℝ) * finiteBound + tailBound :=
  ContributionSplit.tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    S support tailEnvelope hzero hadd
    (externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffStableKey_of_keyValue
      K rows fallback S.finiteContribution keyValue hcover hvalue hrow hrowUpper)
    htail htailSum

end BoundedPolymerCase

end Exact3D
end StatMech
