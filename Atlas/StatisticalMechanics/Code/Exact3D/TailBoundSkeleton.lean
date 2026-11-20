/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.PolymerEnumeration

open scoped BigOperators










namespace StatMech
namespace Exact3D


structure TailCutoff where
  radius : ℕ
  maxDegree : ℕ
  maxRange : ℕ


def InsideFiniteCutoff {d : ℕ} (K : TailCutoff)
    (c : LocalPolymerCoordinate d) : Prop :=
  c.support.containedInBox K.radius ∧ c.degree ≤ K.maxDegree ∧ c.range ≤ K.maxRange


def OutsideFiniteCutoff {d : ℕ} (K : TailCutoff)
    (c : LocalPolymerCoordinate d) : Prop :=
  ¬ InsideFiniteCutoff K c


abbrev FiniteCutoffCoordinate (d : ℕ) (K : TailCutoff) : Type :=
  {c : LocalPolymerCoordinate d // InsideFiniteCutoff K c}


abbrev TailCoordinate (d : ℕ) (K : TailCutoff) : Type :=
  {c : LocalPolymerCoordinate d // OutsideFiniteCutoff K c}


abbrev FiniteCutoffCase (d : ℕ) (K : TailCutoff) : Type :=
  BoundedPolymerCase d K.radius K.maxDegree K.maxRange


abbrev FiniteCutoffTable (d : ℕ) (K : TailCutoff) : Type :=
  RatInterval.CaseTable (FiniteCutoffCase d K)



def toBoundedLocalCoordinate {d : ℕ} {K : TailCutoff}
    (c : FiniteCutoffCoordinate d K) :
    BoundedPolymerCase.BoundedLocalCoordinate d K.radius K.maxDegree K.maxRange :=
  ⟨c.1, by simpa [InsideFiniteCutoff] using c.2⟩



noncomputable def classifyFiniteCutoffCoordinate {d : ℕ} (K : TailCutoff)
    (c : FiniteCutoffCoordinate d K) : FiniteCutoffCase d K :=
  BoundedPolymerCase.classifyBoundedLocalCoordinate (toBoundedLocalCoordinate c)


structure CutoffContributionData (d : ℕ) where
  cutoff : TailCutoff
  finiteContribution : FiniteCutoffCoordinate d cutoff → ℝ
  tailContribution : TailCoordinate d cutoff → ℝ




structure FiniteTableUpperBound {Case α : Type*} [DecidableEq Case]
    (T : RatInterval.CaseTable Case) (classify : α → Case)
    (value : α → ℝ) (bound : ℝ) : Prop where
  covers : RatInterval.CaseTable.Covers T classify
  sound : RatInterval.CaseTable.Sound T classify value
  intervalUpper_le : ∀ c, c ∈ T.cases → ((T.interval c).upper : ℝ) ≤ bound


theorem finite_le_of_tableUpperBound {Case α : Type*} [DecidableEq Case]
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {value : α → ℝ} {bound : ℝ}
    (h : FiniteTableUpperBound T classify value bound) (a : α) :
    value a ≤ bound :=
  le_trans (h.sound a).2 (h.intervalUpper_le (classify a) (h.covers a))


structure ContributionSplit (α : Type*) where
  finiteContribution : α → ℝ
  tailContribution : α → ℝ
  totalContribution : α → ℝ

namespace ContributionSplit


def Additive (S : ContributionSplit α) : Prop :=
  ∀ a, S.totalContribution a = S.finiteContribution a + S.tailContribution a


def TailUpperBound (S : ContributionSplit α) (bound : ℝ) : Prop :=
  ∀ a, S.tailContribution a ≤ bound




def TailEnvelopeOn (S : ContributionSplit α) (s : Finset α)
    (envelope : α → ℝ) : Prop :=
  ∀ a, a ∈ s → S.tailContribution a ≤ envelope a


def TotalUpperBound (S : ContributionSplit α) (bound : ℝ) : Prop :=
  ∀ a, S.totalContribution a ≤ bound



theorem totalUpperBound_of_finiteTableUpperBound_and_tailUpperBound
    {Case α : Type*} [DecidableEq Case]
    (S : ContributionSplit α)
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {finiteBound tailBound : ℝ}
    (hadd : S.Additive)
    (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail : S.TailUpperBound tailBound) :
    S.TotalUpperBound (finiteBound + tailBound) := by
  intro a
  calc
    S.totalContribution a =
        S.finiteContribution a + S.tailContribution a := hadd a
    _ ≤ finiteBound + tailBound :=
        add_le_add (finite_le_of_tableUpperBound hfinite a) (htail a)



theorem tail_sum_le_of_envelopeOn
    (S : ContributionSplit α) (s : Finset α) (envelope : α → ℝ)
    (henv : S.TailEnvelopeOn s envelope) :
    (∑ a ∈ s, S.tailContribution a) ≤ ∑ a ∈ s, envelope a := by
  exact Finset.sum_le_sum fun a ha => henv a ha





theorem total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    {Case α : Type*} [DecidableEq Case]
    (S : ContributionSplit α) (s : Finset α)
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {finiteBound tailBound : ℝ} (tailEnvelope : α → ℝ)
    (hadd : S.Additive)
    (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail : S.TailEnvelopeOn s tailEnvelope)
    (htailSum : (∑ a ∈ s, tailEnvelope a) ≤ tailBound) :
    (∑ a ∈ s, S.totalContribution a) ≤
      (s.card : ℝ) * finiteBound + tailBound := by
  calc
    (∑ a ∈ s, S.totalContribution a) =
        ∑ a ∈ s, (S.finiteContribution a + S.tailContribution a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact hadd a
    _ = (∑ a ∈ s, S.finiteContribution a) +
        ∑ a ∈ s, S.tailContribution a := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ _a ∈ s, finiteBound) + ∑ a ∈ s, tailEnvelope a := by
      exact add_le_add
        (Finset.sum_le_sum fun a _ => finite_le_of_tableUpperBound hfinite a)
        (tail_sum_le_of_envelopeOn S s tailEnvelope htail)
    _ ≤ (s.card : ℝ) * finiteBound + tailBound := by
      apply add_le_add
      · simp [Finset.sum_const, nsmul_eq_mul]
      · exact htailSum

end ContributionSplit

end Exact3D
end StatMech
