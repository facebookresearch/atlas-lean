/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.NNReal.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Threshold accessibility

## i. Overview

Threshold accessibility sums the opportunities of destinations whose
supplied travel time is present and at most a threshold `T`. Travel
times and thresholds are nonnegative reals; a missing travel time
contributes zero at every threshold. The sum is nondecreasing in the
threshold for nonnegative opportunities.

## ii. Key results

- `TransportAccessibility.thresholdOpportunitySum_eq_filter_sum`: the
  contribution sum is the filtered opportunity sum.
- `TransportAccessibility.thresholdOpportunitySum_mono`: threshold
  monotonicity.

## iii. Table of contents

- A. Contributions and monotonicity

## iv. References

- S. L. Handy and D. A. Niemeier, measuring accessibility: an
  exploration of issues and alternatives, *Environment and Planning A*
  29(7), 1997 (cumulative-opportunity measures). The hard cutoff and
  the treatment of a missing supplied travel time as zero contribution
  are conventions of this formalization.
-/

@[expose] public section

namespace TransportAccessibility

/-! ## A. Contributions and monotonicity -/

/-- Contribution of one destination at threshold `T`: its opportunity
when a travel time is present and at most `T`, and zero otherwise. Travel
times and thresholds are nonnegative reals; a missing travel time
(`none`) contributes zero at every threshold. -/
noncomputable def thresholdContribution {ι : Type*} (o : ι → ℝ)
    (t : ι → Option NNReal) (T : NNReal) (i : ι) : ℝ :=
  match t i with
  | some τ => if τ ≤ T then o i else 0
  | none => 0

/-- Threshold accessibility: total opportunity over the destinations in
`s` whose supplied travel time is present and at most `T`. -/
noncomputable def thresholdOpportunitySum {ι : Type*} (s : Finset ι)
    (o : ι → ℝ) (t : ι → Option NNReal) (T : NNReal) : ℝ :=
  ∑ i ∈ s, thresholdContribution o t T i

/-- A destination within its threshold contributes its opportunity. -/
lemma thresholdContribution_of_le {ι : Type*} (o : ι → ℝ)
    (t : ι → Option NNReal) (T : NNReal) {i : ι} {τ : NNReal}
    (h : t i = some τ) (hτ : τ ≤ T) :
    thresholdContribution o t T i = o i := by
  simp [thresholdContribution, h, hτ]

/-- A destination past its threshold contributes zero. -/
lemma thresholdContribution_eq_zero_of_gt {ι : Type*} (o : ι → ℝ)
    (t : ι → Option NNReal) (T : NNReal) {i : ι} {τ : NNReal}
    (h : t i = some τ) (hτ : T < τ) :
    thresholdContribution o t T i = 0 := by
  simp [thresholdContribution, h, not_le_of_gt hτ]

/-- A destination with no supplied travel time contributes zero. -/
lemma thresholdContribution_eq_zero_of_eq_none {ι : Type*} (o : ι → ℝ)
    (t : ι → Option NNReal) (T : NNReal) {i : ι} (h : t i = none) :
    thresholdContribution o t T i = 0 := by
  unfold thresholdContribution
  rw [h]

open scoped Classical in
/-- The match sum is the filtered opportunity sum. -/
lemma thresholdOpportunitySum_eq_filter_sum {ι : Type*} (s : Finset ι)
    (o : ι → ℝ) (t : ι → Option NNReal) (T : NNReal) :
    thresholdOpportunitySum s o t T
      = ∑ i ∈ s.filter (fun i => ∃ τ : NNReal, t i = some τ ∧ τ ≤ T), o i := by
  unfold thresholdOpportunitySum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ∃ τ : NNReal, t i = some τ ∧ τ ≤ T
  · have ⟨τ, hti, hle⟩ := h
    rw [ite_eq_left h, thresholdContribution_of_le o t T hti hle]
  · rw [ite_eq_right h]
    cases hti : t i
    case none =>
      rw [thresholdContribution_eq_zero_of_eq_none o t T hti]
    case some τ =>
      have hle : ¬τ ≤ T := fun hle => h ⟨τ, hti, hle⟩
      rw [thresholdContribution_eq_zero_of_gt o t T hti (lt_of_not_ge hle)]

/-- Threshold accessibility is nondecreasing in the threshold, for
nonnegative opportunities. -/
lemma thresholdOpportunitySum_mono {ι : Type*} (s : Finset ι)
    (o : ι → ℝ) (t : ι → Option NNReal) (ho : ∀ i : ι, i ∈ s → 0 ≤ o i)
    {T1 T2 : NNReal} (hT : T1 ≤ T2) :
    thresholdOpportunitySum s o t T1 ≤ thresholdOpportunitySum s o t T2 := by
  unfold thresholdOpportunitySum
  apply Finset.sum_le_sum
  intro i hi
  cases hti : t i
  case none =>
    rw [thresholdContribution_eq_zero_of_eq_none o t T1 hti,
      thresholdContribution_eq_zero_of_eq_none o t T2 hti]
  case some τ =>
    by_cases h1 : τ ≤ T1
    · have h2 : τ ≤ T2 := le_trans h1 hT
      rw [thresholdContribution_of_le o t T1 hti h1,
        thresholdContribution_of_le o t T2 hti h2]
    · by_cases h2 : τ ≤ T2
      · rw [thresholdContribution_eq_zero_of_gt o t T1 hti (lt_of_not_ge h1),
          thresholdContribution_of_le o t T2 hti h2]
        exact ho i hi
      · rw [thresholdContribution_eq_zero_of_gt o t T1 hti (lt_of_not_ge h1),
          thresholdContribution_eq_zero_of_gt o t T2 hti (lt_of_not_ge h2)]

end TransportAccessibility
