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
import Mathlib.Tactic.Linarith

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

- W. G. Hansen, how accessibility shapes land use, *Journal of the
  American Institute of Planners* 25, 1959.
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
theorem thresholdContribution_of_le {ι : Type*} (o : ι → ℝ)
    (t : ι → Option NNReal) (T : NNReal) {i : ι} {τ : NNReal}
    (h : t i = some τ) (hτ : τ ≤ T) :
    thresholdContribution o t T i = o i := by
  simp [thresholdContribution, h, hτ]

/-- A destination past its threshold contributes zero. -/
theorem thresholdContribution_eq_zero_of_gt {ι : Type*} (o : ι → ℝ)
    (t : ι → Option NNReal) (T : NNReal) {i : ι} {τ : NNReal}
    (h : t i = some τ) (hτ : T < τ) :
    thresholdContribution o t T i = 0 := by
  simp [thresholdContribution, h, not_le.mpr hτ]

/-- A destination with no supplied travel time contributes zero. -/
theorem thresholdContribution_eq_none {ι : Type*} (o : ι → ℝ)
    (t : ι → Option NNReal) (T : NNReal) {i : ι} (h : t i = none) :
    thresholdContribution o t T i = 0 := by
  simp only [thresholdContribution, h]

open scoped Classical in
/-- The match sum is the filtered opportunity sum. -/
theorem thresholdOpportunitySum_eq_filter_sum {ι : Type*} (s : Finset ι)
    (o : ι → ℝ) (t : ι → Option NNReal) (T : NNReal) :
    thresholdOpportunitySum s o t T
      = ∑ i ∈ s.filter (fun i => ∃ τ : NNReal, t i = some τ ∧ τ ≤ T), o i := by
  unfold thresholdOpportunitySum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hti : t i with
  | none =>
      have hex : ¬∃ τ : NNReal, (none : Option NNReal) = some τ ∧ τ ≤ T := by
        rintro ⟨τ, hcon, -⟩
        exact Option.some_ne_none τ hcon.symm
      rw [thresholdContribution_eq_none o t T hti, ite_eq_right hex]
  | some τ =>
      by_cases hτ : τ ≤ T
      · rw [thresholdContribution_of_le o t T hti hτ, ite_eq_left ⟨τ, rfl, hτ⟩]
      · have hex : ¬∃ σ : NNReal, (some τ) = some σ ∧ σ ≤ T := by
          rintro ⟨σ, hcon, hσ⟩
          have hτσ : τ = σ := Option.some_inj.mp hcon
          subst hτσ
          exact hτ hσ
        rw [thresholdContribution_eq_zero_of_gt o t T hti (lt_of_not_ge hτ),
          ite_eq_right hex]

/-- Threshold accessibility is nondecreasing in the threshold, for
nonnegative opportunities. -/
theorem thresholdOpportunitySum_mono {ι : Type*} (s : Finset ι)
    (o : ι → ℝ) (t : ι → Option NNReal) (ho : ∀ i : ι, 0 ≤ o i)
    {T1 T2 : NNReal} (hT : T1 ≤ T2) :
    thresholdOpportunitySum s o t T1 ≤ thresholdOpportunitySum s o t T2 := by
  unfold thresholdOpportunitySum
  apply Finset.sum_le_sum
  intro i _
  cases hti : t i with
  | none =>
      rw [thresholdContribution_eq_none o t T1 hti,
        thresholdContribution_eq_none o t T2 hti]
  | some τ =>
      by_cases h1 : τ ≤ T1
      · have h2 : τ ≤ T2 := le_trans h1 hT
        rw [thresholdContribution_of_le o t T1 hti h1,
          thresholdContribution_of_le o t T2 hti h2]
      · by_cases h2 : τ ≤ T2
        · rw [thresholdContribution_eq_zero_of_gt o t T1 hti (lt_of_not_ge h1),
            thresholdContribution_of_le o t T2 hti h2]
          exact ho i
        · rw [thresholdContribution_eq_zero_of_gt o t T1 hti (lt_of_not_ge h1),
            thresholdContribution_eq_zero_of_gt o t T2 hti (lt_of_not_ge h2)]

end TransportAccessibility
