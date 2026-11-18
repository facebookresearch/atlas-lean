/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Transport.Accessibility
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Opportunity monotonicity and bounds

At fixed travel times and threshold, pointwise larger nonnegative
opportunities give no smaller threshold accessibility, and the
accessibility lies between zero and the total destination
opportunities over the same destination set.

## Main results

- `TransportAccessibility.thresholdOpportunitySum_mono_opportunities`:
  monotonicity in the opportunities.
- `TransportAccessibility.thresholdOpportunitySum_le_total`:
  accessibility is at most the total opportunities.
- `TransportAccessibility.thresholdOpportunitySum_nonneg`:
  accessibility is nonnegative.
-/

@[expose] public section

namespace TransportAccessibility

/-- Accessibility is monotone in the opportunities at fixed
travel times and threshold. -/
lemma thresholdOpportunitySum_mono_opportunities {ι : Type*}
    (s : Finset ι) (o₁ o₂ : ι → ℝ) (t : ι → Option NNReal)
    (T : NNReal) (ho : ∀ i ∈ s, o₁ i ≤ o₂ i) :
    thresholdOpportunitySum s o₁ t T
      ≤ thresholdOpportunitySum s o₂ t T := by
  unfold thresholdOpportunitySum
  apply Finset.sum_le_sum
  intro i hi
  cases hti : t i
  case none =>
    rw [thresholdContribution_eq_zero_of_eq_none o₁ t T hti,
      thresholdContribution_eq_zero_of_eq_none o₂ t T hti]
  case some τ =>
    by_cases hle : τ ≤ T
    · rw [thresholdContribution_of_le o₁ t T hti hle,
        thresholdContribution_of_le o₂ t T hti hle]
      exact ho i hi
    · rw [thresholdContribution_eq_zero_of_gt o₁ t T hti (lt_of_not_ge hle),
        thresholdContribution_eq_zero_of_gt o₂ t T hti (lt_of_not_ge hle)]

/-- Accessibility is bounded by the total opportunities. -/
lemma thresholdOpportunitySum_le_total {ι : Type*} (s : Finset ι)
    (o : ι → ℝ) (t : ι → Option NNReal) (T : NNReal)
    (ho : ∀ i ∈ s, 0 ≤ o i) :
    thresholdOpportunitySum s o t T ≤ ∑ i ∈ s, o i := by
  unfold thresholdOpportunitySum
  apply Finset.sum_le_sum
  intro i hi
  cases hti : t i
  case none =>
    rw [thresholdContribution_eq_zero_of_eq_none o t T hti]
    exact ho i hi
  case some τ =>
    by_cases hle : τ ≤ T
    · rw [thresholdContribution_of_le o t T hti hle]
    · rw [thresholdContribution_eq_zero_of_gt o t T hti (lt_of_not_ge hle)]
      exact ho i hi

/-- Accessibility is nonnegative for nonnegative opportunities. -/
lemma thresholdOpportunitySum_nonneg {ι : Type*} (s : Finset ι)
    (o : ι → ℝ) (t : ι → Option NNReal) (T : NNReal)
    (ho : ∀ i ∈ s, 0 ≤ o i) :
    0 ≤ thresholdOpportunitySum s o t T := by
  unfold thresholdOpportunitySum
  apply Finset.sum_nonneg
  intro i hi
  cases hti : t i
  case none =>
    rw [thresholdContribution_eq_zero_of_eq_none o t T hti]
  case some τ =>
    by_cases hle : τ ≤ T
    · rw [thresholdContribution_of_le o t T hti hle]
      exact ho i hi
    · rw [thresholdContribution_eq_zero_of_gt o t T hti (lt_of_not_ge hle)]

end TransportAccessibility
