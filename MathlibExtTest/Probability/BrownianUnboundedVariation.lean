/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianUnboundedVariation
public import MathlibExt.Probability.BrownianMotionExistence

/-!
# Tests for the unbounded variation of Brownian paths

The deterministic lemma on a linear function (bounded variation, quadratic sums `t² / n → 0`), and
non-vacuity of the probabilistic statement on the Brownian motion of `exists_isBrownianReal`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.BrownianUnboundedVariation

/-- A constant function has bounded variation, so its quadratic sums tend to `0`. -/
example (t : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ((fun _ : ℝ≥0 ↦ (1 : ℝ)) (t * (k + 1) / n) - (fun _ : ℝ≥0 ↦ (1 : ℝ)) (t * k / n)) ^ 2)
      atTop (𝓝 0) :=
  tendsto_sum_sq_increments_of_boundedVariationOn continuous_const t
    (by
      unfold BoundedVariationOn
      rw [eVariationOn.constant_on]
      · exact ENNReal.zero_ne_top
      · rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
        rfl)

/-- Non-vacuity: some Brownian motion has, almost surely, unbounded variation on `[0, 1]`. -/
example : ∃ (μ : Measure (ℝ≥0 → ℝ)) (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ),
    IsProbabilityMeasure μ ∧ ∀ᵐ ω ∂μ, ¬ BoundedVariationOn (fun s ↦ W s ω) (Set.Icc 0 1) := by
  obtain ⟨μ, W, hW⟩ := exists_isBrownianReal
  have hμ : IsProbabilityMeasure μ := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact ⟨μ, W, hμ, hW.ae_not_boundedVariationOn one_pos⟩

end MathlibExtTest.Probability.BrownianUnboundedVariation
