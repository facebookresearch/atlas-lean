/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianRecurrence
public import MathlibExt.Probability.BrownianMotionExistence

/-!
# Tests for the recurrence of linear Brownian motion

Non-vacuity on the Brownian motion of `exists_isBrownianReal`: it is unbounded above and below
along integer times, and it hits the levels `-1`, `0` and `10⁶`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathlibExtTest.Probability.BrownianRecurrence

/-- Non-vacuity: some Brownian motion is, almost surely, above `A` and below `-A` at integer times
after `N`, for all `A` and `N`. -/
example : ∃ (μ : Measure (ℝ≥0 → ℝ)) (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ),
    IsProbabilityMeasure μ ∧ ∀ᵐ ω ∂μ, ∀ A : ℝ, ∀ N : ℕ,
      (∃ n ≥ N, A < W n ω) ∧ (∃ n ≥ N, W n ω < -A) := by
  obtain ⟨μ, W, hW⟩ := exists_isBrownianReal
  have hμ : IsProbabilityMeasure μ := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨μ, W, hμ, ?_⟩
  filter_upwards [hW.ae_unbounded_atTop] with ω h A N
  exact ⟨(h A N).1, (h (-A) N).2⟩

/-- Non-vacuity: the levels `-1`, `0` and `10⁶` are all hit, almost surely. -/
example : ∃ (μ : Measure (ℝ≥0 → ℝ)) (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ),
    IsProbabilityMeasure μ ∧ ∀ᵐ ω ∂μ,
      (∃ t, W t ω = -1) ∧ (∃ t, W t ω = 0) ∧ (∃ t, W t ω = 10 ^ 6) := by
  obtain ⟨μ, W, hW⟩ := exists_isBrownianReal
  have hμ : IsProbabilityMeasure μ := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨μ, W, hμ, ?_⟩
  filter_upwards [hW.ae_exists_eq] with ω h
  exact ⟨h _, h _, h _⟩

end MathlibExtTest.Probability.BrownianRecurrence
