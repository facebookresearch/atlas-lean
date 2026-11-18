/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianOscillation
public import MathlibExt.Probability.BrownianMotionExistence

/-!
# Tests for the oscillation of Brownian motion at time zero

The Gaussian half-line mass for the standard Gaussian, and non-vacuity of the oscillation theorem
on the Brownian motion of `exists_isBrownianReal`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.BrownianOscillation

/-- The standard Gaussian gives mass `1/2` to `(0, ∞)`. -/
example : gaussianReal 0 1 (Set.Ioi 0) = 1 / 2 := gaussianReal_Ioi_zero one_ne_zero

/-- Non-vacuity: some Brownian motion takes both signs on `(0, ε]` for every `ε > 0`, a.s.;
in particular it vanishes somewhere in `(0, 1]`, by the intermediate value theorem. -/
example : ∃ (μ : Measure (ℝ≥0 → ℝ)) (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ),
    IsProbabilityMeasure μ ∧ ∀ᵐ ω ∂μ, ∀ ε : ℝ≥0, 0 < ε →
      (∃ s ∈ Set.Ioc 0 ε, 0 < W s ω) ∧ (∃ s ∈ Set.Ioc 0 ε, W s ω < 0) := by
  obtain ⟨μ, W, hμ, hWm, -, hW⟩ := exists_isBrownianReal
  exact ⟨μ, W, hμ, hW.ae_exists_pos_and_neg hWm⟩

end MathlibExtTest.Probability.BrownianOscillation
