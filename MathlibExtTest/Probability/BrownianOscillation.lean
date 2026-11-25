/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianOscillation
public import MathlibExt.Probability.BrownianMotionExistence
public import MathlibExt.Probability.OrnsteinUhlenbeck

/-!
# Tests for the oscillation of Brownian motion at time zero

The Gaussian half-line mass for the standard Gaussian, and non-vacuity of the oscillation theorem
on a Brownian motion with measurable coordinates, the continuous modification
(`IsPreBrownianReal.exists_isBrownianReal_modification`) of the coordinate process of
`exists_isPreBrownianReal_eval`.
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
  obtain ⟨μ, hB⟩ := exists_isPreBrownianReal_eval
  have hμ : IsProbabilityMeasure μ := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWm, -, -, hW⟩ :=
    hB.exists_isBrownianReal_modification fun t ↦ measurable_pi_apply t
  exact ⟨μ, W, hμ, hW.ae_exists_pos_and_neg hWm⟩

end MathlibExtTest.Probability.BrownianOscillation
