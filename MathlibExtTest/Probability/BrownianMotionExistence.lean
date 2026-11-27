/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotionExistence
public import MathlibExt.Probability.BrownianQuadraticVariation
public import MathlibExt.Probability.OrnsteinUhlenbeck

/-!
# Tests for the existence of Brownian motion

The fourth Gaussian moment at variance `0` and `1`, Kolmogorov's condition at equal times, and
non-vacuity: `exists_isBrownianReal` produces a Brownian motion, and the continuous modification
(`IsPreBrownianReal.exists_isBrownianReal_modification`) of the coordinate process of
`exists_isPreBrownianReal_eval` has the Brownian one-time laws, starts at `0`, has continuous
paths everywhere and satisfies Kolmogorov's condition.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.BrownianMotionExistence

/-- The fourth moment of the standard Gaussian is `3`. -/
example : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  simpa using integral_pow_four_gaussianReal 1

/-- At variance `0` the formula gives `0`, consistent with the Dirac mass at `0`. -/
example : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 0 = 0 := by
  rw [integral_pow_four_gaussianReal]
  simp

/-- Non-vacuity: Brownian motion exists, with continuous paths, `B 0 = 0` a.s., `B 1 ~ N(0, 1)`
and Kolmogorov's fourth-moment condition. -/
example : ∃ (μ : Measure (ℝ≥0 → ℝ)) (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ),
    (∀ ω, Continuous fun t ↦ W t ω) ∧ (∀ᵐ ω ∂μ, W 0 ω = 0) ∧
      HasLaw (W 1) (gaussianReal 0 1) μ ∧ IsKolmogorovProcess W μ 4 2 3 := by
  obtain ⟨μ, hB⟩ := exists_isPreBrownianReal_eval
  have : IsProbabilityMeasure μ := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWm, hWc, -, hW⟩ :=
    hB.exists_isBrownianReal_modification fun t ↦ measurable_pi_apply t
  exact ⟨μ, W, hWc, hW.eval_zero_ae_eq_zero, by simpa using hW.hasLaw_eval 1,
    hW.isKolmogorovProcess hWm⟩

/-- `exists_isBrownianReal` produces a Brownian motion, whose underlying measure is a
probability measure. -/
example : ∃ (μ : Measure (ℝ≥0 → ℝ)) (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ),
    IsProbabilityMeasure μ ∧ IsBrownianReal W μ := by
  obtain ⟨μ, W, hW⟩ := exists_isBrownianReal
  exact ⟨μ, W, (hW.hasLaw_eval 0).isProbabilityMeasure, hW⟩

/-- The continuous modification agrees with the original pre-Brownian motion at each time. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (t : ℝ≥0) :
    ∃ W : ℝ≥0 → Ω → ℝ, W t =ᵐ[P] B t ∧ IsBrownianReal W P := by
  obtain ⟨W, -, -, hWB, hW⟩ := hB.exists_isBrownianReal_modification hBm
  exact ⟨W, hWB t, hW⟩

end MathlibExtTest.Probability.BrownianMotionExistence
