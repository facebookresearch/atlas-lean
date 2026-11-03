/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianQuadraticVariation
public import MathlibExt.Probability.OrnsteinUhlenbeck

/-!
# Tests for the quadratic variation of Brownian motion

Boundary values of `weightedQVError` (no cells; zero weight), and a non-vacuity witness: the
coordinate process of the Kolmogorov-extension Brownian measure on paths has quadratic variation
`t` in `L²` and in probability.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.BrownianQuadraticVariation

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}

/-- With no cells the error is `0`. -/
example (φ : ℝ → ℝ) (t : ℝ≥0) (ω : Ω) : weightedQVError φ B t 0 ω = 0 := by
  simp [weightedQVError]

/-- With zero weight the error is `0`. -/
example (t : ℝ≥0) (n : ℕ) (ω : Ω) : weightedQVError (fun _ ↦ 0) B t n ω = 0 := by
  simp [weightedQVError]

/-- Non-vacuity: a pre-Brownian motion exists, and its quadratic variation along uniform
partitions of `[0, t]` tends to `t` in `L²` and in probability. -/
example (t : ℝ≥0) : ∃ μ : Measure (ℝ≥0 → ℝ),
    Tendsto (fun n : ℕ ↦ eLpNorm (fun f : ℝ≥0 → ℝ ↦ ∑ k ∈ Finset.range n,
      (f (t * (k + 1) / n) - f (t * k / n)) ^ 2 - t) 2 μ) atTop (𝓝 0) ∧
    TendstoInMeasure μ (fun (n : ℕ) (f : ℝ≥0 → ℝ) ↦ ∑ k ∈ Finset.range n,
      (f (t * (k + 1) / n) - f (t * k / n)) ^ 2) atTop (fun _ ↦ (t : ℝ)) := by
  obtain ⟨μ, hμ⟩ := exists_isPreBrownianReal_eval
  exact ⟨μ, hμ.tendsto_eLpNorm_sum_sq_sub t, hμ.tendstoInMeasure_sum_sq t⟩

end MathlibExtTest.Probability.BrownianQuadraticVariation
