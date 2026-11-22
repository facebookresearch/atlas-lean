/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OrnsteinUhlenbeckSDE

/-!
# Tests for the pathwise Ornstein–Uhlenbeck solution

Both Ornstein–Uhlenbeck statements instantiated on a Brownian motion, the law of the solution
started at `0` (`X t ~ N(0, (σ² / (2θ)) (1 - e^{-2θt}))`, through
`IsOrnsteinUhlenbeckFromZero.hasLaw_eval`), the stationary law, and the boundary value
`cov[X 0, X 0] = v` of the general covariance formula (variance of the start).
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExtTest.Probability.OrnsteinUhlenbeckSDE

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Started at `0`, the solution is an OU process; its value at time `t` has law
`N(0, (σ² / (2θ)) (1 - e^{-2θt}))`. -/
example (hB : IsBrownianReal B P) {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) (t : ℝ≥0) :
    HasLaw (fun ω ↦ ouPathSolution θ σ 0 (fun u ↦ B (Real.toNNReal u) ω) t)
      (gaussianReal 0 (σ ^ 2 / (2 * θ) * (1 - exp (-2 * θ * t))).toNNReal) P :=
  (hB.isOrnsteinUhlenbeckFromZero_ouPathSolution hθ σ).hasLaw_eval t

/-- Started from `N(0, σ² / (2θ))` independent of `B`, the solution is stationary: every time
has the stationary law. -/
example (hB : IsBrownianReal B P) {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) {X₀ : Ω → ℝ}
    (hX₀ : HasLaw X₀ (gaussianReal 0 (σ ^ 2 / (2 * θ)).toNNReal) P)
    (hind : IndepFun X₀ (fun ω t ↦ B t ω) P) (t : ℝ≥0) :
    HasLaw (fun ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) t)
      (gaussianReal 0 (σ ^ 2 / (2 * θ)).toNNReal) P :=
  (hB.isStationaryOrnsteinUhlenbeck_ouPathSolution hθ σ hX₀ hind).hasLaw_eval t

/-- Boundary value of the general covariance formula: at `s = t = 0` it is the variance `v` of
the start. -/
example (hB : IsBrownianReal B P) {θ : ℝ} (hθ : θ ≠ 0) (σ : ℝ) {X₀ : Ω → ℝ} {v : ℝ≥0}
    (hX₀ : HasLaw X₀ (gaussianReal 0 v) P) (hind : IndepFun X₀ (fun ω t ↦ B t ω) P) :
    cov[fun ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) 0,
      fun ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) 0; P] = v := by
  simpa using (hB.isGaussianProcess_ouPathSolution hθ σ hX₀ hind).2.2 0 0

end MathlibExtTest.Probability.OrnsteinUhlenbeckSDE
