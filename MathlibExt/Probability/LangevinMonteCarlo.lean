/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The Langevin Monte Carlo algorithm

The Langevin Monte Carlo (LMC) algorithm, or unadjusted Langevin algorithm, samples
approximately from a density `π ∝ e^{-f}` on a finite-dimensional real inner product space by
the update `ϑ (k + 1) = ϑ k - h ∇f (ϑ k) + √(2 h) ξ (k + 1)`, with `ξ (k + 1)` standard Gaussian
and independent of `ϑ k` (A. S. Dalalyan, *Further and stronger analogy between sampling and
optimization: Langevin Monte Carlo and gradient descent*, arXiv:1704.04752v2, eq. (2)). It is the
Euler discretization of the Langevin diffusion `dL = -∇f(L) dt + √2 dW`, and gradient descent
plus Gaussian noise.

This file defines the update on laws, `lmcStep f h μ`: the law of `ϑ - h ∇f ϑ + √(2h) ξ` when
`ϑ ∼ μ` and `ξ` is an independent standard Gaussian vector, and computes one step from a point
(`lmcStep_dirac`). The `W₂` convergence of the iterates for strongly log-concave targets is
recorded in `WantedExt/Probability/LangevinMonteCarloWanted.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.LangevinMonteCarlo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **One step of the Langevin Monte Carlo algorithm, on laws.** If `ϑ ∼ μ` and `ξ` is a standard
Gaussian vector independent of `ϑ`, then `lmcStep f h μ` is the law of
`ϑ - h ∇f(ϑ) + √(2h) ξ`: the pushforward of `μ ⊗ 𝒩(0, I)` by that map (A. S. Dalalyan,
arXiv:1704.04752v2, update rule (2)). -/
noncomputable def lmcStep (f : E → ℝ) (h : ℝ) (μ : Measure E) : Measure E :=
  (μ.prod (stdGaussian E)).map
    (fun q : E × E => q.1 - h • gradient f q.1 + Real.sqrt (2 * h) • q.2)

/-- **One Langevin Monte Carlo step from a point is Gaussian.** If `∇f` is continuous, then
from a deterministic point `x` the law of `x - h ∇f(x) + √(2h) ξ` is the standard Gaussian pushed
forward by `ξ ↦ x - h ∇f(x) + √(2h) ξ`, that is `𝒩(x - h ∇f(x), 2h I)` for `h ≥ 0`: a gradient
descent step plus Gaussian noise (A. S. Dalalyan, arXiv:1704.04752v2, update rule (2) with a
deterministic `ϑ(0)`). -/
theorem lmcStep_dirac {f : E → ℝ} (hf : Continuous (gradient f)) (h : ℝ) (x : E) :
    lmcStep f h (Measure.dirac x) =
      (stdGaussian E).map (fun ξ : E => x - h • gradient f x + Real.sqrt (2 * h) • ξ) := by
  have hc : Continuous (fun q : E × E => q.1 - h • gradient f q.1 + Real.sqrt (2 * h) • q.2) := by
    fun_prop
  rw [lmcStep, Measure.dirac_prod, Measure.map_map hc.measurable measurable_prodMk_left]
  rfl

end MathlibExt.Probability.LangevinMonteCarlo
