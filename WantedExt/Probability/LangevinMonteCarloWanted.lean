/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.LangevinMonteCarlo
public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Convergence of Langevin Monte Carlo in Wasserstein distance: wanted

A. S. Dalalyan, *Further and stronger analogy between sampling and optimization: Langevin Monte
Carlo and gradient descent*, arXiv:1704.04752v2 (the corrected arXiv version of the COLT 2017
paper, whose proceedings version prints a different constant), Theorem 1(a): for a strongly
log-concave target with Lipschitz score and a step `h ≤ 2 / (m + M)`, the law of the `K`-th LMC
iterate is within `(1 - m h)^K W₂(ν₀, π) + 1.82 (M / m) (h p)^{1/2}` of the target in `W₂`. The
contraction factor is that of gradient descent on `f`, and the second term is the
discretization bias. Earlier bounds: Dalalyan (2014, total variation), Durmus and Moulines
(arXiv:1605.01559, Wasserstein).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MathlibExt.Probability.LangevinMonteCarlo
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

namespace MathlibExt.Probability.LangevinMonteCarloWanted

/-- **Wasserstein convergence of Langevin Monte Carlo (Dalalyan).** Let `p ≥ 1` and
`f : ℝ^p → ℝ` be differentiable, `m`-strongly convex and with `M`-Lipschitz gradient, in the form
`f θ - f θ' - ⟪∇f θ', θ - θ'⟫ ≥ (m / 2) ‖θ - θ'‖²` and `‖∇f θ - ∇f θ'‖ ≤ M ‖θ - θ'‖`
(`m, M > 0`), and let `π` be the probability measure with density `e^{-f} / ∫ e^{-f}`. Let
`0 < h ≤ 2 / (m + M)` and let `ν k` be the law of the `k`-th Langevin Monte Carlo iterate
`ϑ (k + 1) = ϑ k - h ∇f(ϑ k) + √(2h) ξ (k + 1)` started from a law `ν 0` with finite second
moment. Then for every `K`,
`W₂(ν K, π) ≤ (1 - m h)^K W₂(ν 0, π) + 1.82 (M / m) (h p)^{1/2}`.

Source: A. S. Dalalyan, *Further and stronger analogy between sampling and optimization: Langevin
Monte Carlo and gradient descent*, arXiv:1704.04752v2 (corrected arXiv version of the COLT 2017
paper), Theorem 1(a), under condition (1) and the update rule (2). The finite second moment of
`ν 0` (implicit in the source, where `W₂(ν₀, π)` is finite) excludes the indeterminate `0 · ∞` of
extended arithmetic when `m h = 1`. -/
theorem_wanted wasserstein_lmc_le {p : ℕ} (hp : 0 < p) {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {m M h : ℝ} (hm : 0 < m) (hM : 0 < M) (hdiff : Differentiable ℝ f)
    (hconv : ∀ θ θ' : EuclideanSpace ℝ (Fin p),
      m / 2 * ‖θ - θ'‖ ^ 2 ≤ f θ - f θ' - inner ℝ (gradient f θ') (θ - θ'))
    (hsmooth : ∀ θ θ' : EuclideanSpace ℝ (Fin p),
      ‖gradient f θ - gradient f θ'‖ ≤ M * ‖θ - θ'‖)
    (hh : 0 < h) (hh2 : h ≤ 2 / (m + M))
    (π : ProbabilityMeasure (EuclideanSpace ℝ (Fin p)))
    (hπ : (π : Measure (EuclideanSpace ℝ (Fin p))) = volume.withDensity
      (fun θ => ENNReal.ofReal (Real.exp (-f θ) / ∫ u, Real.exp (-f u))))
    (ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin p)))
    (hν0 : ∫⁻ θ, ‖θ‖ₑ ^ 2 ∂(ν 0 : Measure (EuclideanSpace ℝ (Fin p))) < ∞)
    (hν : ∀ k, (ν (k + 1) : Measure (EuclideanSpace ℝ (Fin p))) = lmcStep f h (ν k))
    (K : ℕ) :
    wasserstein 2 (ν K) π ≤
      ENNReal.ofReal ((1 - m * h) ^ K) * wasserstein 2 (ν 0) π +
        ENNReal.ofReal (182 / 100 * (M / m) * Real.sqrt (h * p))

end MathlibExt.Probability.LangevinMonteCarloWanted
