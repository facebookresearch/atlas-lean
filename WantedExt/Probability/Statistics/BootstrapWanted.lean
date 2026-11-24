/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.MallowsMetric
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The bootstrap for the mean (Bickel and Freedman, 1981)

Efron's bootstrap approximates the sampling distribution of `√n (μ_n - μ)` by the conditional
law, given the data `X₁, …, X_n`, of `√m (μ*_m - μ_n)`, where `X*₁, …, X*_m` are drawn
independently and uniformly from the data. Bickel and Freedman proved that the approximation is
asymptotically valid whenever the variance is finite (P. J. Bickel and D. A. Freedman, "Some
asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217).

Resampling is written through the indices: a bootstrap sample of size `m` from
`X₀, …, X_n` (here `n + 1` data points, to avoid the empty sample) is `X_{I(1)}, …, X_{I(m)}`
for a uniformly random map `I : Fin m → Fin (n + 1)`, so a bootstrap expectation is the average
over the `(n + 1)^m` maps `I`. Weak convergence is tested against bounded continuous functions.

Their proof combines the almost sure convergence of the empirical law in the Mallows metric
(`tendsto_wasserstein_empirical`) with Mallows' contraction of normalised sums
(`MathlibExt.Probability.Statistics.MallowsMetric.wasserstein_two_normalizedSum_le`) and the
central limit theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

namespace MathlibExt.Probability.Statistics.BootstrapWanted

/-- **Almost sure convergence of the empirical law in the Mallows metric** (P. J. Bickel and
D. A. Freedman, *Ann. Statist.* 9 (1981), Lemma 8.4, and (2.1) for `p = 2` on the line). Let
`E` be a separable Banach space, `1 ≤ p < ∞`, and `X₀, X₁, …` i.i.d. `E`-valued with law
`μ ∈ Γ_p` (finite `p`-th moment). If `F n ω` is the empirical law `(n+1)⁻¹ ∑_{i ≤ n} δ_{X_i(ω)}`,
then `d_p(F n ω, μ) → 0` for almost every `ω`. -/
theorem_wanted tendsto_wasserstein_empirical {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [NormedAddCommGroup E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] {p : ℝ} (hp : 1 ≤ p) {X : ℕ → Ω → E}
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (μ : ProbabilityMeasure E)
    (hlaw : P.map (X 0) = (μ : Measure E)) (hmom : ∫⁻ x, ‖x‖ₑ ^ p ∂(μ : Measure E) < ∞)
    (F : ℕ → Ω → ProbabilityMeasure E)
    (hF : ∀ n ω, (F n ω : Measure E) =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range (n + 1), Measure.dirac (X i ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => wasserstein p (F n ω) μ) atTop (𝓝 0)

/-- **Bickel–Freedman bootstrap central limit theorem for the mean** (P. J. Bickel and
D. A. Freedman, *Ann. Statist.* 9 (1981), Theorem 2.1(a)). Let `X₀, X₁, …` be i.i.d. real
random variables with finite positive variance `σ²`, and let `μ_n` be the mean of the first
`n + 1` of them. Along almost every sample sequence, as `n` and `m` tend to infinity jointly,
the conditional law of `√m (μ*_m - μ_n)` given the data converges weakly to `N(0, σ²)`; here the
conditional expectation of `f(√m (μ*_m - μ_n))` is the average over all resampling maps
`I : Fin m → Fin (n + 1)`. -/
theorem_wanted bootstrap_mean_tendsto_gaussianReal {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hL2 : MemLp (X 0) 2 P) {σsq : ℝ≥0} (hvar : variance (X 0) P = σsq) (hpos : 0 < σsq) :
    ∀ᵐ ω ∂P, ∀ f : ℝ →ᵇ ℝ, Tendsto (fun nm : ℕ × ℕ =>
        (((nm.1 + 1 : ℕ) : ℝ) ^ nm.2)⁻¹ * ∑ I : Fin nm.2 → Fin (nm.1 + 1),
          f (Real.sqrt nm.2 * ((nm.2 : ℝ)⁻¹ * ∑ j, X (I j) ω -
            ((nm.1 + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (nm.1 + 1), X i ω)))
      (atTop ×ˢ atTop) (𝓝 (∫ x, f x ∂(gaussianReal 0 σsq)))

/-- **Consistency of the bootstrap standard deviation** (P. J. Bickel and D. A. Freedman,
*Ann. Statist.* 9 (1981), Theorem 2.1(b)). Under the hypotheses of
`bootstrap_mean_tendsto_gaussianReal`, along almost every sample sequence the bootstrap standard
deviation `s*_m = ((1/m) ∑_j (X*_j - μ*_m)²)^{1/2}` converges to `σ` in conditional probability:
for every `ε > 0` the proportion of resampling maps `I : Fin m → Fin (n + 1)` with
`|s*_m - σ| > ε` tends to `0` as `n, m → ∞`. -/
theorem_wanted bootstrap_sd_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hL2 : MemLp (X 0) 2 P) {σsq : ℝ≥0} (hvar : variance (X 0) P = σsq) (hpos : 0 < σsq) :
    ∀ᵐ ω ∂P, ∀ ε > 0, Tendsto (fun nm : ℕ × ℕ =>
        (((nm.1 + 1 : ℕ) : ℝ) ^ nm.2)⁻¹ *
          ((Finset.univ.filter fun I : Fin nm.2 → Fin (nm.1 + 1) =>
            ε < |Real.sqrt ((nm.2 : ℝ)⁻¹ * ∑ j, (X (I j) ω -
              (nm.2 : ℝ)⁻¹ * ∑ l, X (I l) ω) ^ 2) - Real.sqrt σsq|).card : ℝ))
      (atTop ×ˢ atTop) (𝓝 0)

/-- **Bootstrap of the mean in `ℝ^k`** (P. J. Bickel and D. A. Freedman, *Ann. Statist.* 9
(1981), Theorem 2.2(a)). Let `X₀, X₁, …` be i.i.d. in `ℝ^k` with `E‖X₀‖² < ∞`, and let `S` be
the covariance matrix of `X₀`. Along almost every sample sequence, as `n, m → ∞`, the
conditional law of `√m ((1/m) ∑_j X*_j - (1/(n+1)) ∑_{i ≤ n} X_i)` converges weakly to the
centred normal law with covariance `S`. -/
theorem_wanted bootstrap_mean_tendsto_multivariateGaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P) :
    ∀ᵐ ω ∂P, ∀ f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ, Tendsto (fun nm : ℕ × ℕ =>
        (((nm.1 + 1 : ℕ) : ℝ) ^ nm.2)⁻¹ * ∑ I : Fin nm.2 → Fin (nm.1 + 1),
          f (Real.sqrt nm.2 • ((nm.2 : ℝ)⁻¹ • ∑ j, X (I j) ω -
            ((nm.1 + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (nm.1 + 1), X i ω)))
      (atTop ×ˢ atTop)
      (𝓝 (∫ x, f x ∂(multivariateGaussian 0
        (Matrix.of fun a b => cov[fun ω => X 0 ω a, fun ω => X 0 ω b; P]))))

end MathlibExt.Probability.Statistics.BootstrapWanted
