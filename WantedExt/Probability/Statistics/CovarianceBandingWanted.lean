/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.CovarianceBanding
public import MathlibExt.Probability.Statistics.PCA
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Operator-norm rate of the banded sample covariance (Bickel and Levina, 2008)

For `n` i.i.d. Gaussian vectors in `ℝ^p` with covariance `Σ` in the bandable class
`U(ε₀, α, C)`, banding the sample covariance at width `k_n ≍ (n⁻¹ log p)^{-1/(2(α+1))}` gives an
estimator of `Σ`, and of `Σ⁻¹` by inversion, that is consistent in operator norm at the rate
`(n⁻¹ log p)^{α/(2(α+1))}`, uniformly over the class (P. J. Bickel and E. Levina, "Regularized
estimation of large covariance matrices", *Ann. Statist.* 36 (2008) 199–227, Theorem 1).

The deterministic half of the proof is proved in
`MathlibExt.Probability.Statistics.CovarianceBanding`; the probabilistic half is a
union bound over the `p²` entries of `Σ̂ - Σ` with Gaussian (sub-exponential) tail bounds.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal Matrix.Norms.L2Operator

open MathlibExt.Probability.Statistics.CovarianceBanding

namespace MathlibExt.Probability.Statistics.CovarianceBandingWanted

/-- **Bickel–Levina rate for the banded sample covariance** (P. J. Bickel and E. Levina,
*Ann. Statist.* 36 (2008), Theorem 1). Let `p n ≥ 2` be dimensions with `log p_n / n → 0`, let
`ε₀, α, C > 0`, and for a sample `X₁, …, X_n` let `Σ̂ = n⁻¹ ∑_i (X_i - X̄)(X_i - X̄)ᵀ` (their
equation (1)). With `k_n = ⌈(n⁻¹ log p_n)^{-1/(2(α+1))}⌉` and
`r_n = (n⁻¹ log p_n)^{α/(2(α+1))}`, both `‖B_{k_n}(Σ̂) - Σ‖` and `‖B_{k_n}(Σ̂)⁻¹ - Σ⁻¹‖` are
`O_P(r_n)` uniformly over `Σ ∈ U(ε₀, α, C)` when `X_i` are i.i.d. `N(0, Σ)`: for every `η > 0`
there are `K` and `N` such that for all `n ≥ N` and all `Σ` in the class each of the two events
`{‖·‖ > K r_n}` has probability at most `η`. The hypothesis `log p_n / n → 0` is the regime of
the paper's abstract and of its proof (which uses tail bounds for `t ≍ (n⁻¹ log p)^{1/2}` small);
`p_n ≥ 2` keeps `log p_n > 0`. -/
theorem_wanted banded_sampleCovariance_rate (p : ℕ → ℕ) (hp : ∀ n, 2 ≤ p n)
    (hlog : Tendsto (fun n : ℕ => Real.log (p n) / n) atTop (𝓝 0))
    {ε₀ α C : ℝ} (hε₀ : 0 < ε₀) (hα : 0 < α) (hC : 0 < C) :
    ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ S ∈ bandableClass (p := p n) ε₀ α C,
      (Measure.pi fun _ : Fin n => multivariateGaussian 0 S)
          {X | K * (Real.log (p n) / n) ^ (α / (2 * (α + 1))) <
            ‖band ⌈(Real.log (p n) / n) ^ (-1 / (2 * (α + 1)))⌉₊
                ((n : ℝ)⁻¹ • ((PCA.center (Matrix.of fun i j => X i j))ᵀ *
                  PCA.center (Matrix.of fun i j => X i j))) - S‖} ≤ ENNReal.ofReal η ∧
      (Measure.pi fun _ : Fin n => multivariateGaussian 0 S)
          {X | K * (Real.log (p n) / n) ^ (α / (2 * (α + 1))) <
            ‖(band ⌈(Real.log (p n) / n) ^ (-1 / (2 * (α + 1)))⌉₊
                ((n : ℝ)⁻¹ • ((PCA.center (Matrix.of fun i j => X i j))ᵀ *
                  PCA.center (Matrix.of fun i j => X i j))))⁻¹ - S⁻¹‖} ≤ ENNReal.ofReal η

end MathlibExt.Probability.Statistics.CovarianceBandingWanted
