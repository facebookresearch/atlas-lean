/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The DerSimonian–Laird random-effects estimator

In the random-effects model of meta-analysis, study `i` of `k ≥ 2` reports
`y_i = μ + δ_i + e_i`, where the study effect `δ_i` has mean `0` and variance `Δ²` (the
between-study variance), the sampling error `e_i` has mean `0` and known variance `v_i > 0`, and
all `2k` deviations are pairwise uncorrelated and square integrable. With the fixed-effect weights
`w_i = 1 / v_i`, Cochran's statistic `Q` (`MetaAnalysis.cochranQ v y`) has expectation
`E Q = (k - 1) + Δ² (S₁ - S₂ / S₁)`, where `S_r = ∑ w_i^r`. Equating `Q` with its expectation
gives DerSimonian and Laird's moment estimator `Δ̂² = max {0, (Q - (k - 1)) / (S₁ - S₂ / S₁)}`.
The pooled estimate weights study `i` in proportion to `(v_i + Δ²)⁻¹`, that is, it uses the
inverse-variance weights `MetaAnalysis.inverseVarianceWeights` of the total variances
`v_i + Δ²`; its variance is `(∑ (v_i + Δ²)⁻¹)⁻¹`.

Cochran's statistic and the inverse-variance weights are those of
`MathlibExt.Probability.Statistics.CochranQ` and `MathlibExt.Probability.Statistics.MetaAnalysis`,
where the minimum-variance property of the weights is proved for independent estimates. Here the
deviations are only assumed uncorrelated, as in the source.

Sources: R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Control. Clin. Trials 7
(1986) 177–188, pp. 181–183, equations (2)–(4).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Moments.Covariance
public import MathlibExt.Probability.Statistics.CochranQ
public import MathlibExt.Probability.Statistics.DerSimonianLaird

@[expose] public section

namespace WantedExt.Probability.Statistics.DerSimonianLairdWanted

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MetaAnalysis

variable {k : ℕ}

/-- **Random-effects model.** The assumptions on study effects `δ`, sampling errors `e`, known
sampling variances `v` and between-study variance `Δ²`: all `2k` deviations are square integrable
with mean `0`, `Var δ_i = Δ²`, `Var e_i = v_i`, and distinct deviations are uncorrelated. -/
structure RandomEffectsModel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (δ e : Fin k → Ω → ℝ) (v : Fin k → ℝ) (Δsq : ℝ) : Prop where
  memLp_δ : ∀ i, MemLp (δ i) 2 μ
  memLp_e : ∀ i, MemLp (e i) 2 μ
  mean_δ : ∀ i, ∫ ω, δ i ω ∂μ = 0
  mean_e : ∀ i, ∫ ω, e i ω ∂μ = 0
  var_δ : ∀ i, Var[δ i; μ] = Δsq
  var_e : ∀ i, Var[e i; μ] = v i
  cov_δδ : ∀ i j, i ≠ j → cov[δ i, δ j; μ] = 0
  cov_ee : ∀ i j, i ≠ j → cov[e i, e j; μ] = 0
  cov_δe : ∀ i j, cov[δ i, e j; μ] = 0

/-- **Expectation of Cochran's `Q`.** Let `μ` be a
probability measure, `k ≥ 2`, `v_i > 0` known sampling variances, `Δ² ≥ 0`, and
`y_i = m + δ_i + e_i` where `δ, e` satisfy the random-effects model assumptions (square
integrable, mean `0`, `Var δ_i = Δ²`, `Var e_i = v_i`, distinct deviations uncorrelated). Then
`S₁ - S₂ / S₁ > 0` and `E[cochranQ v y] = (k - 1) + Δ² (S₁ - S₂ / S₁)`, with `S_r = ∑ (v_i⁻¹)^r`.

Sources: R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Control. Clin. Trials 7
(1986) 177–188, p. 182 (the moment equation). -/
public theorem_wanted integral_cochranQ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hk : 2 ≤ k) (v : Fin k → ℝ) (hv : ∀ i, 0 < v i) (Δsq m : ℝ)
    (hΔ : 0 ≤ Δsq) (δ e : Fin k → Ω → ℝ) (hmodel : RandomEffectsModel μ δ e v Δsq) :
    0 < weightScale v ∧
      ∫ ω, cochranQ v (fun i => m + δ i ω + e i ω) ∂μ = (k - 1) + Δsq * weightScale v

/-- **Bias of the moment estimators.** Under the hypotheses
of `integral_cochranQ` (probability measure `μ`, `k ≥ 2`, sampling variances `v_i > 0`,
`Δ² ≥ 0`, `y_i = m + δ_i + e_i` with the random-effects model assumptions), the untruncated
estimator `(Q - (k - 1)) / (S₁ - S₂ / S₁)` has expectation `Δ²`, the DerSimonian–Laird estimator
`Δ̂²` is nonnegative, and `E Δ̂² ≥ Δ²`.

Sources: R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Control. Clin. Trials 7
(1986) 177–188, p. 183. -/
public theorem_wanted momentEstimator_unbiased_dlEstimator_bias {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hk : 2 ≤ k) (v : Fin k → ℝ) (hv : ∀ i, 0 < v i)
    (Δsq m : ℝ) (hΔ : 0 ≤ Δsq) (δ e : Fin k → Ω → ℝ)
    (hmodel : RandomEffectsModel μ δ e v Δsq) :
    ∫ ω, momentEstimator v (fun i => m + δ i ω + e i ω) ∂μ = Δsq ∧
      (∀ ω, 0 ≤ dlEstimator v (fun i => m + δ i ω + e i ω)) ∧
      Δsq ≤ ∫ ω, dlEstimator v (fun i => m + δ i ω + e i ω) ∂μ

/-- **The random-effects pooled estimate with known `Δ²`.**
Under the hypotheses of `integral_cochranQ` (probability measure `μ`, `k ≥ 2`, sampling variances
`v_i > 0`, `Δ² ≥ 0`, `y_i = m + δ_i + e_i` with the random-effects model assumptions), the pooled
estimate `∑ᵢ ωᵢ yᵢ` with the inverse-variance weights `ω` of `v_i + Δ²` has expectation `m` and
variance `(∑ᵢ (v_i + Δ²)⁻¹)⁻¹`, and every weighted average `∑ c_i y_i` with `∑ c_i = 1` has
variance at least `(∑ᵢ (v_i + Δ²)⁻¹)⁻¹`.

Sources: R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Control. Clin. Trials 7
(1986) 177–188, p. 183, equations (2)–(4). -/
public theorem_wanted pooledEstimate_optimal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hk : 2 ≤ k) (v : Fin k → ℝ) (hv : ∀ i, 0 < v i) (Δsq m : ℝ)
    (hΔ : 0 ≤ Δsq) (δ e : Fin k → Ω → ℝ) (hmodel : RandomEffectsModel μ δ e v Δsq)
    (c : Fin k → ℝ) (hc : ∑ i, c i = 1) :
    ∫ ω, pooledEstimate v Δsq (fun i => m + δ i ω + e i ω) ∂μ = m ∧
      Var[fun ω => pooledEstimate v Δsq (fun i => m + δ i ω + e i ω); μ] =
        (∑ i, (v i + Δsq)⁻¹)⁻¹ ∧
      (∑ i, (v i + Δsq)⁻¹)⁻¹ ≤ Var[fun ω => ∑ i, c i * (m + δ i ω + e i ω); μ]

end WantedExt.Probability.Statistics.DerSimonianLairdWanted
