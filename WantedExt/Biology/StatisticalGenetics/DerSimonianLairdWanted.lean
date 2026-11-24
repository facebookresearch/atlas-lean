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
between-study variance), the sampling error `e_i` has mean `0` and known variance `1 / w_i`, and
all `2k` deviations are pairwise uncorrelated and square integrable. Cochran's statistic
`Q = ∑ w_i (y_i - ȳ_w)²`, with `ȳ_w = ∑ w_i y_i / ∑ w_i`, has expectation
`E Q = (k - 1) + Δ² (S₁ - S₂ / S₁)`, where `S_r = ∑ w_i^r`. Equating `Q` with its expectation gives
DerSimonian and Laird's moment estimator `Δ̂² = max {0, (Q - (k - 1)) / (S₁ - S₂ / S₁)}`, and the
pooled estimate uses the weights `w*_i = (1 / w_i + Δ²)⁻¹`.

The statistic `Q` and the inverse-variance weights are defined in
`MathlibExt.Probability.Statistics.CochranQ` and `MathlibExt.Probability.Statistics.MetaAnalysis`
(where the minimum-variance property is proved for independent estimates); here only the
weights `w_i` are needed and the definitions are restated.

Sources: R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Control. Clin. Trials 7
(1986) 177–188, pp. 181–183, equations (2)–(4).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.DerSimonianLairdWanted

open MeasureTheory ProbabilityTheory

variable {k : ℕ}

/-- The weighted mean `ȳ_w = ∑ w_i y_i / ∑ w_i`. -/
noncomputable def weightedMean (w y : Fin k → ℝ) : ℝ :=
  (∑ i, w i * y i) / ∑ i, w i

/-- Cochran's heterogeneity statistic `Q = ∑ w_i (y_i - ȳ_w)²`. -/
noncomputable def cochranQ (w y : Fin k → ℝ) : ℝ :=
  ∑ i, w i * (y i - weightedMean w y) ^ 2

/-- The scaling `S₁ - S₂ / S₁` with `S_r = ∑ w_i^r`. -/
noncomputable def weightScale (w : Fin k → ℝ) : ℝ :=
  (∑ i, w i) - (∑ i, w i ^ 2) / ∑ i, w i

/-- The untruncated moment estimator `(Q - (k - 1)) / (S₁ - S₂ / S₁)` of `Δ²`. -/
noncomputable def momentEstimator (w y : Fin k → ℝ) : ℝ :=
  (cochranQ w y - (k - 1)) / weightScale w

/-- The DerSimonian–Laird estimator `Δ̂² = max {0, (Q - (k - 1)) / (S₁ - S₂ / S₁)}`. -/
noncomputable def dlEstimator (w y : Fin k → ℝ) : ℝ :=
  max 0 (momentEstimator w y)

/-- The random-effects weights `w*_i = (1 / w_i + Δ²)⁻¹`. -/
noncomputable def randomEffectsWeights (w : Fin k → ℝ) (Δsq : ℝ) (i : Fin k) : ℝ :=
  (1 / w i + Δsq)⁻¹

/-- The random-effects model assumptions on study effects `δ`, sampling errors `e`, known weights
`w` and between-study variance `Δ²`: all `2k` deviations are square integrable with mean `0`,
`Var δ_i = Δ²`, `Var e_i = 1 / w_i`, and distinct deviations are uncorrelated. -/
structure RandomEffectsModel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (δ e : Fin k → Ω → ℝ) (w : Fin k → ℝ) (Δsq : ℝ) : Prop where
  memLp_δ : ∀ i, MemLp (δ i) 2 μ
  memLp_e : ∀ i, MemLp (e i) 2 μ
  mean_δ : ∀ i, ∫ ω, δ i ω ∂μ = 0
  mean_e : ∀ i, ∫ ω, e i ω ∂μ = 0
  var_δ : ∀ i, Var[δ i; μ] = Δsq
  var_e : ∀ i, Var[e i; μ] = 1 / w i
  cov_δδ : ∀ i j, i ≠ j → cov[δ i, δ j; μ] = 0
  cov_ee : ∀ i j, i ≠ j → cov[e i, e j; μ] = 0
  cov_δe : ∀ i j, cov[δ i, e j; μ] = 0

/-- **Expectation of Cochran's `Q`** (DerSimonian and Laird 1986, p. 182). Let `μ` be a
probability measure, `k ≥ 2`, `w_i > 0` known weights, `Δ² ≥ 0`, and `y_i = m + δ_i + e_i` where
`δ, e` satisfy the random-effects model assumptions (square integrable, mean `0`,
`Var δ_i = Δ²`, `Var e_i = 1 / w_i`, distinct deviations uncorrelated). Then
`S₁ - S₂ / S₁ > 0` and `E Q = (k - 1) + Δ² (S₁ - S₂ / S₁)`.

Sources: DerSimonian and Laird (1986), p. 182 (the moment equation). -/
public theorem_wanted integral_cochranQ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hk : 2 ≤ k) (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (Δsq m : ℝ)
    (hΔ : 0 ≤ Δsq) (δ e : Fin k → Ω → ℝ) (hmodel : RandomEffectsModel μ δ e w Δsq) :
    0 < weightScale w ∧
      ∫ ω, cochranQ w (fun i => m + δ i ω + e i ω) ∂μ = (k - 1) + Δsq * weightScale w

/-- **Bias of the moment estimators** (DerSimonian and Laird 1986, p. 183). Under the hypotheses
of `integral_cochranQ` (probability measure `μ`, `k ≥ 2`, weights `w_i > 0`, `Δ² ≥ 0`,
`y_i = m + δ_i + e_i` with the random-effects model assumptions), the untruncated estimator
`(Q - (k - 1)) / (S₁ - S₂ / S₁)` has expectation `Δ²`, the DerSimonian–Laird estimator `Δ̂²` is
nonnegative, and `E Δ̂² ≥ Δ²`.

Sources: DerSimonian and Laird (1986), p. 183. -/
public theorem_wanted momentEstimator_unbiased_dlEstimator_bias {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hk : 2 ≤ k) (w : Fin k → ℝ) (hw : ∀ i, 0 < w i)
    (Δsq m : ℝ) (hΔ : 0 ≤ Δsq) (δ e : Fin k → Ω → ℝ)
    (hmodel : RandomEffectsModel μ δ e w Δsq) :
    ∫ ω, momentEstimator w (fun i => m + δ i ω + e i ω) ∂μ = Δsq ∧
      (∀ ω, 0 ≤ dlEstimator w (fun i => m + δ i ω + e i ω)) ∧
      Δsq ≤ ∫ ω, dlEstimator w (fun i => m + δ i ω + e i ω) ∂μ

/-- **The random-effects pooled estimate with known `Δ²`** (DerSimonian and Laird 1986, (2)–(4)).
Under the hypotheses of `integral_cochranQ` (probability measure `μ`, `k ≥ 2`, weights `w_i > 0`,
`Δ² ≥ 0`, `y_i = m + δ_i + e_i` with the random-effects model assumptions), the pooled estimate
`μ̂ = ∑ w*_i y_i / ∑ w*_i` with `w*_i = (1 / w_i + Δ²)⁻¹` has expectation `m` and variance
`(∑ w*_i)⁻¹`, and every weighted average `∑ c_i y_i` with `∑ c_i = 1` has variance at least
`(∑ w*_i)⁻¹`.

Sources: DerSimonian and Laird (1986), p. 183, (2)–(4). -/
public theorem_wanted pooledEstimate_optimal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hk : 2 ≤ k) (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (Δsq m : ℝ)
    (hΔ : 0 ≤ Δsq) (δ e : Fin k → Ω → ℝ) (hmodel : RandomEffectsModel μ δ e w Δsq)
    (c : Fin k → ℝ) (hc : ∑ i, c i = 1) :
    ∫ ω, weightedMean (randomEffectsWeights w Δsq) (fun i => m + δ i ω + e i ω) ∂μ = m ∧
      Var[fun ω => weightedMean (randomEffectsWeights w Δsq) (fun i => m + δ i ω + e i ω); μ] =
        (∑ i, randomEffectsWeights w Δsq i)⁻¹ ∧
      (∑ i, randomEffectsWeights w Δsq i)⁻¹ ≤
        Var[fun ω => ∑ i, c i * (m + δ i ω + e i ω); μ]

/-- **Equal sampling variances** (DerSimonian and Laird 1986, p. 183). Let `k ≥ 2` and let every
weight equal `w = 1 / s² > 0`. For real study estimates `y`, with `ȳ = ∑ y_i / k`: the
DerSimonian–Laird estimator is `max {0, ∑ (y_i - ȳ)² / (k - 1) - s²}`, the weighted mean is `ȳ`,
and for every `Δ² ≥ 0` the random-effects pooled estimate is `ȳ` with
`(∑ w*_i)⁻¹ = (s² + Δ²) / k`.

Sources: DerSimonian and Laird (1986), p. 183. -/
public theorem_wanted equal_weights (hk : 2 ≤ k) (s2 : ℝ) (hs2 : 0 < s2) (y : Fin k → ℝ)
    (Δsq : ℝ) (hΔ : 0 ≤ Δsq) :
    dlEstimator (fun _ : Fin k => 1 / s2) y =
        max 0 ((∑ i, (y i - (∑ j, y j) / k) ^ 2) / (k - 1) - s2) ∧
      weightedMean (fun _ : Fin k => 1 / s2) y = (∑ j, y j) / k ∧
      weightedMean (randomEffectsWeights (fun _ : Fin k => 1 / s2) Δsq) y = (∑ j, y j) / k ∧
      (∑ i, randomEffectsWeights (fun _ : Fin k => 1 / s2) Δsq i)⁻¹ = (s2 + Δsq) / k

end WantedExt.Biology.StatisticalGenetics.DerSimonianLairdWanted
