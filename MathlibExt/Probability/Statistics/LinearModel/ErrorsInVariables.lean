/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.StrongLaw

/-!
# Errors in variables: attenuation of the OLS slope and its correction

In the classical errors-in-variables (measurement-error) model the response follows
`y i = β₀ + β ξ i + ε i`, but the regressor `ξ i` is observed only through
`x i = ξ i + u i`, with measurement error `u i`. The naive least-squares slope of `y` on the
observed `x` (`FiniteProbability.olsSlope`, `S_xy / S_xx`) is inconsistent: its probability limit
is `λ β`, where

`λ = σ_ξ² / (σ_ξ² + σ_u²)`

is the *attenuation factor* (reliability ratio). Since `0 ≤ λ < 1` whenever `σ_u² > 0`, the
naive slope is biased toward zero ("regression dilution").

If the measurement-error variance `σ_u²` is known, or consistently estimated by `σ̂_u²`, the
method-of-moments (reliability-ratio) corrected slope `S_xy / (S_xx - n σ̂_u²)` is consistent
for `β`; it is the naive slope divided by the estimated reliability ratio
`(s_x² - σ̂_u²) / s_x²` (`correctedSlope_eq_olsSlope_div`).

## Model and hypotheses

`ClassicalErrorsInVariables μ ξ u ε` records the sampling hypotheses on the sequence of
triples `(ξ i, u i, ε i)`: pairwise independent across `i` (the hypothesis of Etemadi's strong
law `ProbabilityTheory.strong_law_ae_real`), identically distributed, square integrable, and with
`ξ`, `u`, `ε` pairwise uncorrelated within an observation. These are moment conditions: the
textbook assumption that `u` and `ε` are mean-zero and independent of `ξ` and of each other
implies them, and no mean-zero hypothesis is needed for the slope.

## Main results

* `attenuationFactor`: `λ = σ_ξ² / (σ_ξ² + σ_u²)`.
* `measurementError_population_attenuation_of_cov_eq_zero`: for square-integrable, pairwise
  uncorrelated `ξ`, `u`, `ε`, the totalized ratio `cov[x, y] / Var[x]` for `y = β₀ + β ξ + ε` and
  `x = ξ + u` is `λ β`; `measurementError_population_attenuation` is the independence form.
* `measurementError_population_slope_of_cov_eq_zero`: when `Var[x] ≠ 0`, `λ β` is the population
  least-squares slope of `y` on `x`, the unique `b` with `cov[x, y - b x] = 0`.
* `correctedSlope`: `S_xy / (S_xx - n σ²)`, and `correctedSlope_eq_olsSlope_div`.
* `ae_tendsto_sxy_div`: for i.i.d. square-integrable pairs, `S_xy / n → cov[X, Y]` a.s.
* `ae_tendsto_olsSlope_attenuation`, `tendstoInMeasure_olsSlope_attenuation`: the naive OLS
  slope converges almost surely, hence in probability, to `λ β`.
* `ae_tendsto_correctedSlope`, `ae_tendsto_correctedSlope_of_ae_tendsto`: the corrected slope
  with known `σ_u²`, or with an almost surely consistent estimate, converges a.s. to `β`.
* `tendstoInMeasure_correctedSlope`: with an estimate `σ̂_u²` consistent in probability, the
  corrected slope converges in probability to `β`.

## References

* W. A. Fuller, *Measurement Error Models*, Wiley (1987), §1.1.
* J. M. Wooldridge, *Econometric Analysis of Cross Section and Panel Data*, 2nd ed., §4.4.2.
* W. H. Greene, *Econometric Analysis*, 8th ed., §8.8 (measurement error).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Topology
open MathlibExt.Probability.FiniteProbability

namespace MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables

/-! ### Definitions and the finite-sample identities -/

/-- The **attenuation factor** (reliability ratio) `λ = σ_ξ² / (σ_ξ² + σ_u²)` of the classical
errors-in-variables model, for signal variance `σξ2` and measurement-error variance `σu2`. The
naive OLS slope converges to `λ β` (`ae_tendsto_olsSlope_attenuation`). -/
noncomputable def attenuationFactor (σξ2 σu2 : ℝ) : ℝ :=
  σξ2 / (σξ2 + σu2)

/-- The **measurement-error corrected slope** `S_xy / (S_xx - n σu2)` of `y` on `x`, for a known
or estimated measurement-error variance `σu2` and `n = card ι`. It is the method-of-moments
estimator `s_xy / (s_x² - σu2)`, i.e. the naive slope `olsSlope x y` divided by the estimated
reliability ratio `(s_x² - σu2) / s_x²` (`correctedSlope_eq_olsSlope_div`); at `σu2 = 0` it is
`olsSlope x y` (`correctedSlope_zero`). Lean's `a / 0 = 0` makes it `0` when the denominator
vanishes. -/
noncomputable def correctedSlope {ι : Type*} [Fintype ι] (x y : ι → ℝ) (σu2 : ℝ) : ℝ :=
  sxy x y / (sxy x x - Fintype.card ι * σu2)

theorem correctedSlope_zero {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    correctedSlope x y 0 = olsSlope x y := by
  rw [correctedSlope, olsSlope, mul_zero, sub_zero]

/-- The divide-by-`n` sample variance is `S_xx / n`. -/
theorem sampleVar_eq_sxy_div {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    sampleVar x = sxy x x / Fintype.card ι := by
  rw [sampleVar, sxy_self_eq]

/-- **Reliability-ratio form of the correction**: if `S_xx ≠ 0`, the corrected slope is the naive
OLS slope divided by the estimated reliability ratio `(s_x² - σu2) / s_x²`. -/
theorem correctedSlope_eq_olsSlope_div {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : sxy x x ≠ 0)
    (y : ι → ℝ) (σu2 : ℝ) :
    correctedSlope x y σu2 = olsSlope x y / ((sampleVar x - σu2) / sampleVar x) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    intro hc
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hc)
    exact hx (by simp [sxy])
  rw [correctedSlope, olsSlope, sampleVar_eq_sxy_div]
  by_cases hd : sxy x x - Fintype.card ι * σu2 = 0
  · have hd' : sxy x x / Fintype.card ι - σu2 = 0 := by
      rw [div_sub' hn, hd, zero_div]
    rw [hd, hd', zero_div, div_zero, div_zero]
  · have hd' : sxy x x / Fintype.card ι - σu2 ≠ 0 := by
      rw [div_sub' hn]; exact div_ne_zero (fun h => hd (by linarith)) hn
    field_simp

/-- For the first `n` terms of two sequences, `S_xy / n` is the mean of the products minus the
product of the means, with sums over `range n`. -/
theorem sxy_div_eq (a b : ℕ → ℝ) (n : ℕ) :
    sxy (fun i : Fin n => a i) (fun i => b i) / n =
      (∑ i ∈ range n, a i * b i) / n -
        ((∑ i ∈ range n, a i) / n) * ((∑ i ∈ range n, b i) / n) := by
  rw [sxy_eq_sum_mul_sub, sampleMean_eq_sum_div, sampleMean_eq_sum_div, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun i => a i * b i), Fin.sum_univ_eq_sum_range a,
    Fin.sum_univ_eq_sum_range b]
  rcases eq_or_ne (n : ℝ) 0 with hn | hn
  · simp [hn]
  · field_simp

/-! ### Strong law for the sample covariance -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Strong law for the sample covariance**: if the pairs `(X i, Y i)` are pairwise independent,
identically distributed and square integrable, then `S_xy / n` of the first `n` pairs converges
almost surely to `cov[X 0, Y 0]`. -/
theorem ae_tendsto_sxy_div [IsProbabilityMeasure μ] {X Y : ℕ → Ω → ℝ}
    (hindep : Pairwise fun i j =>
      IndepFun (fun ω => (X i ω, Y i ω)) (fun ω => (X j ω, Y j ω)) μ)
    (hident : ∀ i, IdentDistrib (fun ω => (X i ω, Y i ω)) (fun ω => (X 0 ω, Y 0 ω)) μ μ)
    (hX : MemLp (X 0) 2 μ) (hY : MemLp (Y 0) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => sxy (fun i : Fin n => X i ω) (fun i => Y i ω) / n) atTop
      (𝓝 cov[X 0, Y 0; μ]) := by
  have slln : ∀ f : ℝ × ℝ → ℝ, Measurable f → Integrable (fun ω => f (X 0 ω, Y 0 ω)) μ →
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ range n, f (X i ω, Y i ω)) / n) atTop
        (𝓝 (∫ ω, f (X 0 ω, Y 0 ω) ∂μ)) := fun f hf hint =>
    strong_law_ae_real (fun i ω => f (X i ω, Y i ω)) hint
      (fun _ _ hij => (hindep hij).comp hf hf) (fun i => (hident i).comp hf)
  filter_upwards [slln (fun p => p.1 * p.2) (by fun_prop) (hX.integrable_mul hY),
    slln (fun p => p.1) (by fun_prop) (hX.integrable one_le_two),
    slln (fun p => p.2) (by fun_prop) (hY.integrable one_le_two)] with ω hxy hx hy
  rw [covariance_eq_sub hX hY]
  exact (hxy.sub (hx.mul hy)).congr
    fun n => (sxy_div_eq (fun i => X i ω) (fun i => Y i ω) n).symm

/-! ### Population attenuation identity -/

/-- **Population attenuation identity**, totalized ratio form: if `X`, `e` and `ε` are square
integrable and pairwise uncorrelated, then for `Y = α + β X + ε` and the mismeasured regressor
`W = X + e`, the ratio `cov[W, Y] / Var[W]` equals `λ β`, with attenuation factor
`λ = Var[X] / (Var[X] + Var[e])`. This is an identity of totalized real ratios and carries no
`Var[W] ≠ 0` hypothesis: if `Var[W] = 0`, both sides are `0` only because real division by zero
is zero, and there is no population least-squares slope. When `Var[W] ≠ 0` the ratio is that
slope; `measurementError_population_slope_of_cov_eq_zero` states the nondegenerate slope form.
The hypotheses are the moment conditions of `ClassicalErrorsInVariables`;
`measurementError_population_attenuation` is the form with independence hypotheses. The condition
`cov[X, ε] = 0` (exogeneity) cannot be dropped: with `e = 0` and nonconstant `ε = X` the slope is
`β + 1`, not `β`.

This is the population form of the attenuation result in W. A. Fuller, *Measurement Error
Models*, Wiley (1987), Chapter 1. -/
theorem measurementError_population_attenuation_of_cov_eq_zero [IsProbabilityMeasure μ]
    {X e ε : Ω → ℝ} {α β : ℝ} (hX : MemLp X 2 μ) (he : MemLp e 2 μ) (hε : MemLp ε 2 μ)
    (hXe : cov[X, e; μ] = 0) (hXε : cov[X, ε; μ] = 0) (heε : cov[e, ε; μ] = 0) :
    cov[fun ω => X ω + e ω, fun ω => α + β * X ω + ε ω; μ] / Var[fun ω => X ω + e ω; μ] =
      attenuationFactor Var[X; μ] Var[e; μ] * β := by
  have hWmem : MemLp (fun ω => X ω + e ω) 2 μ := hX.add he
  have hβX : MemLp (fun ω => β * X ω) 2 μ := hX.const_mul β
  have hβXε_int : Integrable (fun ω => β * X ω + ε ω) μ := (hβX.add hε).integrable one_le_two
  have hα : (fun ω => α + β * X ω + ε ω) = fun ω => α + (β * X ω + ε ω) := by
    funext ω; ring
  have hcov0 : covariance (fun ω => X ω + e ω) (fun ω => α + β * X ω + ε ω) μ
      = covariance (fun ω => X ω + e ω) (fun ω => β * X ω + ε ω) μ := by
    rw [hα]
    exact covariance_const_add_right hβXε_int α
  have hcov1 : covariance (fun ω => X ω + e ω) (fun ω => β * X ω + ε ω) μ
      = covariance (fun ω => X ω + e ω) (fun ω => β * X ω) μ
        + covariance (fun ω => X ω + e ω) ε μ :=
    covariance_add_right (X := fun ω => X ω + e ω) (Y := fun ω => β * X ω)
      (Z := ε) hWmem hβX hε
  have hsmuleq : (fun ω => β * X ω) = β • X := by
    funext ω; exact (smul_eq_mul β (X ω)).symm
  have hcov2 : covariance (fun ω => X ω + e ω) (fun ω => β * X ω) μ
      = β * covariance (fun ω => X ω + e ω) X μ := by
    rw [hsmuleq]
    exact covariance_smul_right β
  have hcovWX : covariance (fun ω => X ω + e ω) X μ = variance X μ := by
    have h := covariance_add_left (X := X) (Y := e) (Z := X) hX he hX
    have hself : covariance X X μ = variance X μ :=
      covariance_self hX.aestronglyMeasurable.aemeasurable
    have hzero : covariance e X μ = 0 := by rw [covariance_comm]; exact hXe
    rw [hself, hzero, add_zero] at h
    exact h
  have hcovWε : covariance (fun ω => X ω + e ω) ε μ = 0 := by
    have h := covariance_add_left (X := X) (Y := e) (Z := ε) hX he hε
    rw [hXε, heε, add_zero] at h
    exact h
  have hVarW : variance (fun ω => X ω + e ω) μ = variance X μ + variance e μ := by
    rw [← covariance_self hWmem.aemeasurable]
    change cov[X + e, X + e; μ] = _
    rw [covariance_add_left hX he (hX.add he), covariance_add_right hX hX he,
      covariance_add_right he hX he, covariance_self hX.aemeasurable,
      covariance_self he.aemeasurable, covariance_comm e X, hXe]
    ring
  have hCov : covariance (fun ω => X ω + e ω) (fun ω => α + β * X ω + ε ω) μ
      = β * variance X μ := by
    rw [hcov0, hcov1, hcov2, hcovWX, hcovWε]
    ring
  rw [hCov, hVarW, attenuationFactor]
  ring

/-- **Population attenuation of the least-squares slope**: under the hypotheses of
`measurementError_population_attenuation_of_cov_eq_zero` and `Var[W] ≠ 0`, the population
least-squares slope of `Y = α + β X + ε` on `W = X + e` is `λ β`: it is the unique `b` for which
the residual `Y - b W` is uncorrelated with `W` (the population normal equation). Without
`Var[W] ≠ 0` every `b` solves the normal equation. -/
theorem measurementError_population_slope_of_cov_eq_zero [IsProbabilityMeasure μ]
    {X e ε : Ω → ℝ} {α β : ℝ} (hX : MemLp X 2 μ) (he : MemLp e 2 μ) (hε : MemLp ε 2 μ)
    (hXe : cov[X, e; μ] = 0) (hXε : cov[X, ε; μ] = 0) (heε : cov[e, ε; μ] = 0)
    (hW : Var[fun ω => X ω + e ω; μ] ≠ 0) (b : ℝ) :
    cov[fun ω => X ω + e ω, fun ω => α + β * X ω + ε ω - b * (X ω + e ω); μ] = 0 ↔
      b = attenuationFactor Var[X; μ] Var[e; μ] * β := by
  have hWmem : MemLp (fun ω => X ω + e ω) 2 μ := hX.add he
  have hYmem : MemLp (fun ω => α + β * X ω + ε ω) 2 μ :=
    ((memLp_const α).add (hX.const_mul β)).add hε
  have hbW : MemLp (fun ω => b * (X ω + e ω)) 2 μ := hWmem.const_mul b
  have hcovWY : cov[fun ω => X ω + e ω, fun ω => α + β * X ω + ε ω; μ] =
      attenuationFactor Var[X; μ] Var[e; μ] * β * Var[fun ω => X ω + e ω; μ] := by
    rw [← measurementError_population_attenuation_of_cov_eq_zero (α := α) (β := β) hX he hε
      hXe hXε heε, div_mul_cancel₀ _ hW]
  have hres : cov[fun ω => X ω + e ω, fun ω => α + β * X ω + ε ω - b * (X ω + e ω); μ] =
      (attenuationFactor Var[X; μ] Var[e; μ] * β - b) * Var[fun ω => X ω + e ω; μ] := by
    rw [show (fun ω => α + β * X ω + ε ω - b * (X ω + e ω)) =
        (fun ω => α + β * X ω + ε ω) - fun ω => b * (X ω + e ω) from rfl,
      covariance_sub_right hWmem hYmem hbW, covariance_const_mul_right,
      covariance_self hWmem.aemeasurable, hcovWY]
    ring
  rw [hres, mul_eq_zero, or_iff_left hW, sub_eq_zero, eq_comm]

set_option linter.unusedVariables false in
/-- **Population attenuation identity**, independence form: if `X`, `e` and `ε` are square
integrable and pairwise independent, then `cov[W, Y] / Var[W] = λ β` for `W = X + e` and
`Y = α + β X + ε` (`measurementError_population_attenuation_of_cov_eq_zero`, since independent
square-integrable variables are uncorrelated). The hypothesis `hW` is contract-required: it is
what makes the ratio the population least-squares slope
(`measurementError_population_slope_of_cov_eq_zero`), although the ratio identity holds without
it. -/
theorem measurementError_population_attenuation [IsProbabilityMeasure μ] {X e ε : Ω → ℝ}
    {α β : ℝ} (hX : MemLp X 2 μ) (he : MemLp e 2 μ) (hε : MemLp ε 2 μ)
    (hXe : IndepFun X e μ) (hXε : IndepFun X ε μ) (heε : IndepFun e ε μ)
    (hW : variance (fun ω => X ω + e ω) μ ≠ 0) :
    covariance (fun ω => X ω + e ω) (fun ω => α + β * X ω + ε ω) μ /
        variance (fun ω => X ω + e ω) μ =
      attenuationFactor (variance X μ) (variance e μ) * β :=
  measurementError_population_attenuation_of_cov_eq_zero hX he hε
    (hXe.covariance_eq_zero hX he) (hXε.covariance_eq_zero hX hε) (heε.covariance_eq_zero he hε)

/-! ### The classical errors-in-variables model -/

/-- **Classical errors-in-variables sampling hypotheses** for the latent regressor `ξ`, the
measurement error `u` and the equation error `ε` (observations `x i = ξ i + u i`,
`y i = β₀ + β ξ i + ε i`): the triples `(ξ i, u i, ε i)` are pairwise independent across `i` and
identically distributed, each coordinate is square integrable, and `ξ`, `u`, `ε` are pairwise
uncorrelated. Independence of `u` and `ε` from `ξ` and from each other implies the last three
fields; no mean-zero hypothesis is imposed. -/
structure ClassicalErrorsInVariables (μ : Measure Ω) (ξ u ε : ℕ → Ω → ℝ) : Prop where
  indepFun : Pairwise fun i j =>
    IndepFun (fun ω => (ξ i ω, u i ω, ε i ω)) (fun ω => (ξ j ω, u j ω, ε j ω)) μ
  identDistrib : ∀ i,
    IdentDistrib (fun ω => (ξ i ω, u i ω, ε i ω)) (fun ω => (ξ 0 ω, u 0 ω, ε 0 ω)) μ μ
  memLp_signal : MemLp (ξ 0) 2 μ
  memLp_measurementError : MemLp (u 0) 2 μ
  memLp_equationError : MemLp (ε 0) 2 μ
  cov_signal_measurementError : cov[ξ 0, u 0; μ] = 0
  cov_signal_equationError : cov[ξ 0, ε 0; μ] = 0
  cov_measurementError_equationError : cov[u 0, ε 0; μ] = 0

namespace ClassicalErrorsInVariables

variable {ξ u ε : ℕ → Ω → ℝ}

/-- Pairs `(φ (ξ i, u i, ε i))` built by a measurable map from the triples inherit the
hypotheses of the strong law. -/
private theorem indepFun_comp (h : ClassicalErrorsInVariables μ ξ u ε) {φ : ℝ × ℝ × ℝ → ℝ × ℝ}
    (hφ : Measurable φ) : Pairwise fun i j =>
      IndepFun (fun ω => φ (ξ i ω, u i ω, ε i ω)) (fun ω => φ (ξ j ω, u j ω, ε j ω)) μ :=
  fun _ _ hij => (h.indepFun hij).comp hφ hφ

private theorem identDistrib_comp (h : ClassicalErrorsInVariables μ ξ u ε)
    {φ : ℝ × ℝ × ℝ → ℝ × ℝ} (hφ : Measurable φ) (i : ℕ) :
    IdentDistrib (fun ω => φ (ξ i ω, u i ω, ε i ω)) (fun ω => φ (ξ 0 ω, u 0 ω, ε 0 ω)) μ μ :=
  (h.identDistrib i).comp hφ

/-- Almost surely, `S_xy / n → β σ_ξ²` and `S_xx / n → σ_ξ² + σ_u²` for the observed data. -/
theorem ae_tendsto_moments [IsProbabilityMeasure μ] (h : ClassicalErrorsInVariables μ ξ u ε)
    (β₀ β : ℝ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => sxy (fun i : Fin n => ξ i ω + u i ω)
        (fun i => β₀ + β * ξ i ω + ε i ω) / n) atTop (𝓝 (β * Var[ξ 0; μ])) ∧
      Tendsto (fun n : ℕ => sxy (fun i : Fin n => ξ i ω + u i ω)
        (fun i => ξ i ω + u i ω) / n) atTop (𝓝 (Var[ξ 0; μ] + Var[u 0; μ])) := by
  have hξ := h.memLp_signal
  have hu := h.memLp_measurementError
  have hε := h.memLp_equationError
  have hx : MemLp (fun ω => ξ 0 ω + u 0 ω) 2 μ := hξ.add hu
  have hβξ : MemLp (fun ω => β * ξ 0 ω) 2 μ := hξ.const_mul β
  have hy : MemLp (fun ω => β₀ + β * ξ 0 ω + ε 0 ω) 2 μ := ((memLp_const β₀).add hβξ).add hε
  have hφxy : Measurable fun p : ℝ × ℝ × ℝ => (p.1 + p.2.1, β₀ + β * p.1 + p.2.2) := by
    fun_prop
  have hφxx : Measurable fun p : ℝ × ℝ × ℝ => (p.1 + p.2.1, p.1 + p.2.1) := by fun_prop
  have hcxy : cov[fun ω => ξ 0 ω + u 0 ω, fun ω => β₀ + β * ξ 0 ω + ε 0 ω; μ] =
      β * Var[ξ 0; μ] := by
    have e : (fun ω => β₀ + β * ξ 0 ω + ε 0 ω) = fun ω => β₀ + (β * ξ 0 ω + ε 0 ω) := by
      funext ω; ring
    rw [e, covariance_const_add_right (Y := fun ω => β * ξ 0 ω + ε 0 ω)
      ((hβξ.add hε).integrable one_le_two)]
    change cov[ξ 0 + u 0, (fun ω => β * ξ 0 ω) + ε 0; μ] = _
    rw [covariance_add_left hξ hu (hβξ.add hε), covariance_add_right hξ hβξ hε,
      covariance_add_right hu hβξ hε, covariance_const_mul_right, covariance_const_mul_right,
      covariance_self hξ.aemeasurable, covariance_comm (u 0) (ξ 0),
      h.cov_signal_measurementError, h.cov_signal_equationError,
      h.cov_measurementError_equationError]
    ring
  have hcxx : cov[fun ω => ξ 0 ω + u 0 ω, fun ω => ξ 0 ω + u 0 ω; μ] =
      Var[ξ 0; μ] + Var[u 0; μ] := by
    change cov[ξ 0 + u 0, ξ 0 + u 0; μ] = _
    rw [covariance_add_left hξ hu (hξ.add hu), covariance_add_right hξ hξ hu,
      covariance_add_right hu hξ hu, covariance_self hξ.aemeasurable,
      covariance_self hu.aemeasurable, covariance_comm (u 0) (ξ 0),
      h.cov_signal_measurementError]
    ring
  filter_upwards [ae_tendsto_sxy_div (X := fun i ω => ξ i ω + u i ω)
      (Y := fun i ω => β₀ + β * ξ i ω + ε i ω) (h.indepFun_comp hφxy) (h.identDistrib_comp hφxy)
      hx hy,
    ae_tendsto_sxy_div (X := fun i ω => ξ i ω + u i ω) (Y := fun i ω => ξ i ω + u i ω)
      (h.indepFun_comp hφxx) (h.identDistrib_comp hφxx) hx hx] with ω h1 h2
  exact ⟨hcxy ▸ h1, hcxx ▸ h2⟩

end ClassicalErrorsInVariables

/-! ### Attenuation and consistency of the corrected slope -/

/-- Deterministic limit step: along any `φ → ∞`, if `S_xy / n → c`, `S_xx / n → v` and the
variance inputs `s k → σ` with `v ≠ σ`, then the corrected slopes converge to `c / (v - σ)`. -/
private theorem tendsto_correctedSlope_comp {x y : ℕ → ℝ} {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) {s : ℕ → ℝ} {c v σ : ℝ}
    (hxy : Tendsto (fun n : ℕ => sxy (fun i : Fin n => x i) (fun i => y i) / n) atTop (𝓝 c))
    (hxx : Tendsto (fun n : ℕ => sxy (fun i : Fin n => x i) (fun i => x i) / n) atTop (𝓝 v))
    (hs : Tendsto s atTop (𝓝 σ)) (hv : v - σ ≠ 0) :
    Tendsto (fun k => correctedSlope (fun i : Fin (φ k) => x i) (fun i => y i) (s k)) atTop
      (𝓝 (c / (v - σ))) := by
  refine ((hxy.comp hφ).div ((hxx.comp hφ).sub hs) hv).congr' ?_
  filter_upwards [hφ.eventually_ne_atTop 0] with k hk
  have hn : (φ k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  simp only [Pi.div_apply, Function.comp_apply, correctedSlope, Fintype.card_fin]
  rw [show sxy (fun i : Fin (φ k) => x i) (fun i => x i) / φ k - s k =
      (sxy (fun i : Fin (φ k) => x i) (fun i => x i) - φ k * s k) / φ k by field_simp,
    div_div_div_cancel_right₀ hn]

private theorem aemeasurable_sxy {X Y : ℕ → Ω → ℝ}
    (hX : ∀ i, AEMeasurable (X i) μ) (hY : ∀ i, AEMeasurable (Y i) μ) (n : ℕ) :
    AEMeasurable (fun ω => sxy (fun i : Fin n => X i ω) (fun i => Y i ω)) μ := by
  simp only [sxy, sampleMean_eq_sum_div]
  fun_prop

namespace ClassicalErrorsInVariables

variable {ξ u ε : ℕ → Ω → ℝ}

/-- The corrected slope of the observed data, with a measurable variance input, is
a.e.-measurable. -/
theorem aemeasurable_correctedSlope (h : ClassicalErrorsInVariables μ ξ u ε) (β₀ β : ℝ)
    {s : Ω → ℝ} (hs : AEMeasurable s μ) (n : ℕ) :
    AEMeasurable (fun ω => correctedSlope (fun i : Fin n => ξ i ω + u i ω)
      (fun i => β₀ + β * ξ i ω + ε i ω) (s ω)) μ := by
  have hξ : ∀ i, AEMeasurable (ξ i) μ := fun i => (h.identDistrib i).aemeasurable_fst.fst
  have hu : ∀ i, AEMeasurable (u i) μ := fun i => (h.identDistrib i).aemeasurable_fst.snd.fst
  have hε : ∀ i, AEMeasurable (ε i) μ := fun i => (h.identDistrib i).aemeasurable_fst.snd.snd
  have hx : ∀ i, AEMeasurable (fun ω => ξ i ω + u i ω) μ := fun i => (hξ i).add (hu i)
  have hy : ∀ i, AEMeasurable (fun ω => β₀ + β * ξ i ω + ε i ω) μ := fun i =>
    (aemeasurable_const.add ((hξ i).const_mul β)).add (hε i)
  simp only [correctedSlope]
  exact (aemeasurable_sxy hx hy n).div ((aemeasurable_sxy hx hx n).sub (hs.const_mul _))

/-- **Attenuation bias of the naive OLS slope**, almost sure form: in the classical
errors-in-variables model with `σ_ξ² + σ_u² > 0`, the least-squares slope of
`y i = β₀ + β ξ i + ε i` on the mismeasured regressor `x i = ξ i + u i` converges almost surely to
`λ β`, where `λ = σ_ξ² / (σ_ξ² + σ_u²)` is the attenuation factor. -/
theorem ae_tendsto_olsSlope_attenuation [IsProbabilityMeasure μ]
    (h : ClassicalErrorsInVariables μ ξ u ε) (β₀ β : ℝ)
    (hvar : 0 < Var[ξ 0; μ] + Var[u 0; μ]) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => olsSlope (fun i : Fin n => ξ i ω + u i ω)
      (fun i => β₀ + β * ξ i ω + ε i ω)) atTop
      (𝓝 (attenuationFactor Var[ξ 0; μ] Var[u 0; μ] * β)) := by
  filter_upwards [h.ae_tendsto_moments β₀ β] with ω hm
  have hlim := tendsto_correctedSlope_comp (x := fun i => ξ i ω + u i ω)
    (y := fun i => β₀ + β * ξ i ω + ε i ω) tendsto_id hm.1 hm.2 tendsto_const_nhds
    (σ := 0) (by rw [sub_zero]; exact hvar.ne')
  simp only [id, correctedSlope_zero] at hlim
  convert hlim using 2
  rw [attenuationFactor, sub_zero]
  ring

/-- **Attenuation bias of the naive OLS slope**, in probability: `plim β̂_OLS = λ β` with
`λ = σ_ξ² / (σ_ξ² + σ_u²)`. -/
theorem tendstoInMeasure_olsSlope_attenuation [IsProbabilityMeasure μ]
    (h : ClassicalErrorsInVariables μ ξ u ε) (β₀ β : ℝ)
    (hvar : 0 < Var[ξ 0; μ] + Var[u 0; μ]) :
    TendstoInMeasure μ (fun (n : ℕ) ω => olsSlope (fun i : Fin n => ξ i ω + u i ω)
      (fun i => β₀ + β * ξ i ω + ε i ω)) atTop
      (fun _ => attenuationFactor Var[ξ 0; μ] Var[u 0; μ] * β) := by
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) (h.ae_tendsto_olsSlope_attenuation β₀ β hvar)
  simp_rw [← correctedSlope_zero]
  exact (h.aemeasurable_correctedSlope β₀ β aemeasurable_const n).aestronglyMeasurable

/-- **Consistency of the corrected slope with an a.s. consistent variance estimate**: if
`σ_ξ² ≠ 0` and `σuHat n → σ_u²` almost surely, then
`correctedSlope x y (σuHat n) = S_xy / (S_xx - n σuHat n) → β` almost surely. -/
theorem ae_tendsto_correctedSlope_of_ae_tendsto [IsProbabilityMeasure μ]
    (h : ClassicalErrorsInVariables μ ξ u ε) (β₀ β : ℝ) (hvar : Var[ξ 0; μ] ≠ 0)
    {σuHat : ℕ → Ω → ℝ} (hσuHat : ∀ᵐ ω ∂μ, Tendsto (fun n => σuHat n ω) atTop (𝓝 Var[u 0; μ])) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => correctedSlope (fun i : Fin n => ξ i ω + u i ω)
      (fun i => β₀ + β * ξ i ω + ε i ω) (σuHat n ω)) atTop (𝓝 β) := by
  filter_upwards [h.ae_tendsto_moments β₀ β, hσuHat] with ω hm hs
  have hlim := tendsto_correctedSlope_comp (x := fun i => ξ i ω + u i ω)
    (y := fun i => β₀ + β * ξ i ω + ε i ω) tendsto_id hm.1 hm.2 hs
    (by rwa [add_sub_cancel_right])
  rw [add_sub_cancel_right, mul_div_cancel_right₀ _ hvar] at hlim
  exact hlim

/-- **Consistency of the corrected slope with known measurement-error variance**: if
`σ_ξ² ≠ 0`, then `S_xy / (S_xx - n σ_u²) → β` almost surely. -/
theorem ae_tendsto_correctedSlope [IsProbabilityMeasure μ]
    (h : ClassicalErrorsInVariables μ ξ u ε) (β₀ β : ℝ) (hvar : Var[ξ 0; μ] ≠ 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => correctedSlope (fun i : Fin n => ξ i ω + u i ω)
      (fun i => β₀ + β * ξ i ω + ε i ω) Var[u 0; μ]) atTop (𝓝 β) :=
  h.ae_tendsto_correctedSlope_of_ae_tendsto β₀ β hvar (σuHat := fun _ _ => Var[u 0; μ])
    (ae_of_all _ fun _ => tendsto_const_nhds)

/-- **Consistency of the corrected slope with a variance estimate consistent in probability**:
if `σ_ξ² ≠ 0` and the a.e.-measurable estimates `σuHat n` converge in probability to `σ_u²`, then
`S_xy / (S_xx - n σuHat n)` converges in probability to `β`. -/
theorem tendstoInMeasure_correctedSlope [IsProbabilityMeasure μ]
    (h : ClassicalErrorsInVariables μ ξ u ε) (β₀ β : ℝ) (hvar : Var[ξ 0; μ] ≠ 0)
    {σuHat : ℕ → Ω → ℝ} (hσuHatm : ∀ n, AEStronglyMeasurable (σuHat n) μ)
    (hσuHat : TendstoInMeasure μ σuHat atTop fun _ => Var[u 0; μ]) :
    TendstoInMeasure μ (fun (n : ℕ) ω => correctedSlope (fun i : Fin n => ξ i ω + u i ω)
      (fun i => β₀ + β * ξ i ω + ε i ω) (σuHat n ω)) atTop (fun _ => β) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff fun n =>
    (h.aemeasurable_correctedSlope β₀ β (hσuHatm n).aemeasurable n).aestronglyMeasurable]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (exists_seq_tendstoInMeasure_atTop_iff hσuHatm).1 hσuHat ns hns
  refine ⟨ns', hns', ?_⟩
  filter_upwards [h.ae_tendsto_moments β₀ β, hae] with ω hm hs
  have hlim := tendsto_correctedSlope_comp (x := fun i => ξ i ω + u i ω)
    (y := fun i => β₀ + β * ξ i ω + ε i ω) (hns.comp hns').tendsto_atTop hm.1 hm.2 hs
    (by rwa [add_sub_cancel_right])
  rw [add_sub_cancel_right, mul_div_cancel_right₀ _ hvar] at hlim
  exact hlim

end ClassicalErrorsInVariables

end MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables
