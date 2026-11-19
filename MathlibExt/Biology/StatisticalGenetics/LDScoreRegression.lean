/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
public import MathlibExt.Probability.FiniteProbability
public import MathlibExt.Probability.ConvergenceInProbability
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Moments.Variance

/-!
# LD-score regression: the regression identity and an unweighted heritability estimator

Bulik-Sullivan et al. (2015) regress the association statistics `χ²_j` of `M` markers on their
LD scores `ℓ_j` and read the SNP heritability off the slope. Their regression equation is

  `𝔼[χ²_j] = N h² ℓ_j / M + N a + 1`,

with `N` the sample size and `N a` a confounding term (for example population stratification),
and the estimator is `ĥ² = slope · M / N`, with the slope fitted by weighted least squares
(heteroscedasticity and LD weights).

## The regression identity

The model is `LDScore.Model` with the stratification shift of `LDScoreInflation`
(`y = X β + ε + s c`), for a probability measure, mean-zero effects and noise, a standardized
genotype matrix, and a stratification term `s² (X_jᵀ c / N)² = a` common to all markers. Under
these assumptions the exact identity (`integral_chiSqStrat_eq`) is

  `𝔼[χ²_j] = 1 + N h² ℓ_j / M + N a - h²`.

It differs from the paper's equation by `-h²`: the residual variance of the model is `1 - h²`,
not `1` (see `LDScore`). The paper's equation holds exactly iff `h² = 0`
(`integral_chiSqStrat_eq_paper_iff`). The slope `N h² / M` is the paper's in every case, and the
`-h²` only moves the intercept, so the unweighted estimator below is not affected by it.

## The estimator

`olsH2Hat N M ℓ χ = olsSlope ℓ χ * M / N` is an unweighted analogue of the paper's estimator: the
ordinary (unweighted) least-squares slope (`FiniteProbability.olsSlope`) of the statistics on the
LD scores, rescaled by `M / N`. The paper's slope is a weighted least-squares fit, and for finite
samples the two slopes generally differ, so the results below are about this unweighted
estimator, not the paper's. Results:

* `olsH2Hat_affine`: if the statistics are exactly affine in the LD scores with slope `N h² / M`
  and the LD scores are not all equal (`sxy ℓ ℓ ≠ 0`), then `olsH2Hat` returns `h²`, whatever the
  intercept.
* `olsH2Hat_integral_chiSqStrat` (population version): `olsH2Hat` applied to the expected statistics
  returns `h²`, with or without confounding.
* `integral_olsH2Hat_chiSqStrat` (unbiasedness): `𝔼[ĥ²] = h²`. The least-squares slope is linear
  in the responses (`FiniteProbability.sxy_eq_sum_sub_mul`), so expectation commutes with it
  (`FiniteProbability.integral_olsSlope`).
* `integral_olsIntercept_chiSqStrat`: the least-squares intercept is unbiased for the exact
  intercept `1 - h² + N a`, so confounding moves the intercept, not the slope.
* `tendstoInMeasure_olsH2Hat` (consistency): along any sequence of designs and models with the
  same `h²` whose estimators have variance tending to `0`, `ĥ²` converges in probability to
  `h²` (Chebyshev, `ConvergenceInProbability.tendstoInMeasure_of_integral_eq_of_evariance`).

## What is assumed rather than derived

The model specifies only second moments of effects and noise, so the variance of `χ²_j` (a
fourth moment) and hence of `ĥ²` is not determined by it. Consistency therefore takes vanishing
estimator variance as a hypothesis; deriving it from an asymptotic regime (`M → ∞` with bounded
LD and independent effects) is not done here. The paper fits by weighted least squares with
heteroscedasticity and LD weights; this file treats the unweighted fit.

## References

* B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working
  Group of the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price,
  B. M. Neale, *LD Score regression distinguishes confounding from polygenicity in
  genome-wide association studies*, Nat. Genet. 47 (2015), 291–295.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
  MathlibExt.Probability.FiniteProbability MathlibExt.Probability.ConvergenceInProbability

namespace MathlibExt.Biology.StatisticalGenetics.LDScoreRegression

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {N M : ℕ}

/-! ### The regression identity -/

/-- **LD-score regression identity** (exact form). For a probability measure, mean-zero effects
and noise, a standardized genotype matrix, `N ≠ 0`, and a stratification term
`s² (X_jᵀ c / N)² = a` common to all markers,
`𝔼[χ²_j] = 1 + N h² ℓ_j / M + N a - h²`: affine in the LD score with slope `N h² / M` and
intercept `1 + N a - h²`. -/
theorem integral_chiSqStrat_eq [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) (j : Fin M) :
    ∫ ω, chiSqStrat D X s c j ω ∂μ = 1 + N * D.h2 * ldScore X j / M + N * a - D.h2 := by
  rw [integral_chiSqStrat_of_const D X hN hX hβ hε s c ha]
  ring

/-- The paper's form `𝔼[χ²_j] = 1 + N h² ℓ_j / M + N a` of the regression equation holds
exactly iff `h² = 0`; otherwise it is off by `-h²`. -/
theorem integral_chiSqStrat_eq_paper_iff [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) (j : Fin M) :
    ∫ ω, chiSqStrat D X s c j ω ∂μ = 1 + N * D.h2 * ldScore X j / M + N * a ↔ D.h2 = 0 := by
  rw [integral_chiSqStrat_eq D X hN hX hβ hε s c ha]
  constructor <;> intro h <;> linarith

/-! ### The heritability estimator -/

/-- The **unweighted LD-score regression heritability estimator** `ĥ² = b̂ · M / N`, where `b̂` is
the ordinary (unweighted) least-squares slope of the statistics `χ` on the LD scores `ℓ` of the
`M` markers and `N` is the sample size. It is an unweighted analogue of the estimator of
Bulik-Sullivan et al. (2015), who fit the slope by weighted least squares; for finite samples the
two slopes generally differ. (Lean's `x / 0 = 0` makes it `0` when `N = 0`, and `olsSlope` is `0`
when the LD scores are all equal, where the slope is not identified.) -/
noncomputable def olsH2Hat (N M : ℕ) (ℓ χ : Fin M → ℝ) : ℝ := olsSlope ℓ χ * M / N

/-- If the statistics are exactly affine in the LD scores with slope `N h² / M`, then
`ĥ² = h²` whatever the intercept, provided `N, M ≠ 0` and the LD scores are not all equal. -/
theorem olsH2Hat_affine (hN : N ≠ 0) (hM : M ≠ 0) {ℓ : Fin M → ℝ} (hℓ : sxy ℓ ℓ ≠ 0)
    (h2 b₀ : ℝ) : olsH2Hat N M ℓ (fun j => b₀ + N * h2 / M * ℓ j) = h2 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  rw [olsH2Hat, olsSlope_affine hℓ]
  field_simp

/-- Under the model with stratification, the statistic `χ²_j` is integrable. -/
theorem integrable_chiSqStrat [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (s : ℝ) (c : Fin N → ℝ) (j : Fin M) :
    Integrable (chiSqStrat D X s c j) μ := by
  have hp : ∀ i, MemLp (phenoStrat D X s c i) 2 μ := fun i =>
    ((memLp_finsetSum Finset.univ fun k _ => (D.memLp_beta k).const_mul (X i k)).add
      (D.memLp_eps i)).add (memLp_const (s * c i))
  have hb : MemLp (betaHatStrat D X s c j) 2 μ := by
    have e : betaHatStrat D X s c j =
        fun ω => (N : ℝ)⁻¹ * ∑ i, X i j * phenoStrat D X s c i ω := by
      funext ω
      rw [betaHatStrat, div_eq_inv_mul]
    rw [e]
    exact (memLp_finsetSum Finset.univ fun i _ => (hp i).const_mul (X i j)).const_mul _
  exact hb.integrable_sq.const_mul (N : ℝ)

/-- The expected statistics as an affine function of the LD scores, in the form used by
`olsH2Hat_affine` and `olsIntercept_affine`. -/
private theorem integral_chiSqStrat_fun [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    (fun j => ∫ ω, chiSqStrat D X s c j ω ∂μ) =
      fun j => (1 - D.h2 + N * a) + N * D.h2 / M * ldScore X j := by
  funext j
  rw [integral_chiSqStrat_of_const D X hN hX hβ hε s c ha, add_comm]

/-- **Population consistency of the unweighted estimator.** Applied to the expected statistics,
the unweighted LD-score regression estimator returns the heritability exactly, with or without a
confounding term `N a`, provided `N, M ≠ 0` and the LD scores are not all equal. -/
theorem olsH2Hat_integral_chiSqStrat [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hℓ : sxy (ldScore X) (ldScore X) ≠ 0)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    olsH2Hat N M (ldScore X) (fun j => ∫ ω, chiSqStrat D X s c j ω ∂μ) = D.h2 := by
  rw [integral_chiSqStrat_fun D X hN hX hβ hε s c ha]
  exact olsH2Hat_affine hN hM hℓ D.h2 _

/-- **Unbiasedness of the unweighted LD-score regression estimator.** For a probability measure,
mean-zero effects and noise, a standardized genotype matrix with LD scores not all equal,
`N, M ≠ 0`, and a confounding term common to all markers, `𝔼[ĥ²] = h²`. -/
theorem integral_olsH2Hat_chiSqStrat [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hℓ : sxy (ldScore X) (ldScore X) ≠ 0)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    ∫ ω, olsH2Hat N M (ldScore X) (fun j => chiSqStrat D X s c j ω) ∂μ = D.h2 := by
  simp only [olsH2Hat]
  rw [integral_div, integral_mul_const,
    integral_olsSlope _ fun j => integrable_chiSqStrat D X s c j]
  exact olsH2Hat_integral_chiSqStrat D X hN hM hX hℓ hβ hε s c ha

/-- The unweighted LD-score regression estimator is integrable under the model. -/
theorem integrable_olsH2Hat_chiSqStrat [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (s : ℝ) (c : Fin N → ℝ) :
    Integrable (fun ω => olsH2Hat N M (ldScore X) fun j => chiSqStrat D X s c j ω) μ :=
  ((integrable_olsSlope _ fun j => integrable_chiSqStrat D X s c j).mul_const _).div_const _

/-- **The intercept measures confounding.** Under the same assumptions, the least-squares
intercept of the statistics on the LD scores is unbiased for the exact intercept
`1 - h² + N a`: confounding enters the intercept, not the slope. -/
theorem integral_olsIntercept_chiSqStrat [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hX : IsStandardized X)
    (hℓ : sxy (ldScore X) (ldScore X) ≠ 0)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    ∫ ω, olsIntercept (ldScore X) (fun j => chiSqStrat D X s c j ω) ∂μ = 1 - D.h2 + N * a := by
  rw [integral_olsIntercept _ fun j => integrable_chiSqStrat D X s c j,
    integral_chiSqStrat_fun D X hN hX hβ hε s c ha, olsIntercept_affine hℓ]

/-- **Consistency of the unweighted LD-score regression estimator.** Along a sequence of designs
(sample sizes `N n`, marker counts `M n`, standardized genotype matrices `X n` with LD scores not
all equal) and models `D n` with common heritability `h²`, mean-zero effects and noise, and
confounding terms common to the markers of each design, if the variance of `ĥ²` tends to `0`,
then `ĥ²` converges to `h²` in probability. The model fixes only second moments, so the
vanishing variance is a hypothesis rather than a consequence. -/
theorem tendstoInMeasure_olsH2Hat [IsProbabilityMeasure μ] {ι : Type*} {l : Filter ι}
    {N M : ι → ℕ} (D : ∀ n, Model μ (N n) (M n)) (X : ∀ n, Matrix (Fin (N n)) (Fin (M n)) ℝ)
    {h2 : ℝ} (hh2 : ∀ n, (D n).h2 = h2) (hN : ∀ n, N n ≠ 0) (hM : ∀ n, M n ≠ 0)
    (hX : ∀ n, IsStandardized (X n)) (hℓ : ∀ n, sxy (ldScore (X n)) (ldScore (X n)) ≠ 0)
    (hβ : ∀ n k, ∫ ω, (D n).beta k ω ∂μ = 0) (hε : ∀ n i, ∫ ω, (D n).eps i ω ∂μ = 0)
    (s : ι → ℝ) (c : ∀ n, Fin (N n) → ℝ) (a : ι → ℝ)
    (ha : ∀ n j, s n ^ 2 * ((∑ i, X n i j * c n i) / N n) ^ 2 = a n)
    (hvar : Tendsto (fun n => evariance (fun ω =>
      olsH2Hat (N n) (M n) (ldScore (X n)) fun j => chiSqStrat (D n) (X n) (s n) (c n) j ω) μ)
      l (𝓝 0)) :
    TendstoInMeasure μ (fun n ω =>
      olsH2Hat (N n) (M n) (ldScore (X n)) fun j => chiSqStrat (D n) (X n) (s n) (c n) j ω)
      l fun _ => h2 :=
  tendstoInMeasure_of_integral_eq_of_evariance
    (fun n => (integrable_olsH2Hat_chiSqStrat (D n) (X n) (s n) (c n)).aestronglyMeasurable)
    (fun n => by
      rw [integral_olsH2Hat_chiSqStrat (D n) (X n) (hN n) (hM n) (hX n) (hℓ n) (hβ n) (hε n) (s n)
        (c n) (ha n), hh2 n])
    hvar

end MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
