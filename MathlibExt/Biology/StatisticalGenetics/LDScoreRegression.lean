/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
public import MathlibExt.Probability.FiniteProbability
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Moments.Variance

/-!
# LD-score regression: the regression identity and the heritability estimator

Bulik-Sullivan et al. (2015) regress the association statistics `χ²_j` of `M` markers on their
LD scores `ℓ_j` and read the SNP heritability off the slope. Their regression equation is

  `𝔼[χ²_j] = N h² ℓ_j / M + N a + 1`,

with `N` the sample size and `N a` a confounding term (for example population stratification),
and the estimator is `ĥ² = slope · M / N`.

## The regression identity

The model is `LDScore.Model` with the stratification shift of `LDScoreInflation`
(`y = X β + ε + s c`), for a probability measure, mean-zero effects and noise, a standardized
genotype matrix, and a stratification term `s² (X_jᵀ c / N)² = a` common to all markers. Under
these assumptions the exact identity (`integral_chiSqStrat_eq`) is

  `𝔼[χ²_j] = 1 + N h² ℓ_j / M + N a - h²`.

It differs from the paper's equation by `-h²`: the residual variance of the model is `1 - h²`,
not `1` (see `LDScore`). The paper's equation holds exactly iff `h² = 0`
(`integral_chiSqStrat_eq_paper_iff`). The slope `N h² / M` is the paper's in every case, and the
`-h²` only moves the intercept, so the heritability estimator below is not affected by it.

## The estimator

`h2Hat N M ℓ χ = olsSlope ℓ χ * M / N` is the paper's estimator: the least-squares slope
(`FiniteProbability.olsSlope`) of the statistics on the LD scores, rescaled by `M / N`. Results:

* `h2Hat_affine`: if the statistics are exactly affine in the LD scores with slope `N h² / M`
  and the LD scores are not all equal (`sxy ℓ ℓ ≠ 0`), then `h2Hat` returns `h²`, whatever the
  intercept.
* `h2Hat_integral_chiSqStrat` (population version): `h2Hat` applied to the expected statistics
  returns `h²`, with or without confounding.
* `integral_h2Hat_chiSqStrat` (unbiasedness): `𝔼[ĥ²] = h²`. The least-squares slope is linear
  in the responses (`sxy_eq_sum_sub_mul`), so expectation commutes with it
  (`integral_olsSlope`).
* `integral_olsIntercept_chiSqStrat`: the least-squares intercept is unbiased for the exact
  intercept `1 - h² + N a`, so confounding moves the intercept, not the slope.
* `tendstoInMeasure_h2Hat` (consistency): along any sequence of designs and models with the
  same `h²` whose estimators have variance tending to `0`, `ĥ²` converges in probability to
  `h²` (Chebyshev, `tendstoInMeasure_of_integral_eq_of_evariance`).

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
  MathlibExt.Probability.FiniteProbability

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

/-! ### Least squares is linear in the responses -/

/-- `S_xy = ∑ i, (x i - x̄) * y i`: the centred cross product is linear in `y`. -/
theorem sxy_eq_sum_sub_mul {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    sxy x y = ∑ i, (x i - sampleMean x) * y i := by
  have h : ∀ i, (x i - sampleMean x) * (y i - sampleMean y) =
      (x i - sampleMean x) * y i - (x i - sampleMean x) * sampleMean y := fun i => by ring
  rw [sxy]
  simp only [h]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_sub_sampleMean, zero_mul, sub_zero]

/-- The least-squares slope of exactly affine responses `b₀ + b₁ x` is `b₁` when `S_xx ≠ 0`. -/
theorem olsSlope_affine {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : sxy x x ≠ 0) (b₀ b₁ : ℝ) :
    olsSlope x (fun i => b₀ + b₁ * x i) = b₁ := by
  rw [olsSlope, eq_comm, eq_div_iff hx, sxy_eq_sum_sub_mul, sxy_eq_sum_sub_mul]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_sub_sampleMean, zero_mul,
    zero_add, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The sample mean is affine: the mean of `b₀ + b₁ x` is `b₀ + b₁ x̄` (for nonempty index). -/
theorem sampleMean_affine {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (b₀ b₁ : ℝ) :
    sampleMean (fun i => b₀ + b₁ * x i) = b₀ + b₁ * sampleMean x := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [sampleMean_eq_sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The least-squares intercept of exactly affine responses `b₀ + b₁ x` is `b₀` when
`S_xx ≠ 0`. -/
theorem olsIntercept_affine {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : sxy x x ≠ 0) (b₀ b₁ : ℝ) :
    olsIntercept x (fun i => b₀ + b₁ * x i) = b₀ := by
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hx (by simp [sxy])
  rw [olsIntercept, olsSlope_affine hx, sampleMean_affine]
  ring

/-- The least-squares slope of integrable responses is integrable. -/
theorem integrable_olsSlope {ι : Type*} [Fintype ι] (x : ι → ℝ) {Y : ι → Ω → ℝ}
    (hY : ∀ i, Integrable (Y i) μ) : Integrable (fun ω => olsSlope x fun i => Y i ω) μ := by
  simp only [olsSlope, sxy_eq_sum_sub_mul]
  exact (integrable_finsetSum _ fun i _ => (hY i).const_mul _).div_const _

/-- Expectation commutes with the least-squares slope: for integrable responses `Y i`,
`𝔼[b̂(x, Y)] = b̂(x, 𝔼 Y)`. -/
theorem integral_olsSlope {ι : Type*} [Fintype ι] (x : ι → ℝ) {Y : ι → Ω → ℝ}
    (hY : ∀ i, Integrable (Y i) μ) :
    ∫ ω, olsSlope x (fun i => Y i ω) ∂μ = olsSlope x fun i => ∫ ω, Y i ω ∂μ := by
  simp only [olsSlope, sxy_eq_sum_sub_mul]
  rw [integral_div, integral_finsetSum _ fun i _ => (hY i).const_mul _]
  simp_rw [integral_const_mul]

/-- Expectation commutes with the least-squares intercept, for a probability measure and
integrable responses. -/
theorem integral_olsIntercept [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] (x : ι → ℝ)
    {Y : ι → Ω → ℝ} (hY : ∀ i, Integrable (Y i) μ) :
    ∫ ω, olsIntercept x (fun i => Y i ω) ∂μ = olsIntercept x fun i => ∫ ω, Y i ω ∂μ := by
  have hm : Integrable (fun ω => sampleMean fun i => Y i ω) μ := by
    simp only [sampleMean_eq_sum_div]
    exact (integrable_finsetSum _ fun i _ => hY i).div_const _
  simp only [olsIntercept]
  rw [integral_sub hm ((integrable_olsSlope x hY).mul_const _), integral_mul_const,
    integral_olsSlope x hY]
  simp only [sampleMean_eq_sum_div]
  rw [integral_div, integral_finsetSum _ fun i _ => hY i]

/-! ### The heritability estimator -/

/-- The **LD-score regression heritability estimator** `ĥ² = b̂ · M / N` of Bulik-Sullivan et al.
(2015), where `b̂` is the least-squares slope of the statistics `χ` on the LD scores `ℓ` of the
`M` markers and `N` is the sample size. (Lean's `x / 0 = 0` makes it `0` when `N = 0`, and
`olsSlope` is `0` when the LD scores are all equal, where the slope is not identified.) -/
noncomputable def h2Hat (N M : ℕ) (ℓ χ : Fin M → ℝ) : ℝ := olsSlope ℓ χ * M / N

/-- If the statistics are exactly affine in the LD scores with slope `N h² / M`, then
`ĥ² = h²` whatever the intercept, provided `N, M ≠ 0` and the LD scores are not all equal. -/
theorem h2Hat_affine (hN : N ≠ 0) (hM : M ≠ 0) {ℓ : Fin M → ℝ} (hℓ : sxy ℓ ℓ ≠ 0)
    (h2 b₀ : ℝ) : h2Hat N M ℓ (fun j => b₀ + N * h2 / M * ℓ j) = h2 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  rw [h2Hat, olsSlope_affine hℓ]
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
`h2Hat_affine` and `olsIntercept_affine`. -/
private theorem integral_chiSqStrat_fun [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    (fun j => ∫ ω, chiSqStrat D X s c j ω ∂μ) =
      fun j => (1 - D.h2 + N * a) + N * D.h2 / M * ldScore X j := by
  funext j
  rw [integral_chiSqStrat_of_const D X hN hX hβ hε s c ha, add_comm]

/-- **Population consistency of the estimator.** Applied to the expected statistics, the
LD-score regression estimator returns the heritability exactly, with or without a
confounding term `N a`, provided `N, M ≠ 0` and the LD scores are not all equal. -/
theorem h2Hat_integral_chiSqStrat [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hℓ : sxy (ldScore X) (ldScore X) ≠ 0)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    h2Hat N M (ldScore X) (fun j => ∫ ω, chiSqStrat D X s c j ω ∂μ) = D.h2 := by
  rw [integral_chiSqStrat_fun D X hN hX hβ hε s c ha]
  exact h2Hat_affine hN hM hℓ D.h2 _

/-- **Unbiasedness of the LD-score regression estimator.** For a probability measure, mean-zero
effects and noise, a standardized genotype matrix with LD scores not all equal, `N, M ≠ 0`, and
a confounding term common to all markers, `𝔼[ĥ²] = h²`. -/
theorem integral_h2Hat_chiSqStrat [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hℓ : sxy (ldScore X) (ldScore X) ≠ 0)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    ∫ ω, h2Hat N M (ldScore X) (fun j => chiSqStrat D X s c j ω) ∂μ = D.h2 := by
  simp only [h2Hat]
  rw [integral_div, integral_mul_const,
    integral_olsSlope _ fun j => integrable_chiSqStrat D X s c j]
  exact h2Hat_integral_chiSqStrat D X hN hM hX hℓ hβ hε s c ha

/-- The LD-score regression estimator is integrable under the model. -/
theorem integrable_h2Hat_chiSqStrat [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (s : ℝ) (c : Fin N → ℝ) :
    Integrable (fun ω => h2Hat N M (ldScore X) fun j => chiSqStrat D X s c j ω) μ :=
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

/-! ### Consistency -/

/-- **Chebyshev consistency.** Estimators `T n` with constant mean `θ` and variance tending to
`0` converge to `θ` in measure. -/
theorem tendstoInMeasure_of_integral_eq_of_evariance {ι : Type*} {l : Filter ι}
    {T : ι → Ω → ℝ} {θ : ℝ} (hT : ∀ n, AEStronglyMeasurable (T n) μ)
    (hmean : ∀ n, ∫ ω, T n ω ∂μ = θ) (hvar : Tendsto (fun n => evariance (T n) μ) l (𝓝 0)) :
    TendstoInMeasure μ T l fun _ => θ := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set c : NNReal := ⟨ε, hε.le⟩
  have hc : c ≠ 0 := by
    intro h
    have : (c : ℝ) = 0 := by rw [h]; rfl
    exact hε.ne' this
  have hbound : ∀ n, μ {ω | ε ≤ dist (T n ω) θ} ≤ evariance (T n) μ / (c : ENNReal) ^ 2 := by
    intro n
    have h := meas_ge_le_evariance_div_sq (hT n) hc
    rwa [hmean n] at h
  have hlim : Tendsto (fun n => evariance (T n) μ / (c : ENNReal) ^ 2) l (𝓝 0) := by
    have hc2 : (c : ENNReal) ^ 2 ≠ 0 := pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hc)
    have h := ENNReal.Tendsto.div_const hvar (Or.inr hc2)
    rwa [ENNReal.zero_div] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) hbound

/-- **Consistency of the LD-score regression estimator.** Along a sequence of designs (sample
sizes `N n`, marker counts `M n`, standardized genotype matrices `X n` with LD scores not all
equal) and models `D n` with common heritability `h²`, mean-zero effects and noise, and
confounding terms common to the markers of each design, if the variance of `ĥ²` tends to `0`,
then `ĥ²` converges to `h²` in probability. The model fixes only second moments, so the
vanishing variance is a hypothesis rather than a consequence. -/
theorem tendstoInMeasure_h2Hat [IsProbabilityMeasure μ] {ι : Type*} {l : Filter ι}
    {N M : ι → ℕ} (D : ∀ n, Model μ (N n) (M n)) (X : ∀ n, Matrix (Fin (N n)) (Fin (M n)) ℝ)
    {h2 : ℝ} (hh2 : ∀ n, (D n).h2 = h2) (hN : ∀ n, N n ≠ 0) (hM : ∀ n, M n ≠ 0)
    (hX : ∀ n, IsStandardized (X n)) (hℓ : ∀ n, sxy (ldScore (X n)) (ldScore (X n)) ≠ 0)
    (hβ : ∀ n k, ∫ ω, (D n).beta k ω ∂μ = 0) (hε : ∀ n i, ∫ ω, (D n).eps i ω ∂μ = 0)
    (s : ι → ℝ) (c : ∀ n, Fin (N n) → ℝ) (a : ι → ℝ)
    (ha : ∀ n j, s n ^ 2 * ((∑ i, X n i j * c n i) / N n) ^ 2 = a n)
    (hvar : Tendsto (fun n => evariance (fun ω =>
      h2Hat (N n) (M n) (ldScore (X n)) fun j => chiSqStrat (D n) (X n) (s n) (c n) j ω) μ)
      l (𝓝 0)) :
    TendstoInMeasure μ (fun n ω =>
      h2Hat (N n) (M n) (ldScore (X n)) fun j => chiSqStrat (D n) (X n) (s n) (c n) j ω)
      l fun _ => h2 :=
  tendstoInMeasure_of_integral_eq_of_evariance
    (fun n => (integrable_h2Hat_chiSqStrat (D n) (X n) (s n) (c n)).aestronglyMeasurable)
    (fun n => by
      rw [integral_h2Hat_chiSqStrat (D n) (X n) (hN n) (hM n) (hX n) (hℓ n) (hβ n) (hε n) (s n)
        (c n) (ha n), hh2 n])
    hvar

end MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
