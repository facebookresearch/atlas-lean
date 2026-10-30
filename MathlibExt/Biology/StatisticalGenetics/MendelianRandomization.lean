/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Integration

/-!
# Mendelian randomization and instrumental-variable identification

Mendelian randomization (Davey Smith & Ebrahim 2003) uses genetic variants as instrumental
variables: a variant `Z` that shifts an exposure `X`, is independent of the confounders of the
exposure–outcome relation, and affects the outcome `Y` only through `X` identifies the causal
effect of `X` on `Y`. This file proves the identification results behind the standard
estimators.

* **Wald ratio**, named after the grouping estimator of Wald (1940), which is this ratio for a
  two-valued grouping variable. In the linear structural model `Y = α + β X + U`, where the
  error `U` collects every other cause of `Y` (confounders of `X` and `Y` included) and the
  instrument enters `Y` only through `X` (exclusion, encoded by the structural equation), an
  instrument uncorrelated with `U` (exogeneity) and correlated with `X` (relevance) gives
  `Cov(Z, Y) / Cov(Z, X) = β`. The ordinary regression slope of `Y` on `X` is instead
  `β + Cov(X, U) / Var(X)` (confounding bias). The exclusion restriction is often phrased as
  "`Z ⊥ Y` given `X` and the confounders"; given `X` alone it fails whenever `X` and `Y` are
  confounded, so it is not used here.
* **Inverse-variance weighting** (Burgess, Butterworth & Thompson 2013). For SNP-level summary
  statistics `β̂_{Xj}`, `β̂_{Yj}` with outcome standard errors `σ_j > 0`, the IVW estimator
  `∑ β̂_{Xj} β̂_{Yj} σ_j⁻² / ∑ β̂_{Xj}² σ_j⁻²` is the weighted least-squares slope through the
  origin and the weighted mean of the ratio estimates `β̂_{Yj} / β̂_{Xj}` with weights
  `w_j = β̂_{Xj}² / σ_j²`. If `β̂_{Yj} = β β̂_{Xj} + ε_j` with uncorrelated mean-zero errors of
  variance `σ_j²` and the `β̂_{Xj}` treated as fixed (the first-order, "no measurement error"
  approximation), the estimator is unbiased with variance `(∑ w_j)⁻¹`, exactly.
* **MR-Egger** (Bowden, Davey Smith & Burgess 2015). The weighted regression of `β̂_{Yj}` on
  `β̂_{Xj}` with an intercept. If the SNP effects on the outcome are `Γ_j = α_j + β γ_j`, where
  `α_j` is the direct (pleiotropic) effect and `γ_j` the SNP–exposure effect, the Egger slope
  is `β + Cov_w(γ, α) / Var_w(γ)` and the intercept is the weighted mean pleiotropy minus a
  correction; under InSIDE (`Cov_w(α, γ) = 0`, instrument strength independent of direct
  effect) the slope is `β` and the intercept is the weighted mean pleiotropic effect, while the
  IVW estimator is biased by `∑ w'_j γ_j α_j / ∑ w'_j γ_j²`. The statements are exact
  identities for the given (population) SNP effects, with InSIDE as the weighted covariance of
  the `J` SNPs; the paper's `J → ∞` sampling version is not formalized.
* **Weak instruments** (Burgess & Thompson 2011). A ratio whose denominator is Gaussian with
  positive variance, and whose numerator is independent of it and not almost surely zero, has
  `𝔼|N / D| = ∞`: the ratio estimator `β̂_Y / β̂_X` with normally distributed `β̂_X` has no
  mean.
* **Local average treatment effect** (Imbens & Angrist 1994, Theorem 1; Angrist, Imbens &
  Rubin 1996). A potential-outcomes model with a binary instrument `Z`, potential treatments
  `D(z)` and potential outcomes `Y(z, d)`. Under independence of `Z` from the potential
  variables, exclusion (`Y(0, d) = Y(1, d)`) and monotonicity (`D(0) ≤ D(1)`), the Wald
  estimand `(𝔼[Y | Z = 1] - 𝔼[Y | Z = 0]) / (𝔼[D | Z = 1] - 𝔼[D | Z = 0])` equals the average
  effect `𝔼[Y(1) - Y(0) | complier]`. The denominator is the proportion of compliers
  (`D(0) = 0`, `D(1) = 1`), so relevance (a positive proportion of compliers) is what makes the
  identity informative; without it both sides are Lean's junk value `0`.

## Main results

* `LinearIVModel.covariance_div_covariance` (and `_of_indepFun`, `covariance_div_variance_div`):
  the Wald ratio identifies `β`.
* `LinearIVModel.covariance_div_variance`: the confounded regression slope.
* `ivw_eq_weightedMean`, `ivw_le_weightedSSR`, `integral_ivw`, `variance_ivw`: the IVW estimator.
* `eggerSSR_le`, `eggerSlope_eq`, `eggerIntercept_eq`, `eggerSlope_eq_of_inside`,
  `ivw_of_pleiotropy`: MR-Egger, InSIDE, and the pleiotropy bias of IVW.
* `lintegral_enorm_div_eq_top`, `not_integrable_div_gaussian`: no mean for a ratio with a
  Gaussian denominator.
* `PotentialOutcomes.armMean_treated_sub`, `PotentialOutcomes.armMean_outcome_sub`,
  `PotentialOutcomes.waldEstimand_eq_late`: first stage, reduced form, and the IV estimand as
  the complier average effect.

## References

* A. Wald, "The fitting of straight lines if both variables are subject to error",
  *Ann. Math. Statist.* 11 (1940), 284–300.
* G. W. Imbens, J. D. Angrist, "Identification and estimation of local average treatment
  effects", *Econometrica* 62 (1994), 467–475.
* J. D. Angrist, G. W. Imbens, D. B. Rubin, "Identification of causal effects using
  instrumental variables", *J. Amer. Statist. Assoc.* 91 (1996), 444–455.
* G. Davey Smith, S. Ebrahim, "'Mendelian randomization': can genetic epidemiology contribute
  to understanding environmental determinants of disease?", *Int. J. Epidemiol.* 32 (2003),
  1–22.
* S. Burgess, A. Butterworth, S. G. Thompson, "Mendelian randomization analysis with multiple
  genetic variants using summarized data", *Genet. Epidemiol.* 37 (2013), 658–665.
* J. Bowden, G. Davey Smith, S. Burgess, "Mendelian randomization with invalid instruments:
  effect estimation and bias detection through Egger regression", *Int. J. Epidemiol.* 44
  (2015), 512–525.
* S. Burgess, S. G. Thompson, "Bias in causal estimates from Mendelian randomization studies
  with weak instruments", *Stat. Med.* 30 (2011), 1312–1323.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.Biology.StatisticalGenetics.MendelianRandomization

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The Wald ratio in the linear instrumental-variable model -/

/-- The linear instrumental-variable model: an instrument `Z`, an exposure `X` and
an outcome `Y = α + β X + U` on a probability space, all square integrable. The error `U`
collects every cause of `Y` other than `X`, including the confounders of `X` and `Y`; `X` may
depend on `U` arbitrarily. The instrument enters the outcome only through the exposure
(exclusion), which is the content of the structural equation `outcome_eq`. Exogeneity
(`Cov(Z, U) = 0`) and relevance (`Cov(Z, X) ≠ 0`) are hypotheses of the theorems that use
them. -/
structure LinearIVModel (μ : Measure Ω) where
  /-- The instrument `Z` (in Mendelian randomization, a genotype). -/
  instrument : Ω → ℝ
  /-- The exposure `X`. -/
  exposure : Ω → ℝ
  /-- The outcome `Y`. -/
  outcome : Ω → ℝ
  /-- The structural error `U`: all other causes of the outcome. -/
  error : Ω → ℝ
  /-- The intercept `α`. -/
  intercept : ℝ
  /-- The causal effect `β` of the exposure on the outcome. -/
  effect : ℝ
  /-- The instrument is square integrable. -/
  memLp_instrument : MemLp instrument 2 μ
  /-- The exposure is square integrable. -/
  memLp_exposure : MemLp exposure 2 μ
  /-- The error is square integrable. -/
  memLp_error : MemLp error 2 μ
  /-- The structural equation `Y = α + β X + U`. -/
  outcome_eq : ∀ ω, outcome ω = intercept + effect * exposure ω + error ω

namespace LinearIVModel

variable {μ : Measure Ω} [IsProbabilityMeasure μ] (M : LinearIVModel μ)

/-- The covariance of any square-integrable variable with the outcome splits along the
structural equation: `Cov(V, Y) = β Cov(V, X) + Cov(V, U)`. -/
theorem covariance_outcome {V : Ω → ℝ} (hV : MemLp V 2 μ) :
    cov[V, M.outcome; μ] = M.effect * cov[V, M.exposure; μ] + cov[V, M.error; μ] := by
  have hXL : MemLp (M.effect • M.exposure) 2 μ := M.memLp_exposure.const_smul _
  have hY : M.outcome = fun ω => M.intercept + (M.effect • M.exposure + M.error) ω := by
    funext ω
    simp [M.outcome_eq, add_assoc]
  rw [hY, covariance_const_add_right ((hXL.add M.memLp_error).integrable one_le_two),
    covariance_add_right hV hXL M.memLp_error, covariance_smul_right]

/-- The Wald ratio: for an exogenous (`Cov(Z, U) = 0`) and relevant (`Cov(Z, X) ≠ 0`)
instrument, `Cov(Z, Y) / Cov(Z, X) = β`. For a two-valued `Z` the ratio is the grouping
estimator of Wald (1940), the difference of the group means of `Y` over that of `X`. -/
theorem covariance_div_covariance (hZU : cov[M.instrument, M.error; μ] = 0)
    (hZX : cov[M.instrument, M.exposure; μ] ≠ 0) :
    cov[M.instrument, M.outcome; μ] / cov[M.instrument, M.exposure; μ] = M.effect := by
  rw [M.covariance_outcome M.memLp_instrument, hZU, add_zero, mul_div_assoc, div_self hZX,
    mul_one]

/-- The Wald ratio for an instrument independent of the error term. -/
theorem covariance_div_covariance_of_indepFun (hZU : IndepFun M.instrument M.error μ)
    (hZX : cov[M.instrument, M.exposure; μ] ≠ 0) :
    cov[M.instrument, M.outcome; μ] / cov[M.instrument, M.exposure; μ] = M.effect :=
  M.covariance_div_covariance (hZU.covariance_eq_zero M.memLp_instrument M.memLp_error) hZX

/-- The Wald ratio as a ratio of regression slopes: the slope of `Y` on `Z` divided by the slope
of `X` on `Z` (the form used with SNP–outcome and SNP–exposure associations) is `β`. -/
theorem covariance_div_variance_div (hZU : cov[M.instrument, M.error; μ] = 0)
    (hZX : cov[M.instrument, M.exposure; μ] ≠ 0) :
    (cov[M.instrument, M.outcome; μ] / Var[M.instrument; μ]) /
      (cov[M.instrument, M.exposure; μ] / Var[M.instrument; μ]) = M.effect := by
  have hV : Var[M.instrument; μ] ≠ 0 := by
    intro hv
    apply hZX
    have hae := ae_eq_integral_of_variance_eq_zero M.memLp_instrument hv
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with ω hω
    simp [hω]
  rw [div_div_div_cancel_right₀ hV, M.covariance_div_covariance hZU hZX]

/-- Confounding bias: the ordinary least-squares slope of `Y` on `X` is
`β + Cov(X, U) / Var(X)`, which differs from `β` exactly when `Cov(X, U) ≠ 0`. -/
theorem covariance_div_variance (hX : Var[M.exposure; μ] ≠ 0) :
    cov[M.exposure, M.outcome; μ] / Var[M.exposure; μ] =
      M.effect + cov[M.exposure, M.error; μ] / Var[M.exposure; μ] := by
  rw [M.covariance_outcome M.memLp_exposure, covariance_self M.memLp_exposure.aemeasurable,
    add_div, mul_div_assoc, div_self hX, mul_one]

end LinearIVModel

/-! ### Summary-data estimators: inverse-variance weighting -/

section SummaryData

variable {ι : Type*} [Fintype ι]

/-- The ratio estimate `β̂_{Yj} / β̂_{Xj}` of SNP `j` (Lean's `x / 0 = 0` gives `0` when
`β̂_{Xj} = 0`; such SNPs carry weight `0` in `ivwWeight`). -/
noncomputable def ratioEstimate (bX bY : ι → ℝ) (j : ι) : ℝ := bY j / bX j

/-- The first-order inverse-variance weight `w_j = β̂_{Xj}² / σ_j²` of the ratio estimate of SNP
`j`, where `σ_j` is the standard error of `β̂_{Yj}` (Burgess, Butterworth & Thompson 2013). -/
noncomputable def ivwWeight (bX se : ι → ℝ) (j : ι) : ℝ := bX j ^ 2 / se j ^ 2

/-- The inverse-variance-weighted (IVW) estimator
`∑ β̂_{Xj} β̂_{Yj} σ_j⁻² / ∑ β̂_{Xj}² σ_j⁻²` (Burgess, Butterworth & Thompson 2013). The
standard errors are positive in the model; it is the junk value `0` if every `β̂_{Xj} = 0`. -/
noncomputable def ivw (bX bY se : ι → ℝ) : ℝ :=
  (∑ j, bX j * bY j / se j ^ 2) / ∑ j, ivwWeight bX se j

/-- The weighted residual sum of squares `∑ (β̂_{Yj} - b β̂_{Xj})² / σ_j²` of the regression
through the origin with slope `b`. -/
noncomputable def weightedSSR (bX bY se : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ j, (bY j - b * bX j) ^ 2 / se j ^ 2

/-- The IVW estimator is the weighted mean of the ratio estimates with weights
`w_j = β̂_{Xj}² / σ_j²`. This holds for all data: a SNP with `β̂_{Xj} = 0` has weight `0` and
contributes nothing to either side. -/
theorem ivw_eq_weightedMean (bX bY se : ι → ℝ) :
    ivw bX bY se =
      (∑ j, ivwWeight bX se j * ratioEstimate bX bY j) / ∑ j, ivwWeight bX se j := by
  unfold ivw
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold ivwWeight ratioEstimate
  by_cases hb : bX j = 0
  · simp [hb]
  · rw [div_mul_div_comm, show bX j ^ 2 * bY j = bX j * bY j * bX j by ring,
      mul_div_mul_right _ _ hb]

/-- The IVW estimator is the weighted least-squares slope through the origin: it minimizes
the weighted residual sum of squares. This holds for all data: if every `β̂_{Xj} = 0` the sum
does not depend on the slope (and `ivw` is the junk value `0`), and a SNP with `σ_j = 0` has
weight `0` on both sides by Lean's `x / 0 = 0`. -/
theorem ivw_le_weightedSSR (bX bY se : ι → ℝ) (b : ℝ) :
    weightedSSR bX bY se (ivw bX bY se) ≤ weightedSSR bX bY se b := by
  set W := ∑ j, ivwWeight bX se j with hW
  set T := ∑ j, bX j * bY j / se j ^ 2 with hT
  have hexp : ∀ c, weightedSSR bX bY se c = (∑ j, bY j ^ 2 / se j ^ 2) - 2 * c * T + c ^ 2 * W := by
    intro c
    rw [hT, hW, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by unfold ivwWeight; ring
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun j _ => by unfold ivwWeight; positivity
  have hivw : ivw bX bY se = T / W := rfl
  rcases hW0.eq_or_lt with h | h
  · have hT0 : T = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => by unfold ivwWeight; positivity)).1 h.symm j (Finset.mem_univ _)
      unfold ivwWeight at hj
      rcases div_eq_zero_iff.1 hj with h1 | h1
      · simp [pow_eq_zero_iff two_ne_zero |>.1 h1]
      · simp [h1]
    rw [hexp, hexp, hT0, ← h]
    simp
  · rw [hexp, hexp, hivw]
    have key : (∑ j, bY j ^ 2 / se j ^ 2) - 2 * b * T + b ^ 2 * W -
        ((∑ j, bY j ^ 2 / se j ^ 2) - 2 * (T / W) * T + (T / W) ^ 2 * W) =
        W * (b - T / W) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg hW0 (sq_nonneg (b - T / W))]

/-- The total weight is positive as soon as some SNP has `β̂_{Xj} ≠ 0`. -/
theorem sum_ivwWeight_pos {bX se : ι → ℝ} (hse : ∀ j, 0 < se j) (hX : ∃ j, bX j ≠ 0) :
    0 < ∑ j, ivwWeight bX se j := by
  obtain ⟨i, hi⟩ := hX
  refine Finset.sum_pos' (fun j _ => by unfold ivwWeight; positivity) ⟨i, Finset.mem_univ _, ?_⟩
  have := hse i
  unfold ivwWeight
  positivity

/-- Without error, IVW recovers the causal effect: if `β̂_{Yj} = β β̂_{Xj}` for all `j` and some
`β̂_{Xj} ≠ 0`, then the IVW estimate is `β`. -/
theorem ivw_of_proportional {bX se : ι → ℝ} (hse : ∀ j, 0 < se j) (hX : ∃ j, bX j ≠ 0)
    (β : ℝ) : ivw bX (fun j => β * bX j) se = β := by
  have hW := (sum_ivwWeight_pos hse hX).ne'
  unfold ivw
  rw [show ∑ j, bX j * (β * bX j) / se j ^ 2 = β * ∑ j, ivwWeight bX se j by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by unfold ivwWeight; ring,
    mul_div_assoc, div_self hW, mul_one]

/-- IVW is affine in the outcome associations: `ivw (β β̂_X + e) = β + ∑ c_j e_j` with
`c_j = β̂_{Xj} / σ_j² / ∑ w`. -/
private theorem ivw_linear {bX se : ι → ℝ} (hW : ∑ j, ivwWeight bX se j ≠ 0) (β : ℝ)
    (e : ι → ℝ) :
    ivw bX (fun j => β * bX j + e j) se =
      β + ∑ j, bX j / se j ^ 2 / (∑ k, ivwWeight bX se k) * e j := by
  unfold ivw
  rw [show ∑ j, bX j * (β * bX j + e j) / se j ^ 2 =
      β * ∑ j, ivwWeight bX se j + ∑ j, bX j * e j / se j ^ 2 by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by unfold ivwWeight; ring,
    add_div, mul_div_assoc, div_self hW, mul_one, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Unbiasedness of IVW (Burgess, Butterworth & Thompson 2013), with the SNP–exposure
associations `β̂_{Xj}` treated as fixed: if `β̂_{Yj} = β β̂_{Xj} + ε_j` with integrable
mean-zero errors, the IVW estimator has mean `β`. -/
theorem integral_ivw {bX se : ι → ℝ} (hse : ∀ j, 0 < se j) (hX : ∃ j, bX j ≠ 0) (β : ℝ)
    {ε : ι → Ω → ℝ} (hint : ∀ j, Integrable (ε j) μ) (hmean : ∀ j, ∫ ω, ε j ω ∂μ = 0) :
    ∫ ω, ivw bX (fun j => β * bX j + ε j ω) se ∂μ = β := by
  have hW := (sum_ivwWeight_pos hse hX).ne'
  simp_rw [ivw_linear hW]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun j _ => (hint j).const_mul _),
    integral_finsetSum _ fun j _ => (hint j).const_mul _]
  simp [integral_const_mul, hmean]

/-- The first-order variance of IVW (Burgess, Butterworth & Thompson 2013): with the
`β̂_{Xj}` fixed and `β̂_{Yj} = β β̂_{Xj} + ε_j`, where the errors are square integrable,
pairwise uncorrelated (for instance independent) and `Var(ε_j) = σ_j²`, the IVW estimator has
variance `(∑ w_j)⁻¹ = (∑ β̂_{Xj}² / σ_j²)⁻¹`. -/
theorem variance_ivw {bX se : ι → ℝ} (hse : ∀ j, 0 < se j) (hX : ∃ j, bX j ≠ 0) (β : ℝ)
    {ε : ι → Ω → ℝ} (hL2 : ∀ j, MemLp (ε j) 2 μ)
    (hcov : ∀ i j, i ≠ j → cov[ε i, ε j; μ] = 0) (hvar : ∀ j, Var[ε j; μ] = se j ^ 2) :
    Var[fun ω => ivw bX (fun j => β * bX j + ε j ω) se; μ] = (∑ j, ivwWeight bX se j)⁻¹ := by
  classical
  have hW := (sum_ivwWeight_pos hse hX).ne'
  set c : ι → ℝ := fun j => bX j / se j ^ 2 / ∑ k, ivwWeight bX se k with hc
  simp_rw [ivw_linear hW]
  change Var[fun ω => β + ∑ j, c j * ε j ω; μ] = _
  have hL2c : ∀ j, MemLp (fun ω => c j * ε j ω) 2 μ := fun j => (hL2 j).const_mul _
  rw [variance_const_add (memLp_finsetSum _ fun j _ => hL2c j).aestronglyMeasurable,
    variance_fun_sum hL2c]
  have hdiag : ∀ i j, cov[fun ω => c i * ε i ω, fun ω => c j * ε j ω; μ] =
      if i = j then c j ^ 2 * se j ^ 2 else 0 := by
    intro i j
    rw [covariance_const_mul_left, covariance_const_mul_right]
    split_ifs with h
    · subst h
      rw [covariance_self (hL2 i).aemeasurable, hvar]
      ring
    · rw [hcov i j h]
      ring
  simp only [hdiag, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [show ∑ j, c j ^ 2 * se j ^ 2 =
      (∑ j, ivwWeight bX se j) / (∑ k, ivwWeight bX se k) ^ 2 by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (hse j).ne'
    rw [hc]
    unfold ivwWeight
    field_simp]
  field_simp

/-! ### MR-Egger regression and InSIDE -/

/-- The weighted mean `∑ v_j a_j / ∑ v_j`. -/
noncomputable def weightedMean (v a : ι → ℝ) : ℝ := (∑ j, v j * a j) / ∑ j, v j

/-- The weighted covariance `∑ v_j (a_j - ā_v)(b_j - b̄_v) / ∑ v_j`, where `ā_v` and `b̄_v` are
weighted means. -/
noncomputable def weightedCov (v a b : ι → ℝ) : ℝ :=
  (∑ j, v j * (a j - weightedMean v a) * (b j - weightedMean v b)) / ∑ j, v j

private theorem weightedMean_add_mul (v α γ : ι → ℝ) (β : ℝ) :
    weightedMean v (fun j => α j + β * γ j) = weightedMean v α + β * weightedMean v γ := by
  unfold weightedMean
  rw [show ∑ j, v j * (α j + β * γ j) = ∑ j, v j * α j + β * ∑ j, v j * γ j by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring, add_div, mul_div_assoc]

private theorem weightedCov_add_mul (v γ α : ι → ℝ) (β : ℝ) :
    weightedCov v γ (fun j => α j + β * γ j) = weightedCov v γ α + β * weightedCov v γ γ := by
  unfold weightedCov
  rw [weightedMean_add_mul, ← mul_div_assoc, ← add_div, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem weightedCov_comm (v a b : ι → ℝ) : weightedCov v a b = weightedCov v b a := by
  unfold weightedCov
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The MR-Egger slope (Bowden, Davey Smith & Burgess 2015): the slope of the weighted linear
regression of `β̂_{Yj}` on `β̂_{Xj}` with an intercept, `Cov_v(β̂_X, β̂_Y) / Var_v(β̂_X)`. The
paper's weights are `v_j = σ_j⁻²`. -/
noncomputable def eggerSlope (v bX bY : ι → ℝ) : ℝ := weightedCov v bX bY / weightedCov v bX bX

/-- The MR-Egger intercept `β̂̄_Y - slope · β̂̄_X` (weighted means). -/
noncomputable def eggerIntercept (v bX bY : ι → ℝ) : ℝ :=
  weightedMean v bY - eggerSlope v bX bY * weightedMean v bX

/-- The weighted residual sum of squares `∑ v_j (β̂_{Yj} - a - b β̂_{Xj})²` of the line with
intercept `a` and slope `b`. -/
noncomputable def eggerSSR (v bX bY : ι → ℝ) (a b : ℝ) : ℝ :=
  ∑ j, v j * (bY j - a - b * bX j) ^ 2

/-- The MR-Egger line is the weighted least-squares line: for nonnegative weights and `β̂_X`
of nonzero weighted variance (so the total weight is positive and `β̂_X` is not constant on the
support of the weights), it minimizes the weighted residual sum of squares. -/
theorem eggerSSR_le {v bX : ι → ℝ} (bY : ι → ℝ) (hv : ∀ j, 0 ≤ v j)
    (hX : weightedCov v bX bX ≠ 0) (a b : ℝ) :
    eggerSSR v bX bY (eggerIntercept v bX bY) (eggerSlope v bX bY) ≤ eggerSSR v bX bY a b := by
  set S := ∑ j, v j with hS
  set m := weightedMean v bX with hm
  set n := weightedMean v bY with hn
  set Cxx := ∑ j, v j * (bX j - m) * (bX j - m) with hCxx
  set Cxy := ∑ j, v j * (bX j - m) * (bY j - n) with hCxy
  have hS0 : S ≠ 0 := by
    intro h
    apply hX
    simp [weightedCov, ← hS, h]
  have hC0 : Cxx ≠ 0 := by
    intro h
    apply hX
    simp [weightedCov, ← hm, ← hCxx, h]
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun j _ => hv j
  have hCnn : 0 ≤ Cxx := Finset.sum_nonneg fun j _ => by
    have := hv j
    rw [mul_assoc]
    exact mul_nonneg this (mul_self_nonneg _)
  have hsx : ∑ j, v j * (bX j - m) = 0 := by
    rw [show ∑ j, v j * (bX j - m) = ∑ j, v j * bX j - m * S by
      rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring, hm, weightedMean, ← hS]
    field_simp
    ring
  have hsy : ∑ j, v j * (bY j - n) = 0 := by
    rw [show ∑ j, v j * (bY j - n) = ∑ j, v j * bY j - n * S by
      rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring, hn, weightedMean, ← hS]
    field_simp
    ring
  -- `SSR(a, b) = Q(b) + S (n - a - b m)²` with `Q(b) = ∑ v ((y - n) - b (x - m))²`
  have hdec : ∀ a b, eggerSSR v bX bY a b =
      (∑ j, v j * (bY j - n) * (bY j - n)) - 2 * b * Cxy + b ^ 2 * Cxx +
        S * (n - a - b * m) ^ 2 := by
    intro a b
    have e : eggerSSR v bX bY a b = (∑ j, v j * (bY j - n) * (bY j - n)) - 2 * b * Cxy +
        b ^ 2 * Cxx + 2 * (n - a - b * m) * (∑ j, v j * (bY j - n)) -
        2 * (n - a - b * m) * b * (∑ j, v j * (bX j - m)) + (n - a - b * m) ^ 2 * S := by
      rw [eggerSSR, hCxy, hCxx, hS, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, hsx, hsy]
    ring
  have hslope : eggerSlope v bX bY = Cxy / Cxx := by
    rw [eggerSlope, weightedCov, weightedCov, ← hS, ← hm, ← hn, ← hCxx, ← hCxy]
    field_simp
  have hint : eggerIntercept v bX bY = n - Cxy / Cxx * m := by
    rw [eggerIntercept, hslope]
  rw [hdec, hdec, hint, hslope]
  have key : (∑ j, v j * (bY j - n) * (bY j - n)) - 2 * b * Cxy + b ^ 2 * Cxx +
        S * (n - a - b * m) ^ 2 -
      ((∑ j, v j * (bY j - n) * (bY j - n)) - 2 * (Cxy / Cxx) * Cxy +
        (Cxy / Cxx) ^ 2 * Cxx + S * (n - (n - Cxy / Cxx * m) - Cxy / Cxx * m) ^ 2) =
      Cxx * (b - Cxy / Cxx) ^ 2 + S * (n - a - b * m) ^ 2 := by
    field_simp
    ring
  nlinarith [mul_nonneg hCnn (sq_nonneg (b - Cxy / Cxx)),
    mul_nonneg hSnn (sq_nonneg (n - a - b * m))]

/-- The MR-Egger slope under pleiotropy (Bowden, Davey Smith & Burgess 2015): if the SNP–outcome
effects are `Γ_j = α_j + β γ_j`, with direct (pleiotropic) effects `α_j` and SNP–exposure
effects `γ_j`, the Egger slope of `Γ` on `γ` is `β + Cov_v(γ, α) / Var_v(γ)`. -/
theorem eggerSlope_eq {v γ : ι → ℝ} (hγ : weightedCov v γ γ ≠ 0)
    (α : ι → ℝ) (β : ℝ) :
    eggerSlope v γ (fun j => α j + β * γ j) = β + weightedCov v γ α / weightedCov v γ γ := by
  unfold eggerSlope
  rw [weightedCov_add_mul, add_div, mul_div_assoc, div_self hγ, mul_one, add_comm]

/-- The MR-Egger intercept under pleiotropy: it is the weighted mean pleiotropic effect
`ᾱ_v` minus `Cov_v(γ, α) / Var_v(γ) · γ̄_v`. -/
theorem eggerIntercept_eq {v γ : ι → ℝ} (hγ : weightedCov v γ γ ≠ 0)
    (α : ι → ℝ) (β : ℝ) :
    eggerIntercept v γ (fun j => α j + β * γ j) =
      weightedMean v α - weightedCov v γ α / weightedCov v γ γ * weightedMean v γ := by
  unfold eggerIntercept
  rw [eggerSlope_eq hγ, weightedMean_add_mul]
  ring

/-- InSIDE (Bowden, Davey Smith & Burgess 2015): if the pleiotropic effects are uncorrelated with
the instrument strengths in the weighted sense, `Cov_v(α, γ) = 0`, the MR-Egger slope is the
causal effect `β` and the intercept is the weighted mean pleiotropic effect `ᾱ_v`, the
directional pleiotropy. -/
theorem eggerSlope_eq_of_inside {v γ α : ι → ℝ} (hγ : weightedCov v γ γ ≠ 0)
    (hinside : weightedCov v α γ = 0) (β : ℝ) :
    eggerSlope v γ (fun j => α j + β * γ j) = β ∧
      eggerIntercept v γ (fun j => α j + β * γ j) = weightedMean v α := by
  rw [weightedCov_comm] at hinside
  refine ⟨?_, ?_⟩
  · rw [eggerSlope_eq hγ, hinside, zero_div, add_zero]
  · rw [eggerIntercept_eq hγ, hinside, zero_div, zero_mul, sub_zero]

/-- Directional pleiotropy biases IVW: if `Γ_j = α_j + β γ_j`, the IVW estimate is
`β + ∑ γ_j α_j σ_j⁻² / ∑ γ_j² σ_j⁻²`. For example a common direct effect `α_j = α ≠ 0`
biases IVW whenever `∑ γ_j σ_j⁻² ≠ 0`, whereas a constant `α` satisfies InSIDE, so
`eggerSlope_eq_of_inside` gives MR-Egger slope `β` and intercept `α`. -/
theorem ivw_of_pleiotropy {γ se : ι → ℝ} (hse : ∀ j, 0 < se j) (hγ : ∃ j, γ j ≠ 0)
    (α : ι → ℝ) (β : ℝ) :
    ivw γ (fun j => α j + β * γ j) se =
      β + (∑ j, γ j * α j / se j ^ 2) / ∑ j, ivwWeight γ se j := by
  have hW := (sum_ivwWeight_pos hse hγ).ne'
  have h := ivw_linear hW β α
  simp_rw [add_comm (α _)]
  rw [h, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

end SummaryData

/-! ### Weak instruments: the ratio estimator has no mean -/

/-- `𝔼|1 / X| = ∞` for a nondegenerate normal variable `X`: its density is bounded below near
`0`, where `1 / |x|` is not integrable. -/
private theorem lintegral_enorm_inv_gaussianReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ x, ‖x⁻¹‖ₑ ∂(gaussianReal m v) = ∞ := by
  set c : ℝ := (√(2 * Real.pi * v))⁻¹ * Real.exp (-(1 + |m|) ^ 2 / (2 * v)) with hc
  have hv0 : (0 : ℝ) < v := by positivity
  have hc0 : 0 < c := by positivity
  have hbound : ∀ x ∈ Set.Ioc (0 : ℝ) 1, c ≤ gaussianPDFReal m v x := by
    intro x hx
    rw [gaussianPDFReal_def]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have hsq : (x - m) ^ 2 ≤ (1 + |m|) ^ 2 := by
      nlinarith [hx.1, hx.2, abs_nonneg m, le_abs_self m, neg_abs_le m]
    rw [div_le_div_iff_of_pos_right (by positivity)]
    linarith
  have hinf : ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖x⁻¹‖ₑ = ∞ := by
    have hni : ¬ IntegrableOn (fun x : ℝ => x⁻¹) (Set.Ioc 0 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one, intervalIntegrable_inv_iff]
      simp
    by_contra h
    exact hni ⟨measurable_inv.aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.2 (lt_top_iff_ne_top.2 h)⟩
  rw [gaussianReal_of_var_ne_zero m hv,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF m v) measurable_inv.enorm]
  refine top_le_iff.1 (le_trans ?_ (setLIntegral_le_lintegral (Set.Ioc (0 : ℝ) 1) _))
  calc (∞ : ℝ≥0∞) = ENNReal.ofReal c * ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖x⁻¹‖ₑ := by
        rw [hinf, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc0).ne']
    _ = ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal c * ‖x⁻¹‖ₑ :=
        (lintegral_const_mul _ measurable_inv.enorm).symm
    _ ≤ ∫⁻ x in Set.Ioc (0 : ℝ) 1, (gaussianPDF m v * fun y : ℝ => ‖y⁻¹‖ₑ) x :=
        setLIntegral_mono ((measurable_gaussianPDF m v).mul measurable_inv.enorm) fun x hx =>
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (hbound x hx)) _

/-- A ratio with a Gaussian denominator has no first moment (a classical fact, recalled in the
weak-instrument analysis of Burgess & Thompson 2011): if `D ~ N(m, v)` with `v > 0` and `N` is
independent of `D` and not almost surely `0`, then `𝔼|N / D| = ∞`. Applied to the ratio
estimator `β̂_Y / β̂_X` with a normally distributed SNP–exposure estimate `β̂_X`. -/
theorem lintegral_enorm_div_eq_top {μ : Measure Ω} [IsProbabilityMeasure μ] {N D : Ω → ℝ}
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (hD : HasLaw D (gaussianReal m v) μ)
    (hN : AEMeasurable N μ) (hind : IndepFun N D μ) (hN0 : ¬ N =ᵐ[μ] 0) :
    ∫⁻ ω, ‖N ω / D ω‖ₑ ∂μ = ∞ := by
  have hsplit : (fun ω => ‖N ω / D ω‖ₑ) = fun ω => ‖N ω‖ₑ * ‖(D ω)⁻¹‖ₑ := by
    funext ω
    rw [div_eq_mul_inv, enorm_mul]
  have hind' : IndepFun (fun ω => ‖N ω‖ₑ) (fun ω => ‖(D ω)⁻¹‖ₑ) μ :=
    hind.comp measurable_enorm measurable_inv.enorm
  have hDi : AEMeasurable (fun ω => ‖(D ω)⁻¹‖ₑ) μ := hD.aemeasurable.inv.enorm
  rw [hsplit, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hN.enorm hDi hind',
    hD.lintegral_comp (f := fun x => ‖x⁻¹‖ₑ) measurable_inv.enorm.aemeasurable,
    lintegral_enorm_inv_gaussianReal hv]
  refine ENNReal.mul_top ?_
  rw [Ne, lintegral_eq_zero_iff' hN.enorm]
  intro h
  apply hN0
  filter_upwards [h] with ω hω
  simpa using hω

/-- The ratio of two independent normal variables, the denominator with positive variance and
the numerator not almost surely zero (`(mN, vN) ≠ (0, 0)`), is not integrable. -/
theorem not_integrable_div_gaussian {μ : Measure Ω} [IsProbabilityMeasure μ] {N D : Ω → ℝ}
    {mN mD : ℝ} {vN vD : ℝ≥0} (hvD : vD ≠ 0) (hN : HasLaw N (gaussianReal mN vN) μ)
    (hD : HasLaw D (gaussianReal mD vD) μ) (hind : IndepFun N D μ) (hN0 : mN ≠ 0 ∨ vN ≠ 0) :
    ¬ Integrable (fun ω => N ω / D ω) μ := by
  intro hint
  have hN0' : ¬ N =ᵐ[μ] 0 := by
    intro h
    have hmap := hN.map_eq
    rw [Measure.map_congr h] at hmap
    change Measure.map (fun _ => (0 : ℝ)) μ = _ at hmap
    have h1 : gaussianReal mN vN {0} = 1 := by
      rw [← hmap]
      simp [Measure.map_const]
    rcases eq_or_ne vN 0 with hv | hv
    · rw [hv, gaussianReal_zero_var] at h1
      have hm : mN ≠ 0 := hN0.resolve_right (not_not.2 hv)
      simp [hm] at h1
    · rw [gaussianReal_apply mN hv] at h1
      simp at h1
  exact (lintegral_enorm_div_eq_top hvD hD hN.aemeasurable hind hN0' ▸
    hasFiniteIntegral_iff_enorm.1 hint.2).ne rfl

/-! ### Potential outcomes and the local average treatment effect -/

/-- Under independence, conditioning on the instrument does not change the mean of a function of
the variables it is independent of. -/
private theorem integral_cond_eq_of_indepFun {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : Type*} [MeasurableSpace β] {Z : Ω → Bool} {V : Ω → β} (hZ : Measurable Z)
    (hV : Measurable V) (hind : IndepFun Z V μ) {f : β → ℝ} (hf : Measurable f) {z : Bool}
    (hz : μ (Z ⁻¹' {z}) ≠ 0) :
    ∫ ω, f (V ω) ∂μ[|Z ⁻¹' {z}] = ∫ ω, f (V ω) ∂μ := by
  have hA : MeasurableSet (Z ⁻¹' {z}) := hZ (measurableSet_singleton z)
  have hφ : Measurable (({z} : Set Bool).indicator fun _ => (1 : ℝ)) := measurable_of_countable _
  have hind' := hind.comp hφ hf
  have hmul : (Z ⁻¹' {z}).indicator (fun ω => f (V ω)) =
      fun ω => (({z} : Set Bool).indicator (fun _ => (1 : ℝ)) ∘ Z) ω * (f ∘ V) ω := by
    funext ω
    by_cases h : Z ω = z <;> simp [Set.indicator, h]
  have hone : (fun ω => (({z} : Set Bool).indicator (fun _ => (1 : ℝ)) ∘ Z) ω) =
      (Z ⁻¹' {z}).indicator 1 := by
    funext ω
    by_cases h : Z ω = z <;> simp [Set.indicator, h]
  rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hA, hmul,
    IndepFun.integral_fun_mul_eq_mul_integral hind' (hφ.comp hZ).aestronglyMeasurable
      (hf.comp hV).aestronglyMeasurable]
  rw [show μ[({z} : Set Bool).indicator (fun _ => (1 : ℝ)) ∘ Z] = μ.real (Z ⁻¹' {z}) by
    rw [← integral_indicator_one hA]
    exact congrArg (fun g => ∫ ω, g ω ∂μ) hone]
  rw [smul_eq_mul, ← mul_assoc, ENNReal.toReal_inv, measureReal_def,
    inv_mul_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hz, measure_ne_top μ _⟩), one_mul]
  rfl

/-- Integrals against `μ[|A]` only see the values on `A`. -/
private theorem integral_cond_congr {μ : Measure Ω} {A : Set Ω} (hA : MeasurableSet A)
    {f g : Ω → ℝ} (h : Set.EqOn f g A) : ∫ ω, f ω ∂μ[|A] = ∫ ω, g ω ∂μ[|A] := by
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure,
    setIntegral_congr_fun hA h]

/-- The four compliance types of Angrist, Imbens & Rubin (1996), determined by the pair of
potential treatments `(D(0), D(1))`. -/
inductive ComplianceType
  /-- `D(0) = 0`, `D(1) = 1`: takes the treatment exactly when encouraged. -/
  | complier
  /-- `D(0) = D(1) = 1`. -/
  | alwaysTaker
  /-- `D(0) = D(1) = 0`. -/
  | neverTaker
  /-- `D(0) = 1`, `D(1) = 0`: takes the treatment exactly when not encouraged. -/
  | defier
  deriving DecidableEq

/-- The compliance type of the potential treatments `(D(0), D(1)) = (d₀, d₁)`. -/
def complianceType : Bool → Bool → ComplianceType
  | false, true => .complier
  | true, true => .alwaysTaker
  | false, false => .neverTaker
  | true, false => .defier

/-- A potential-outcomes model with a binary instrument and a binary treatment (Imbens &
Angrist 1994; Angrist, Imbens & Rubin 1996): the assigned instrument `Z`, the potential
treatments `D(z)` and the potential outcomes `Y(z, d)`, all measurable. The observed treatment
is `D(Z)` and the observed outcome `Y(Z, D(Z))`. The identifying assumptions (independence,
exclusion, monotonicity, relevance) are separate predicates. -/
structure PotentialOutcomes (Ω : Type*) [MeasurableSpace Ω] where
  /-- The assigned instrument `Z`. -/
  instrument : Ω → Bool
  /-- The potential treatment `D(z)` under assignment `z`. -/
  treatment : Bool → Ω → Bool
  /-- The potential outcome `Y(z, d)` under assignment `z` and treatment `d`. -/
  outcome : Bool → Bool → Ω → ℝ
  /-- The instrument is measurable. -/
  measurable_instrument : Measurable instrument
  /-- The potential treatments are measurable. -/
  measurable_treatment : ∀ z, Measurable (treatment z)
  /-- The potential outcomes are measurable. -/
  measurable_outcome : ∀ z d, Measurable (outcome z d)

namespace PotentialOutcomes

variable (P : PotentialOutcomes Ω)

/-- The observed treatment `D = D(Z)`. -/
def observedTreatment (ω : Ω) : Bool := P.treatment (P.instrument ω) ω

/-- The observed outcome `Y = Y(Z, D(Z))`. -/
def observedOutcome (ω : Ω) : ℝ := P.outcome (P.instrument ω) (P.observedTreatment ω) ω

/-- The compliance type of a unit. -/
def type (ω : Ω) : ComplianceType := complianceType (P.treatment false ω) (P.treatment true ω)

/-- The compliers, `D(0) = 0` and `D(1) = 1`. -/
def compliers : Set Ω := {ω | P.type ω = .complier}

/-- Independence (random assignment): the instrument is independent of the vector of all
potential treatments and potential outcomes. -/
def Independence (μ : Measure Ω) : Prop :=
  IndepFun P.instrument (fun ω => (fun z => P.treatment z ω, fun z d => P.outcome z d ω)) μ

/-- Exclusion: the instrument affects the outcome only through the treatment,
`Y(0, d) = Y(1, d)`. -/
def Exclusion : Prop := ∀ d ω, P.outcome false d ω = P.outcome true d ω

/-- Monotonicity: assignment never decreases the treatment, `D(0) ≤ D(1)`; there are no
defiers. -/
def Monotonicity : Prop := ∀ ω, P.treatment false ω ≤ P.treatment true ω

/-- The mean of `f` in the arm `Z = z`, `𝔼[f | Z = z]`, the expectation under the conditional
measure. It is the junk value `0` when `P(Z = z) = 0`. -/
noncomputable def armMean (μ : Measure Ω) (f : Ω → ℝ) (z : Bool) : ℝ :=
  ∫ ω, f ω ∂μ[|P.instrument ⁻¹' {z}]

/-- The observed treatment as a `0`/`1` real variable. -/
def treated (ω : Ω) : ℝ := if P.observedTreatment ω then 1 else 0

/-- The Wald (instrumental-variable) estimand
`(𝔼[Y | Z = 1] - 𝔼[Y | Z = 0]) / (𝔼[D | Z = 1] - 𝔼[D | Z = 0])`. -/
noncomputable def waldEstimand (μ : Measure Ω) : ℝ :=
  (P.armMean μ P.observedOutcome true - P.armMean μ P.observedOutcome false) /
    (P.armMean μ P.treated true - P.armMean μ P.treated false)

/-- The vector of potential treatments and potential outcomes of a unit. -/
private def potentials (ω : Ω) : (Bool → Bool) × (Bool → Bool → ℝ) :=
  (fun z => P.treatment z ω, fun z d => P.outcome z d ω)

private theorem measurable_potentials : Measurable P.potentials :=
  Measurable.prodMk (measurable_pi_iff.2 fun z => P.measurable_treatment z)
    (measurable_pi_iff.2 fun z => measurable_pi_iff.2 fun d => P.measurable_outcome z d)

/-- Under independence, an arm mean of a variable that on that arm is a function of the
potential vector equals the population mean of that function. -/
private theorem armMean_eq {μ : Measure Ω} [IsProbabilityMeasure μ] (hind : P.Independence μ)
    {z : Bool} (hz : μ (P.instrument ⁻¹' {z}) ≠ 0)
    {f : (Bool → Bool) × (Bool → Bool → ℝ) → ℝ} (hf : Measurable f) {g : Ω → ℝ}
    (hg : ∀ ω, P.instrument ω = z → g ω = f (P.potentials ω)) :
    P.armMean μ g z = ∫ ω, f (P.potentials ω) ∂μ := by
  rw [armMean, integral_cond_congr (P.measurable_instrument (measurableSet_singleton z))
    (fun ω hω => hg ω hω)]
  exact integral_cond_eq_of_indepFun P.measurable_instrument P.measurable_potentials hind hf hz

/-- The treatment rate in arm `z` is `P(D(z) = 1)`. -/
private theorem armMean_treated {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hind : P.Independence μ) {z : Bool} (hz : μ (P.instrument ⁻¹' {z}) ≠ 0) :
    P.armMean μ P.treated z = μ.real {ω | P.treatment z ω = true} := by
  rw [P.armMean_eq hind hz (f := fun v => if v.1 z then (1 : ℝ) else 0)
    ((measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp
      ((measurable_pi_apply z).comp measurable_fst))
    (fun ω hω => by
      unfold treated observedTreatment potentials
      rw [hω])]
  change _ = μ.real (P.treatment z ⁻¹' {true})
  rw [← integral_indicator_one ((P.measurable_treatment z) (measurableSet_singleton true))]
  congr 1
  funext ω
  by_cases h : P.treatment z ω = true <;> simp [potentials, Set.indicator, h]

/-- The outcome under assignment `z` and the potential treatment `D(z)`, as a function of the
potential vector. -/
private def outcomeAt (z : Bool) (v : (Bool → Bool) × (Bool → Bool → ℝ)) : ℝ :=
  if v.1 z then v.2 z true else v.2 z false

private theorem measurable_outcomeAt (z : Bool) : Measurable (outcomeAt z) := by
  have hs : MeasurableSet {v : (Bool → Bool) × (Bool → Bool → ℝ) | v.1 z = true} :=
    measurableSet_eq_fun ((measurable_pi_apply z).comp measurable_fst) measurable_const
  exact Measurable.ite hs
    ((measurable_pi_apply true).comp ((measurable_pi_apply z).comp measurable_snd))
    ((measurable_pi_apply false).comp ((measurable_pi_apply z).comp measurable_snd))

private theorem integrable_outcomeAt {μ : Measure Ω} (hY : ∀ z d, Integrable (P.outcome z d) μ)
    (z : Bool) : Integrable (fun ω => outcomeAt z (P.potentials ω)) μ := by
  refine Integrable.mono' ((hY z true).norm.add (hY z false).norm)
    ((measurable_outcomeAt z).comp P.measurable_potentials).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  simp only [outcomeAt, potentials, Pi.add_apply]
  by_cases h : P.treatment z ω = true <;> simp [h]

/-- The mean outcome in arm `z` is `𝔼[Y(z, D(z))]`. -/
private theorem armMean_observedOutcome {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hind : P.Independence μ) {z : Bool} (hz : μ (P.instrument ⁻¹' {z}) ≠ 0) :
    P.armMean μ P.observedOutcome z = ∫ ω, outcomeAt z (P.potentials ω) ∂μ :=
  P.armMean_eq hind hz (measurable_outcomeAt z) fun ω hω => by
    simp only [observedOutcome, observedTreatment, outcomeAt, potentials, hω]
    by_cases h : P.treatment z ω = true <;> simp [h]

private theorem measurableSet_compliers : MeasurableSet P.compliers := by
  have h : P.compliers = {ω | P.treatment false ω = false} ∩ {ω | P.treatment true ω = true} := by
    ext ω
    simp only [compliers, type, Set.mem_ofPred_eq, Set.mem_inter_iff]
    by_cases h0 : P.treatment false ω = true <;> by_cases h1 : P.treatment true ω = true <;>
      simp_all [complianceType]
  rw [h]
  exact ((P.measurable_treatment false) (measurableSet_singleton false)).inter
    ((P.measurable_treatment true) (measurableSet_singleton true))

/-- The first stage (Imbens & Angrist 1994): under independence and monotonicity, with both
arms of positive probability, the difference in treatment rates between the arms is the
proportion of compliers. -/
theorem armMean_treated_sub {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hind : P.Independence μ) (hmono : P.Monotonicity)
    (hZ : ∀ z, μ (P.instrument ⁻¹' {z}) ≠ 0) :
    P.armMean μ P.treated true - P.armMean μ P.treated false = μ.real P.compliers := by
  rw [P.armMean_treated hind (hZ true), P.armMean_treated hind (hZ false),
    ← measureReal_sdiff (s₁ := {ω | P.treatment true ω = true})
      (s₂ := {ω | P.treatment false ω = true}) (fun ω (h : P.treatment false ω = true) => by
        have := hmono ω
        rw [h] at this
        exact top_le_iff.1 this)
      ((P.measurable_treatment false) (measurableSet_singleton true))]
  congr 1
  ext ω
  simp only [compliers, type, Set.mem_sdiff, Set.mem_ofPred_eq]
  by_cases h0 : P.treatment false ω = true <;> by_cases h1 : P.treatment true ω = true <;>
    simp_all [complianceType]

/-- The reduced form (Imbens & Angrist 1994): under independence, exclusion and monotonicity,
with integrable potential outcomes and both arms of positive probability, the difference in
mean outcomes between the arms is `𝔼[(Y(z, 1) - Y(z, 0)) 1_complier]`, for either `z`. -/
theorem armMean_outcome_sub {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hind : P.Independence μ) (hexcl : P.Exclusion) (hmono : P.Monotonicity)
    (hY : ∀ z d, Integrable (P.outcome z d) μ) (hZ : ∀ z, μ (P.instrument ⁻¹' {z}) ≠ 0)
    (z : Bool) :
    P.armMean μ P.observedOutcome true - P.armMean μ P.observedOutcome false =
      ∫ ω in P.compliers, P.outcome z true ω - P.outcome z false ω ∂μ := by
  rw [P.armMean_observedOutcome hind (hZ true), P.armMean_observedOutcome hind (hZ false),
    ← integral_sub (P.integrable_outcomeAt hY true) (P.integrable_outcomeAt hY false),
    ← integral_indicator P.measurableSet_compliers]
  congr 1
  funext ω
  have hm := hmono ω
  rw [Bool.le_iff_imp] at hm
  have e0 := hexcl false ω
  have e1 := hexcl true ω
  simp only [outcomeAt, potentials, compliers, type, Set.indicator, Set.mem_ofPred_eq]
  cases z <;> by_cases h0 : P.treatment false ω = true <;>
    by_cases h1 : P.treatment true ω = true <;> simp_all [complianceType]

/-- The local average treatment effect theorem (Imbens & Angrist 1994, Theorem 1; Angrist,
Imbens & Rubin 1996): under independence, exclusion and monotonicity, with integrable potential
outcomes and both arms of positive probability, the Wald estimand is the average treatment
effect among compliers, `𝔼[Y(1) - Y(0) | complier]` (read at either instrument value `z`, which
exclusion makes irrelevant). Relevance, a positive proportion of compliers, is what makes the
two sides meaningful: by `armMean_treated_sub` it is the statement that the Wald denominator is
nonzero. Without it both sides are Lean's junk value `0` (division by `0`, and conditioning on
a null set), so the identity holds but says nothing; the proof does not need it. -/
theorem waldEstimand_eq_late {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hind : P.Independence μ) (hexcl : P.Exclusion) (hmono : P.Monotonicity)
    (hY : ∀ z d, Integrable (P.outcome z d) μ)
    (hZ : ∀ z, μ (P.instrument ⁻¹' {z}) ≠ 0) (z : Bool) :
    P.waldEstimand μ = ∫ ω, P.outcome z true ω - P.outcome z false ω ∂μ[|P.compliers] := by
  rw [waldEstimand, P.armMean_outcome_sub hind hexcl hmono hY hZ z,
    P.armMean_treated_sub hind hmono hZ, ProbabilityTheory.cond, integral_smul_measure,
    smul_eq_mul, ENNReal.toReal_inv, measureReal_def, div_eq_inv_mul]

end PotentialOutcomes

end MathlibExt.Biology.StatisticalGenetics.MendelianRandomization
