/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.SigmoidLogOdds
public import MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Logistic errors-in-variables: slope attenuation and rare-event calibration

A binary outcome `Y` follows a logistic model `P(Y = 1 | X) = σ(α + β X)` in a regressor `X`
that is observed only through `W = X + U`. *Regression calibration* corrects the naive fit of
`Y` on `W` by replacing `X` with its calibrated value `E[X | W]`; when `E[X | W]` is linear in
`W` with slope `ρ`, this divides the naive slope by `ρ`. For the linear model the correction is
exact (`MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables`). For the logistic
model this file proves two weaker results: an exact attenuation-and-deattenuation identity for
the slope in the normal discriminant model, and an approximate regression-calibration bound for
rare events.

**Normal discriminant model: exact slope attenuation.** If, given `Y = y`, `X ~ N(μ_y, v)` and
`U ~ N(0, v_u)` are independent, then `P(Y = 1 | X)` is exactly logistic with slope
`β = (μ₁ - μ₀) / v`, and `P(Y = 1 | W)` is exactly logistic with slope `ρ β`, where
`ρ = v / (v + v_u)` is the (within-class) reliability ratio `attenuationFactor v v_u`. The naive
logistic slope is therefore attenuated by `ρ`, and dividing it by `ρ` recovers `β`
(`logistic_errorsInVariables_attenuation`). This deattenuation is not regression calibration in
the sense above: under the class mixture,
`E[X | W = w] = ρ w + (1 - ρ) (μ₀ + (μ₁ - μ₀) P(Y = 1 | W = w))`, which is not linear in `w`
when `ρ < 1` and `μ₀ ≠ μ₁`, so `E[X | W]` is not `linearCalibration _ ρ` (this formula is not
formalized here). Here `ρ` uses the class-conditional variance `v`, not the marginal variance of
`X`, which also contains the between-class spread `D = p (1 - p) (μ₁ - μ₀)²`. Correcting with
that marginal reliability ratio `(v + D) / (v + D + v_u)` instead gives
`β v (v + v_u + D) / ((v + v_u) (v + D))`, which undercorrects and equals `β` only when
`v_u D β = 0`. The conditional probabilities are stated as versions:
`∫_{W ∈ A} σ(α_W + ρ β W) dP = P(Y = 1, W ∈ A)` for every measurable `A`.

**Rare events: approximate regression calibration.** With the regression-calibration assumption
`X | W = w ~ N(m(w), τ²)`, the log-linear risk `exp (α + β X)`, the rare-event limit of the
logistic risk, induces `E[exp (α + β X) | W = w] = R(w)` with
`R(w) = exp (α + β² τ² / 2 + β m(w))`: for the log-linear risk, regression calibration is exact,
keeping the true slope `β` and shifting only the intercept (`integral_exp_affine_gaussianReal`).
For the logistic risk it is only approximate: `E[σ(α + β X) | W = w]` lies below `R(w)` and
falls short of it by at most `exp (2 α + 2 β² τ² + 2 β m(w)) = R(w)² exp (β² τ²)`, quadratic in
the risk scale up to the variance factor `exp (β² τ²)`
(`exp_sub_integral_sigmoid_affine_gaussianReal_le`). The gap is genuinely nonzero, e.g. `1 / 2`
at `α = β = 0`.

## Main definitions

* `bayesPosterior p f₀ f₁ x`: `p f₁(x) / (p f₁(x) + (1 - p) f₀(x))`.
* `discriminantSlope μ₀ μ₁ v`, `discriminantIntercept p μ₀ μ₁ v`: the logistic coefficients of the
  normal discriminant model.
* `linearCalibration μx ρ w`: the linear calibration function `μx + ρ (w - μx)`.

## Main results

* `bayesPosterior_gaussianPDFReal`: the Gaussian Bayes posterior is
  `σ(discriminantIntercept + discriminantSlope * x)`.
* `setIntegral_bayesPosterior_eq_measureReal_inter`: with Gaussian class-conditional laws of
  equal variance, `bayesPosterior` composed with `Z` is a version of `P(Y = 1 | Z)`.
* `discriminantSlope_add_eq_attenuationFactor_mul`, `abs_discriminantSlope_add_lt`: the slope on
  the mismeasured regressor is `ρ β`, strictly smaller in absolute value when `v_u > 0`.
* `logistic_errorsInVariables_attenuation`: exact logistic models in `X` and in `W`, the
  attenuated slope `ρ β` on `W`, and its deattenuation `(ρ β) / ρ = β`.
* `integral_exp_affine_gaussianReal`, `integral_exp_affine_linearCalibration`: exact
  regression calibration for the log-linear risk.
* `integral_sigmoid_affine_gaussianReal_le`, `exp_sub_integral_sigmoid_affine_gaussianReal_le`:
  the logistic risk is within `R² exp (β² τ²)` below the calibrated log-linear risk `R`.

## References

* R. J. Carroll, D. Ruppert, L. A. Stefanski, C. M. Crainiceanu, *Measurement Error in Nonlinear
  Models*, 2nd ed., Chapman & Hall/CRC (2006), Ch. 4 (regression calibration) and §4.8.
* B. Rosner, D. Spiegelman, W. C. Willett, "Correction of logistic regression relative risk
  estimates and confidence intervals for measurement error", *Am. J. Epidemiol.* 132 (1990).
* T. Hastie, R. Tibshirani, J. Friedman, *The Elements of Statistical Learning*, 2nd ed., §4.4.5
  (logistic regression versus linear discriminant analysis).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables

namespace MathlibExt.Probability.Statistics.ErrorsInVariables.LogisticCalibration

/-! ### Rare-event regression calibration -/

/-- The log-linear risk `exp (α + β x)` is integrable against every real Gaussian law. -/
theorem integrable_exp_affine_gaussianReal (α β m : ℝ) (τ2 : ℝ≥0) :
    Integrable (fun x => exp (α + β * x)) (gaussianReal m τ2) := by
  simp_rw [exp_add α]
  exact (integrable_exp_mul_gaussianReal β).const_mul _

/-- **Regression calibration is exact for the log-linear risk.** If `X | W = w ~ N(m, τ²)`, then
`E[exp (α + β X) | W = w] = exp (α + β² τ² / 2 + β m)`: in the calibrated covariate `m` the
induced risk is log-linear with the same slope `β`, and only the intercept moves, by
`β² τ² / 2`. -/
theorem integral_exp_affine_gaussianReal (α β m : ℝ) (τ2 : ℝ≥0) :
    ∫ x, exp (α + β * x) ∂gaussianReal m τ2 = exp (α + β ^ 2 * τ2 / 2 + β * m) := by
  have h := mgf_gaussianReal (X := id) (p := gaussianReal m τ2) (μ := m) (v := τ2)
    (by simp [HasLaw.id]) β
  simp only [mgf, id] at h
  simp_rw [exp_add α, integral_const_mul]
  simp_rw [mul_comm β] at h ⊢
  rw [h, exp_add, exp_add, exp_add]
  ring_nf

/-- The **linear calibration function** `E[X | W = w] = μx + ρ (w - μx)`, for the mean `μx` of
`X` and the reliability ratio `ρ`. In the classical Gaussian model `X ~ N(μx, σ_x²)`,
`W = X + U`, `U ~ N(0, σ_u²)`, the ratio is `ρ = attenuationFactor σ_x² σ_u²`. -/
noncomputable def linearCalibration (μx ρ w : ℝ) : ℝ :=
  μx + ρ * (w - μx)

/-- **Rare-event calibration with a linear calibration function.** If
`X | W = w ~ N(μx + ρ (w - μx), τ²)`, the log-linear risk induces a log-linear model in `w` with
the attenuated slope `ρ β`; regressing on the calibrated covariate `linearCalibration μx ρ w`
instead recovers the slope `β` (`integral_exp_affine_gaussianReal`). -/
theorem integral_exp_affine_linearCalibration (α β μx ρ w : ℝ) (τ2 : ℝ≥0) :
    ∫ x, exp (α + β * x) ∂gaussianReal (linearCalibration μx ρ w) τ2 =
      exp ((α + β ^ 2 * τ2 / 2 + β * (1 - ρ) * μx) + ρ * β * w) := by
  rw [integral_exp_affine_gaussianReal, linearCalibration]
  ring_nf

/-- `σ(α + β x)` is integrable against every finite measure. -/
theorem integrable_sigmoid_affine (α β : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun x => sigmoid (α + β * x)) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (sigmoid_pos _)]
  exact sigmoid_le_one _

/-- The logistic function lies below the exponential. -/
theorem sigmoid_le_exp (t : ℝ) : sigmoid t ≤ exp t := by
  have he := exp_pos t
  rw [sigmoid_def, exp_neg, inv_le_iff_one_le_mul₀ (by positivity), mul_add,
    mul_inv_cancel₀ he.ne']
  linarith

/-- The gap between the exponential and the logistic function is at most `exp (2 t)`. -/
theorem exp_sub_sigmoid_le (t : ℝ) : exp t - sigmoid t ≤ exp (2 * t) := by
  have he := exp_pos t
  have hd : exp t - sigmoid t = exp t ^ 2 / (1 + exp t) := by
    rw [sigmoid_def, exp_neg]
    field_simp
    ring
  rw [hd, show 2 * t = t + t by ring, exp_add, ← sq]
  exact div_le_self (by positivity) (by linarith)

/-- If `X | W = w ~ N(m, τ²)`, the induced logistic risk `E[σ(α + β X) | W = w]` is at most the
calibrated log-linear risk `exp (α + β² τ² / 2 + β m)`. -/
theorem integral_sigmoid_affine_gaussianReal_le (α β m : ℝ) (τ2 : ℝ≥0) :
    ∫ x, sigmoid (α + β * x) ∂gaussianReal m τ2 ≤ exp (α + β ^ 2 * τ2 / 2 + β * m) := by
  rw [← integral_exp_affine_gaussianReal]
  exact integral_mono (integrable_sigmoid_affine _ _ _)
    (integrable_exp_affine_gaussianReal _ _ _ _) fun x => sigmoid_le_exp _

/-- **Rare-event regression calibration for the logistic model is approximate.** If
`X | W = w ~ N(m, τ²)`, the induced logistic risk `E[σ(α + β X) | W = w]` falls short of the
calibrated log-linear risk `R = exp (α + β² τ² / 2 + β m)`, whose slope in `m` is the true `β`,
by at most `exp (2 α + 2 β² τ² + 2 β m) = R² exp (β² τ²)`: the error is quadratic in the risk
scale up to the variance factor `exp (β² τ²)`. -/
theorem exp_sub_integral_sigmoid_affine_gaussianReal_le (α β m : ℝ) (τ2 : ℝ≥0) :
    exp (α + β ^ 2 * τ2 / 2 + β * m) - ∫ x, sigmoid (α + β * x) ∂gaussianReal m τ2 ≤
      exp (2 * α + 2 * β ^ 2 * τ2 + 2 * β * m) := by
  have h2 := integral_exp_affine_gaussianReal (2 * α) (2 * β) m τ2
  rw [show 2 * α + (2 * β) ^ 2 * (τ2 : ℝ) / 2 + 2 * β * m =
    2 * α + 2 * β ^ 2 * τ2 + 2 * β * m by ring] at h2
  rw [← integral_exp_affine_gaussianReal, ← h2,
    ← integral_sub (integrable_exp_affine_gaussianReal _ _ _ _) (integrable_sigmoid_affine _ _ _)]
  refine integral_mono ((integrable_exp_affine_gaussianReal _ _ _ _).sub
    (integrable_sigmoid_affine _ _ _)) (integrable_exp_affine_gaussianReal _ _ _ _) fun x => ?_
  simp only
  rw [show 2 * α + 2 * β * x = 2 * (α + β * x) by ring]
  exact exp_sub_sigmoid_le _

/-! ### The normal discriminant model -/

/-- The **Bayes posterior** `P(Y = 1 | X = x) = p f₁(x) / (p f₁(x) + (1 - p) f₀(x))` for the prior
`p = P(Y = 1)` and class-conditional densities `f₀`, `f₁`. -/
noncomputable def bayesPosterior (p : ℝ) (f₀ f₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  p * f₁ x / (p * f₁ x + (1 - p) * f₀ x)

/-- The **logistic slope of the normal discriminant model**, `(μ₁ - μ₀) / v`, for class means
`μ₀`, `μ₁` and common variance `v`. -/
noncomputable def discriminantSlope (μ₀ μ₁ v : ℝ) : ℝ :=
  (μ₁ - μ₀) / v

/-- The **logistic intercept of the normal discriminant model**,
`log (p / (1 - p)) - (μ₁ - μ₀) / v * (μ₀ + μ₁) / 2`. -/
noncomputable def discriminantIntercept (p μ₀ μ₁ v : ℝ) : ℝ :=
  log (p / (1 - p)) - discriminantSlope μ₀ μ₁ v * ((μ₀ + μ₁) / 2)

/-- **The Gaussian Bayes posterior is logistic.** For a prior `p ∈ (0, 1)` and class-conditional
laws `N(μ₀, v)`, `N(μ₁, v)` with `v ≠ 0`, `P(Y = 1 | X = x) = σ(α + β x)` with
`β = discriminantSlope μ₀ μ₁ v` and `α = discriminantIntercept p μ₀ μ₁ v`. -/
theorem bayesPosterior_gaussianPDFReal {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) (μ₀ μ₁ : ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    bayesPosterior p (gaussianPDFReal μ₀ v) (gaussianPDFReal μ₁ v) x =
      sigmoid (discriminantIntercept p μ₀ μ₁ v + discriminantSlope μ₀ μ₁ v * x) := by
  have hq : 0 < 1 - p := by linarith
  have hc : 0 < (√(2 * π * v))⁻¹ := by
    have := gaussianPDFReal_pos μ₀ v x hv
    rw [gaussianPDFReal] at this
    exact pos_of_mul_pos_left this (exp_pos _).le
  rw [bayesPosterior, ← sigmoid_log_sub_log (mul_pos hp₀ (gaussianPDFReal_pos _ _ _ hv))
    (mul_pos hq (gaussianPDFReal_pos _ _ _ hv))]
  congr 1
  simp only [gaussianPDFReal]
  rw [log_mul hp₀.ne' (by positivity), log_mul hq.ne' (by positivity),
    log_mul hc.ne' (by positivity), log_mul hc.ne' (by positivity), log_exp, log_exp,
    discriminantIntercept, discriminantSlope, log_div hp₀.ne' hq.ne']
  field_simp
  ring

/-- Clearing the denominator of `bayesPosterior`. -/
theorem bayesPosterior_mul_add {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) {f₀ f₁ : ℝ → ℝ} {x : ℝ}
    (h₀ : 0 < f₀ x) (h₁ : 0 < f₁ x) :
    bayesPosterior p f₀ f₁ x * (p * f₁ x + (1 - p) * f₀ x) = p * f₁ x := by
  have : 0 < p * f₁ x + (1 - p) * f₀ x := by
    have := mul_pos hp₀ h₁
    have := mul_pos (sub_pos.2 hp₁) h₀
    linarith
  rw [bayesPosterior, div_mul_cancel₀ _ this.ne']

/-- A set integral against a non-degenerate real Gaussian law, as a Lebesgue integral against its
density. -/
theorem setIntegral_gaussianReal_eq {m : ℝ} {s : ℝ≥0} (hs : s ≠ 0) {A : Set ℝ}
    (hA : MeasurableSet A) (g : ℝ → ℝ) :
    ∫ x in A, g x ∂gaussianReal m s = ∫ x, gaussianPDFReal m s x * A.indicator g x := by
  rw [← integral_indicator hA, integral_gaussianReal_eq_integral_smul hs]
  rfl

/-- **The Bayes posterior integrates the mixture correctly**: against the mixture
`p N(m₁, s) + (1 - p) N(m₀, s)`, the integral of the posterior over `A` is `p N(m₁, s)(A)`. -/
theorem bayesPosterior_gaussian_mixture {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) (m₀ m₁ : ℝ)
    {s : ℝ≥0} (hs : s ≠ 0) {A : Set ℝ} (hA : MeasurableSet A) :
    p * ∫ x in A, bayesPosterior p (gaussianPDFReal m₀ s) (gaussianPDFReal m₁ s) x
        ∂gaussianReal m₁ s +
      (1 - p) * ∫ x in A, bayesPosterior p (gaussianPDFReal m₀ s) (gaussianPDFReal m₁ s) x
        ∂gaussianReal m₀ s = p * (gaussianReal m₁ s).real A := by
  set q := bayesPosterior p (gaussianPDFReal m₀ s) (gaussianPDFReal m₁ s) with hq
  have hqσ : q = fun x => sigmoid (discriminantIntercept p m₀ m₁ s +
      discriminantSlope m₀ m₁ s * x) := funext (bayesPosterior_gaussianPDFReal hp₀ hp₁ m₀ m₁ hs)
  have hqm : Measurable q := by rw [hqσ]; fun_prop
  have hint : ∀ m : ℝ, Integrable (fun x => gaussianPDFReal m s x * A.indicator q x) := by
    intro m
    refine (integrable_gaussianPDFReal m s).mono'
      ((measurable_gaussianPDFReal m s).mul (hqm.indicator hA)).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    have hq01 : |A.indicator q x| ≤ 1 := by
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, hqσ, abs_of_pos (sigmoid_pos _)]
        exact sigmoid_le_one _
      · simp [hx]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact mul_le_of_le_one_right (gaussianPDFReal_nonneg _ _ _) hq01
  rw [setIntegral_gaussianReal_eq hs hA, setIntegral_gaussianReal_eq hs hA,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint m₁).const_mul p) ((hint m₀).const_mul (1 - p))]
  have h1 : (gaussianReal m₁ s).real A = ∫ x in A, (fun _ => (1 : ℝ)) x ∂gaussianReal m₁ s := by
    simp
  rw [h1, setIntegral_gaussianReal_eq hs hA, ← integral_const_mul]
  congr 1
  funext x
  by_cases hx : x ∈ A
  · simp only [Set.indicator_of_mem hx]
    have := bayesPosterior_mul_add hp₀ hp₁ (gaussianPDFReal_pos m₀ s x hs)
      (gaussianPDFReal_pos m₁ s x hs) (f₀ := gaussianPDFReal m₀ s) (f₁ := gaussianPDFReal m₁ s)
    rw [← hq] at this
    simp only [mul_one]
    linear_combination this
  · simp [hx]

/-- **The Bayes posterior is a version of `P(Y = 1 | Z)`.** Let `Y` be a binary label with
`p = P(Y = 1) ∈ (0, 1)`, and let `Z` have law `N(m_y, s)`, `s ≠ 0`, conditionally on `Y = y`.
Then for every measurable `A`, `∫_{Z ∈ A} q(Z) dP = P(Y = 1, Z ∈ A)` for
`q = bayesPosterior p (gaussianPDFReal m₀ s) (gaussianPDFReal m₁ s)`. -/
theorem setIntegral_bayesPosterior_eq_measureReal_inter {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → Bool} {Z : Ω → ℝ}
    (hY : Measurable Y) (hZ : Measurable Z)
    (hp₀ : 0 < P.real (Y ⁻¹' {true})) (hp₁ : P.real (Y ⁻¹' {true}) < 1)
    {m₀ m₁ : ℝ} {s : ℝ≥0} (hs : s ≠ 0)
    (h₀ : HasLaw Z (gaussianReal m₀ s) P[|Y ⁻¹' {false}])
    (h₁ : HasLaw Z (gaussianReal m₁ s) P[|Y ⁻¹' {true}])
    {A : Set ℝ} (hA : MeasurableSet A) :
    ∫ ω in Z ⁻¹' A, bayesPosterior (P.real (Y ⁻¹' {true})) (gaussianPDFReal m₀ s)
        (gaussianPDFReal m₁ s) (Z ω) ∂P = P.real (Y ⁻¹' {true} ∩ Z ⁻¹' A) := by
  set p := P.real (Y ⁻¹' {true}) with hp
  set q := bayesPosterior p (gaussianPDFReal m₀ s) (gaussianPDFReal m₁ s) with hq
  have hqσ : q = fun x => sigmoid (discriminantIntercept p m₀ m₁ s +
      discriminantSlope m₀ m₁ s * x) := funext (bayesPosterior_gaussianPDFReal hp₀ hp₁ m₀ m₁ hs)
  have hqm : Measurable q := by rw [hqσ]; fun_prop
  have hfalse : P.real (Y ⁻¹' {false}) = 1 - p := by
    have : Y ⁻¹' {false} = (Y ⁻¹' {true})ᶜ := by ext; simp
    rw [this, probReal_compl_eq_one_sub (hY (measurableSet_singleton _))]
  have hdecomp : P = P (Y ⁻¹' {true}) • P[|Y ⁻¹' {true}] +
      P (Y ⁻¹' {false}) • P[|Y ⁻¹' {false}] := by
    conv_lhs => rw [← sum_meas_smul_cond_fiber hY P]
    rw [Fintype.sum_bool]
  have hcond : ∀ (y : Bool) (m : ℝ), HasLaw Z (gaussianReal m s) P[|Y ⁻¹' {y}] →
      ∫ ω in Z ⁻¹' A, q (Z ω) ∂P[|Y ⁻¹' {y}] = ∫ x in A, q x ∂gaussianReal m s := by
    intro y m h
    rw [← h.map_eq, setIntegral_map hA hqm.aestronglyMeasurable hZ.aemeasurable]
  have hintc : ∀ y : Bool,
      Integrable (fun ω => q (Z ω)) ((P[|Y ⁻¹' {y}]).restrict (Z ⁻¹' A)) := by
    intro y
    rw [hqσ]
    exact (integrable_sigmoid_affine _ _ _).comp_measurable hZ |>.mono_measure le_rfl
  have hRHS : P.real (Y ⁻¹' {true} ∩ Z ⁻¹' A) = p * (gaussianReal m₁ s).real A := by
    rw [← h₁.map_eq, map_measureReal_apply hZ hA, hp, measureReal_def, measureReal_def,
      measureReal_def, ← ENNReal.toReal_mul, mul_comm (P _),
      cond_mul_eq_inter (hY (measurableSet_singleton _))]
  rw [hRHS, ← bayesPosterior_gaussian_mixture hp₀ hp₁ m₀ m₁ hs hA, ← hcond true m₁ h₁,
    ← hcond false m₀ h₀, ← hfalse]
  conv_lhs => rw [hdecomp]
  rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
    integral_add_measure ((hintc true).smul_measure (measure_ne_top _ _))
      ((hintc false).smul_measure (measure_ne_top _ _)),
    integral_smul_measure, integral_smul_measure]
  simp only [smul_eq_mul, hp, measureReal_def]

/-! ### Attenuation and its correction -/

/-- **Attenuation of the logistic slope**: adding independent measurement error of variance `vu`
to the class-conditional variance `v` multiplies the discriminant slope by the reliability ratio
`attenuationFactor v vu = v / (v + vu)`. -/
theorem discriminantSlope_add_eq_attenuationFactor_mul (μ₀ μ₁ : ℝ) {v vu : ℝ} (hv : v ≠ 0) :
    discriminantSlope μ₀ μ₁ (v + vu) = attenuationFactor v vu * discriminantSlope μ₀ μ₁ v := by
  rw [discriminantSlope, discriminantSlope, attenuationFactor]
  field_simp

/-- **The naive slope is biased toward zero**: for `v, vu > 0` and distinct class means, the slope
on the mismeasured regressor is strictly smaller in absolute value. -/
theorem abs_discriminantSlope_add_lt (μ₀ μ₁ : ℝ) (hμ : μ₀ ≠ μ₁) {v vu : ℝ} (hv : 0 < v)
    (hvu : 0 < vu) : |discriminantSlope μ₀ μ₁ (v + vu)| < |discriminantSlope μ₀ μ₁ v| := by
  rw [discriminantSlope, discriminantSlope, abs_div, abs_div, abs_of_pos hv,
    abs_of_pos (by linarith : 0 < v + vu)]
  exact div_lt_div_of_pos_left (abs_pos.2 (sub_ne_zero.2 hμ.symm)) hv (by linarith)

/-- The true and the naive logistic lines cross where the log odds equal the prior log odds,
at the midpoint `(μ₀ + μ₁) / 2` of the class means, whatever the variance. -/
theorem discriminantIntercept_add_slope_mul_midpoint (p μ₀ μ₁ v : ℝ) :
    discriminantIntercept p μ₀ μ₁ v + discriminantSlope μ₀ μ₁ v * ((μ₀ + μ₁) / 2) =
      log (p / (1 - p)) := by
  rw [discriminantIntercept]
  ring

/-- **Slope attenuation for logistic errors-in-variables.** Let `Y` be a binary label with
`p = P(Y = 1) ∈ (0, 1)`. Given `Y = y`, let the true regressor `X ~ N(μ_y, v)` (`v ≠ 0`) and the
measurement error `U ~ N(0, vu)` be independent, and observe `W = X + U`. With
`β = discriminantSlope μ₀ μ₁ v` and `ρ = attenuationFactor v vu`:

1. `P(Y = 1 | X) = σ(discriminantIntercept p μ₀ μ₁ v + β X)`, an exact logistic model in `X`;
2. `P(Y = 1 | W) = σ(discriminantIntercept p μ₀ μ₁ (v + vu) + ρ β W)`, an exact logistic model in
   `W` whose slope is attenuated by `ρ`;
3. dividing the naive slope `ρ β` by the within-class reliability ratio `ρ` recovers `β`.

Items 1 and 2 are stated as versions of the conditional probabilities: their integrals over
`{X ∈ A}`, respectively `{W ∈ A}`, are `P(Y = 1, X ∈ A)`, respectively `P(Y = 1, W ∈ A)`.

Item 3 is slope deattenuation, not regression calibration: `E[X | W]` is not linear in `W` for
this mixture (see the module docstring). -/
theorem logistic_errorsInVariables_attenuation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → Bool} {X U : Ω → ℝ}
    (hY : Measurable Y) (hX : Measurable X) (hU : Measurable U)
    (hp₀ : 0 < P.real (Y ⁻¹' {true})) (hp₁ : P.real (Y ⁻¹' {true}) < 1)
    {μ₀ μ₁ : ℝ} {v vu : ℝ≥0} (hv : v ≠ 0)
    (hX₀ : HasLaw X (gaussianReal μ₀ v) P[|Y ⁻¹' {false}])
    (hX₁ : HasLaw X (gaussianReal μ₁ v) P[|Y ⁻¹' {true}])
    (hU₀ : HasLaw U (gaussianReal 0 vu) P[|Y ⁻¹' {false}])
    (hU₁ : HasLaw U (gaussianReal 0 vu) P[|Y ⁻¹' {true}])
    (hXU₀ : IndepFun X U P[|Y ⁻¹' {false}]) (hXU₁ : IndepFun X U P[|Y ⁻¹' {true}]) :
    let p := P.real (Y ⁻¹' {true})
    let β := discriminantSlope μ₀ μ₁ v
    let ρ := attenuationFactor v vu
    (∀ A : Set ℝ, MeasurableSet A →
      ∫ ω in X ⁻¹' A, sigmoid (discriminantIntercept p μ₀ μ₁ v + β * X ω) ∂P =
        P.real (Y ⁻¹' {true} ∩ X ⁻¹' A)) ∧
    (∀ A : Set ℝ, MeasurableSet A →
      ∫ ω in (X + U) ⁻¹' A,
          sigmoid (discriminantIntercept p μ₀ μ₁ (v + vu) + ρ * β * (X + U) ω) ∂P =
        P.real (Y ⁻¹' {true} ∩ (X + U) ⁻¹' A)) ∧
    discriminantSlope μ₀ μ₁ (v + vu) / ρ = β := by
  intro p β ρ
  have hvu : v + vu ≠ 0 := (add_pos_of_pos_of_nonneg (pos_iff_ne_zero.2 hv) vu.2).ne'
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hvvu : (v : ℝ) + vu ≠ 0 := by
    have : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm hv')
    positivity
  have hslope : discriminantSlope μ₀ μ₁ (v + vu) = ρ * β :=
    discriminantSlope_add_eq_attenuationFactor_mul μ₀ μ₁ hv'
  have hρ : ρ ≠ 0 := div_ne_zero hv' hvvu
  have hW : ∀ (y : Bool) (m : ℝ), HasLaw X (gaussianReal m v) P[|Y ⁻¹' {y}] →
      HasLaw U (gaussianReal 0 vu) P[|Y ⁻¹' {y}] → IndepFun X U P[|Y ⁻¹' {y}] →
      HasLaw (X + U) (gaussianReal m (v + vu)) P[|Y ⁻¹' {y}] := by
    intro y m hXy hUy hXUy
    refine ⟨hXy.aemeasurable.add hUy.aemeasurable, ?_⟩
    rw [gaussianReal_add_gaussianReal_of_indepFun hXUy hXy hUy, add_zero]
  refine ⟨fun A hA => ?_, fun A hA => ?_, ?_⟩
  · rw [← setIntegral_bayesPosterior_eq_measureReal_inter hY hX hp₀ hp₁ hv hX₀ hX₁ hA]
    simp_rw [bayesPosterior_gaussianPDFReal hp₀ hp₁ μ₀ μ₁ hv]
    rfl
  · rw [← setIntegral_bayesPosterior_eq_measureReal_inter hY (hX.add hU) hp₀ hp₁ hvu
      (hW false μ₀ hX₀ hU₀ hXU₀) (hW true μ₁ hX₁ hU₁ hXU₁) hA]
    simp_rw [bayesPosterior_gaussianPDFReal hp₀ hp₁ μ₀ μ₁ hvu, NNReal.coe_add, hslope]
    rfl
  · rw [hslope, mul_div_cancel_left₀ _ hρ]

end MathlibExt.Probability.Statistics.ErrorsInVariables.LogisticCalibration
