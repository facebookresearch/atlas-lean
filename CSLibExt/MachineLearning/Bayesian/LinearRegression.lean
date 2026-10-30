/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.NormalNormal
public import MathlibExt.MeasureTheory.Measure.PiWithDensity

/-!
# Bayesian linear regression with one feature

Scope: a scalar weight `w` (the 1-D case, regression through the origin) with a `N(m₀, s₀)` prior,
and `n` responses that are independent given `w`, `yᵢ ~ N(w xᵢ, σ²)`, with the inputs `x` fixed
and the noise variance `σ²` known. The likelihood `linRegLikelihood σ2 x` is the product
`Measure.pi fun i ↦ gaussianReal (w * x i) σ2` (`linRegLikelihood_apply`, through MathlibExt's
`Measure.pi_withDensity`).

* `gaussianPDFReal_mul_linRegLikelihoodPDFReal` (**completing the square**): with
  `Sxx = ∑ xᵢ²` and `Sxy = ∑ xᵢ yᵢ`, prior density times likelihood is a function of `y` times
  the Gaussian density with the posterior mean and variance.
* `posterior_linRegLikelihood_gaussianReal` (**Gaussian posterior**): for almost every response
  vector `y`, Mathlib's posterior kernel `κ†μ` at `y` is the Gaussian with
  * mean `linRegPostMean = (σ² m₀ + s₀ Sxy) / (σ² + s₀ Sxx)`, and
  * variance `linRegPostVar = s₀ σ² / (σ² + s₀ Sxx)`.
  The proof feeds the completed square to Bayes' rule for densities
  (`posterior_ae_eq_of_mul_eq`).
* `inv_linRegPostVar`: precisions add, `1 / linRegPostVar = 1 / s₀ + Sxx / σ²`.
* `linRegLikelihood_comp_gaussianReal`: the evidence has density `linRegEvidencePDFReal`.
* `linRegPredictive_comp_posterior` (**posterior predictive**): the response at a new input
  `x'` is `N(x' m, x'² v + σ²)`, with `m` and `v` the posterior mean and variance.

With `n = 1` and `x = 1` this is the Normal–Normal model of
`CSLibExt/MachineLearning/Bayesian/NormalNormal.lean`. Several features with an isotropic prior
would need the multivariate Gaussian and are not treated here.

## References

* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §3.3.1–3.3.2.
* K. P. Murphy, *Probabilistic Machine Learning: An Introduction*, MIT Press, 2022, Chapter 11
  (Bayesian linear regression).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Bayesian

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

variable {n : ℕ}

/-- The posterior variance `s₀ σ² / (σ² + s₀ ∑ xᵢ²)` of the weight. -/
noncomputable def linRegPostVar (s₀ σ2 : ℝ≥0) (x : Fin n → ℝ) : ℝ≥0 :=
  s₀ * σ2 / (σ2 + s₀ * (∑ i, x i ^ 2).toNNReal)

/-- The posterior mean `(σ² m₀ + s₀ ∑ xᵢ yᵢ) / (σ² + s₀ ∑ xᵢ²)` of the weight. -/
noncomputable def linRegPostMean (m₀ : ℝ) (s₀ σ2 : ℝ≥0) (x y : Fin n → ℝ) : ℝ :=
  (σ2 * m₀ + s₀ * ∑ i, x i * y i) / (σ2 + s₀ * ∑ i, x i ^ 2)

theorem coe_toNNReal_sum_sq (x : Fin n → ℝ) : ((∑ i, x i ^ 2).toNNReal : ℝ) = ∑ i, x i ^ 2 :=
  Real.coe_toNNReal _ (sum_nonneg fun i _ ↦ sq_nonneg (x i))

theorem coe_linRegPostVar (s₀ σ2 : ℝ≥0) (x : Fin n → ℝ) :
    (linRegPostVar s₀ σ2 x : ℝ) = s₀ * σ2 / (σ2 + s₀ * ∑ i, x i ^ 2) := by
  rw [linRegPostVar, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_mul,
    coe_toNNReal_sum_sq]

theorem linRegPostVar_ne_zero {s₀ σ2 : ℝ≥0} (h₀ : s₀ ≠ 0) (h : σ2 ≠ 0) (x : Fin n → ℝ) :
    linRegPostVar s₀ σ2 x ≠ 0 := by
  unfold linRegPostVar
  have : σ2 + s₀ * (∑ i, x i ^ 2).toNNReal ≠ 0 := by positivity
  positivity

/-- Precisions add: `1 / linRegPostVar = 1 / s₀ + ∑ xᵢ² / σ²`. -/
theorem inv_linRegPostVar {s₀ σ2 : ℝ≥0} (h₀ : s₀ ≠ 0) (h : σ2 ≠ 0) (x : Fin n → ℝ) :
    ((linRegPostVar s₀ σ2 x : ℝ))⁻¹ = (s₀ : ℝ)⁻¹ + (∑ i, x i ^ 2) / σ2 := by
  have hs : (0 : ℝ) < s₀ := by positivity
  have hσ : (0 : ℝ) < σ2 := by positivity
  have hx : 0 ≤ ∑ i, x i ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg (x i)
  rw [coe_linRegPostVar]
  field_simp

/-- The product `∏ φ(yᵢ; w xᵢ, σ²)` of Gaussian densities. For `σ² ≠ 0` it is the Lebesgue density
of the data `y` given the weight `w` (independent `yᵢ ~ N(w xᵢ, σ²)`). With no data (`n = 0`) it
is the empty product `1`, the density of the unit mass on the single empty response. For `σ² = 0`
and `n > 0` the responses are deterministic and have no density, and this formula is `0`. -/
noncomputable def linRegLikelihoodPDFReal (σ2 : ℝ≥0) (x : Fin n → ℝ) (w : ℝ) (y : Fin n → ℝ) :
    ℝ :=
  ∏ i, gaussianPDFReal (w * x i) σ2 (y i)

theorem linRegLikelihoodPDFReal_eq (σ2 : ℝ≥0) (x : Fin n → ℝ) (w : ℝ) (y : Fin n → ℝ) :
    linRegLikelihoodPDFReal σ2 x w y =
      (√(2 * π * σ2))⁻¹ ^ n * rexp (-(∑ i, (y i - w * x i) ^ 2) / (2 * σ2)) := by
  simp only [linRegLikelihoodPDFReal, gaussianPDFReal, prod_mul_distrib, prod_const, card_univ,
    Fintype.card_fin, ← Real.exp_sum, neg_div, sum_neg_distrib, ← sum_div]

/-- **Completing the square for linear regression.** With the constant
`C y = p(m) L(y | m) / r_y(m)` at the posterior mean `m`, prior density times likelihood is
`C y` times the posterior density, for every weight `w`. -/
theorem gaussianPDFReal_mul_linRegLikelihoodPDFReal (m₀ : ℝ) {s₀ σ2 : ℝ≥0} (h₀ : s₀ ≠ 0)
    (h : σ2 ≠ 0) (x : Fin n → ℝ) (w : ℝ) (y : Fin n → ℝ) :
    gaussianPDFReal m₀ s₀ w * linRegLikelihoodPDFReal σ2 x w y *
        gaussianPDFReal (linRegPostMean m₀ s₀ σ2 x y) (linRegPostVar s₀ σ2 x)
          (linRegPostMean m₀ s₀ σ2 x y) =
      gaussianPDFReal m₀ s₀ (linRegPostMean m₀ s₀ σ2 x y) *
          linRegLikelihoodPDFReal σ2 x (linRegPostMean m₀ s₀ σ2 x y) y *
        gaussianPDFReal (linRegPostMean m₀ s₀ σ2 x y) (linRegPostVar s₀ σ2 x) w := by
  have hs : (0 : ℝ) < s₀ := by positivity
  have hσ : (0 : ℝ) < σ2 := by positivity
  have hx : 0 ≤ ∑ i, x i ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg (x i)
  have hD : (0 : ℝ) < σ2 + s₀ * ∑ i, x i ^ 2 := by positivity
  have hsum : ∀ v : ℝ, ∑ i, (y i - v * x i) ^ 2 =
      ∑ i, y i ^ 2 - 2 * v * ∑ i, x i * y i + v ^ 2 * ∑ i, x i ^ 2 := fun v ↦ by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_sum]
    congr 1
    · congr 1
      exact sum_congr rfl fun i _ ↦ by ring
    · exact sum_congr rfl fun i _ ↦ by ring
  simp only [linRegLikelihoodPDFReal_eq, gaussianPDFReal, hsum, coe_linRegPostVar]
  set m := linRegPostMean m₀ s₀ σ2 x y with hm
  set Sxx := ∑ i, x i ^ 2
  set Sxy := ∑ i, x i * y i
  set Syy := ∑ i, y i ^ 2
  have hexp : -(w - m₀) ^ 2 / (2 * s₀) + -(Syy - 2 * w * Sxy + w ^ 2 * Sxx) / (2 * σ2) +
      -(m - m) ^ 2 / (2 * (s₀ * σ2 / (σ2 + s₀ * Sxx))) =
      -(m - m₀) ^ 2 / (2 * s₀) + -(Syy - 2 * m * Sxy + m ^ 2 * Sxx) / (2 * σ2) +
      -(w - m) ^ 2 / (2 * (s₀ * σ2 / (σ2 + s₀ * Sxx))) := by
    rw [hm, linRegPostMean]
    field_simp
    ring
  calc _ = ((√(2 * π * s₀))⁻¹ * (√(2 * π * σ2))⁻¹ ^ n *
        (√(2 * π * (s₀ * σ2 / (σ2 + s₀ * Sxx))))⁻¹) *
        rexp (-(w - m₀) ^ 2 / (2 * s₀) + -(Syy - 2 * w * Sxy + w ^ 2 * Sxx) / (2 * σ2) +
          -(m - m) ^ 2 / (2 * (s₀ * σ2 / (σ2 + s₀ * Sxx)))) := by
          rw [Real.exp_add, Real.exp_add]; ring
    _ = ((√(2 * π * s₀))⁻¹ * (√(2 * π * σ2))⁻¹ ^ n *
        (√(2 * π * (s₀ * σ2 / (σ2 + s₀ * Sxx))))⁻¹) *
        rexp (-(m - m₀) ^ 2 / (2 * s₀) + -(Syy - 2 * m * Sxy + m ^ 2 * Sxx) / (2 * σ2) +
          -(w - m) ^ 2 / (2 * (s₀ * σ2 / (σ2 + s₀ * Sxx)))) := by rw [hexp]
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

theorem linRegLikelihoodPDFReal_pos {σ2 : ℝ≥0} (h : σ2 ≠ 0) (x : Fin n → ℝ) (w : ℝ)
    (y : Fin n → ℝ) : 0 < linRegLikelihoodPDFReal σ2 x w y :=
  prod_pos fun _ _ ↦ gaussianPDFReal_pos _ _ _ h

/-- Prior times likelihood divided by the posterior density, evaluated at the posterior mean,
where the ratio does not depend on the weight. For `s₀ ≠ 0` and `σ² ≠ 0` this is the evidence
density, the Lebesgue density of the marginal law of the data
(`linRegLikelihood_comp_gaussianReal`). It is not a density of the evidence in the degenerate
cases. -/
noncomputable def linRegEvidencePDFReal (m₀ : ℝ) (s₀ σ2 : ℝ≥0) (x y : Fin n → ℝ) : ℝ :=
  gaussianPDFReal m₀ s₀ (linRegPostMean m₀ s₀ σ2 x y) *
      linRegLikelihoodPDFReal σ2 x (linRegPostMean m₀ s₀ σ2 x y) y /
    gaussianPDFReal (linRegPostMean m₀ s₀ σ2 x y) (linRegPostVar s₀ σ2 x)
      (linRegPostMean m₀ s₀ σ2 x y)

theorem linRegEvidencePDFReal_pos (m₀ : ℝ) {s₀ σ2 : ℝ≥0} (h₀ : s₀ ≠ 0) (h : σ2 ≠ 0)
    (x y : Fin n → ℝ) : 0 < linRegEvidencePDFReal m₀ s₀ σ2 x y := by
  unfold linRegEvidencePDFReal
  have := gaussianPDFReal_pos m₀ s₀ (linRegPostMean m₀ s₀ σ2 x y) h₀
  have := linRegLikelihoodPDFReal_pos h x (linRegPostMean m₀ s₀ σ2 x y) y
  have := gaussianPDFReal_pos (linRegPostMean m₀ s₀ σ2 x y) (linRegPostVar s₀ σ2 x)
    (linRegPostMean m₀ s₀ σ2 x y) (linRegPostVar_ne_zero h₀ h x)
  positivity

/-- Prior density times likelihood is the evidence density times the posterior density. -/
theorem gaussianPDFReal_mul_linRegLikelihoodPDFReal' (m₀ : ℝ) {s₀ σ2 : ℝ≥0} (h₀ : s₀ ≠ 0)
    (h : σ2 ≠ 0) (x : Fin n → ℝ) (w : ℝ) (y : Fin n → ℝ) :
    gaussianPDFReal m₀ s₀ w * linRegLikelihoodPDFReal σ2 x w y =
      linRegEvidencePDFReal m₀ s₀ σ2 x y *
        gaussianPDFReal (linRegPostMean m₀ s₀ σ2 x y) (linRegPostVar s₀ σ2 x) w := by
  have hr := gaussianPDFReal_pos (linRegPostMean m₀ s₀ σ2 x y) (linRegPostVar s₀ σ2 x)
    (linRegPostMean m₀ s₀ σ2 x y) (linRegPostVar_ne_zero h₀ h x)
  rw [linRegEvidencePDFReal, div_mul_eq_mul_div, eq_div_iff hr.ne',
    gaussianPDFReal_mul_linRegLikelihoodPDFReal m₀ h₀ h]

/-! ### The likelihood kernel -/

/-- `linRegLikelihoodPDFReal` as an extended nonnegative real: the likelihood density for
`σ² ≠ 0` or `n = 0`, and `0` for `σ² = 0` and `n > 0`. -/
noncomputable def linRegLikelihoodPDF (σ2 : ℝ≥0) (x : Fin n → ℝ) (w : ℝ) (y : Fin n → ℝ) :
    ℝ≥0∞ :=
  ∏ i, gaussianPDF (w * x i) σ2 (y i)

theorem linRegLikelihoodPDF_eq (σ2 : ℝ≥0) (x : Fin n → ℝ) (w : ℝ) (y : Fin n → ℝ) :
    linRegLikelihoodPDF σ2 x w y = ENNReal.ofReal (linRegLikelihoodPDFReal σ2 x w y) := by
  rw [linRegLikelihoodPDF, linRegLikelihoodPDFReal,
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ gaussianPDFReal_nonneg _ _ _]
  rfl

theorem measurable_linRegLikelihoodPDF (σ2 : ℝ≥0) (x : Fin n → ℝ) :
    Measurable (Function.uncurry (linRegLikelihoodPDF σ2 x)) := by
  change Measurable fun z : ℝ × (Fin n → ℝ) ↦ ∏ i, gaussianPDF (z.1 * x i) σ2 (z.2 i)
  refine Finset.measurable_prod _ fun i _ ↦ ?_
  have hf : Measurable fun z : ℝ × (Fin n → ℝ) ↦ (z.1 * x i, σ2, z.2 i) := by fun_prop
  exact measurable_uncurry_gaussianPDF.comp hf

/-- **The likelihood of Bayesian linear regression** with one feature and known noise variance:
given the weight `w`, the responses are independent, `yᵢ ~ N(w xᵢ, σ²)`. For `σ² = 0` they are
exactly `w xᵢ` (`linRegLikelihood_zero_apply`). -/
noncomputable def linRegLikelihood (σ2 : ℝ≥0) (x : Fin n → ℝ) : Kernel ℝ (Fin n → ℝ) :=
  if σ2 = 0 then Kernel.deterministic (fun w i ↦ w * x i) (by fun_prop)
  else (Kernel.const ℝ volume).withDensity (linRegLikelihoodPDF σ2 x)

theorem linRegLikelihood_apply' {σ2 : ℝ≥0} (h : σ2 ≠ 0) (x : Fin n → ℝ) (w : ℝ) :
    linRegLikelihood σ2 x w = volume.withDensity (linRegLikelihoodPDF σ2 x w) := by
  simp only [linRegLikelihood, h, ↓reduceIte]
  rw [Kernel.withDensity_apply _ (measurable_linRegLikelihoodPDF σ2 x), Kernel.const_apply]

/-- With zero noise the responses are exactly `w xᵢ`. -/
theorem linRegLikelihood_zero_apply (x : Fin n → ℝ) (w : ℝ) :
    linRegLikelihood 0 x w = Measure.dirac fun i ↦ w * x i := by
  simp [linRegLikelihood, Kernel.deterministic_apply]

/-- The likelihood is the product of the Gaussian laws of the responses. -/
theorem linRegLikelihood_apply {σ2 : ℝ≥0} (h : σ2 ≠ 0) (x : Fin n → ℝ) (w : ℝ) :
    linRegLikelihood σ2 x w = Measure.pi fun i ↦ gaussianReal (w * x i) σ2 := by
  have : ∀ i, SigmaFinite (volume.withDensity (gaussianPDF (w * x i) σ2)) := fun i ↦ by
    rw [← gaussianReal_of_var_ne_zero _ h]
    infer_instance
  simp_rw [linRegLikelihood_apply' h, gaussianReal_of_var_ne_zero _ h]
  rw [Measure.pi_withDensity (μ := fun _ ↦ volume) fun i ↦ measurable_gaussianPDF _ _,
    ← volume_pi]
  rfl

instance {σ2 : ℝ≥0} (x : Fin n → ℝ) : IsMarkovKernel (linRegLikelihood σ2 x) := by
  by_cases h : σ2 = 0
  · subst h
    exact ⟨fun w ↦ by rw [linRegLikelihood_zero_apply]; infer_instance⟩
  · exact ⟨fun w ↦ by rw [linRegLikelihood_apply h]; infer_instance⟩

/-! ### The posterior -/

theorem measurable_linRegPostMean (m₀ : ℝ) (s₀ σ2 : ℝ≥0) (x : Fin n → ℝ) :
    Measurable (linRegPostMean m₀ s₀ σ2 x) := by
  unfold linRegPostMean
  fun_prop

theorem measurable_linRegEvidencePDFReal (m₀ : ℝ) (s₀ σ2 : ℝ≥0) (x : Fin n → ℝ) :
    Measurable (linRegEvidencePDFReal m₀ s₀ σ2 x) := by
  have hm := measurable_linRegPostMean m₀ s₀ σ2 x
  have hp : Measurable fun y ↦ gaussianPDFReal m₀ s₀ (linRegPostMean m₀ s₀ σ2 x y) :=
    (measurable_gaussianPDFReal m₀ s₀).comp hm
  have hL : Measurable fun y ↦ linRegLikelihoodPDFReal σ2 x (linRegPostMean m₀ s₀ σ2 x y) y := by
    refine Finset.measurable_prod _ fun i _ ↦ ?_
    have hf : Measurable fun y : Fin n → ℝ ↦ (linRegPostMean m₀ s₀ σ2 x y * x i, σ2, y i) :=
      (hm.mul_const _).prodMk (measurable_const.prodMk (measurable_pi_apply i))
    exact measurable_uncurry_gaussianPDFReal.comp hf
  have hr : Measurable fun y ↦ gaussianPDFReal (linRegPostMean m₀ s₀ σ2 x y)
      (linRegPostVar s₀ σ2 x) (linRegPostMean m₀ s₀ σ2 x y) := by
    have hf : Measurable fun y : Fin n → ℝ ↦ (linRegPostMean m₀ s₀ σ2 x y,
        linRegPostVar s₀ σ2 x, linRegPostMean m₀ s₀ σ2 x y) :=
      hm.prodMk (measurable_const.prodMk hm)
    exact measurable_uncurry_gaussianPDFReal.comp hf
  exact (hp.mul hL).div hr

theorem measurable_linRegPostMean_gaussianPDF (m₀ : ℝ) (s₀ σ2 : ℝ≥0) (x : Fin n → ℝ) :
    Measurable (Function.uncurry fun y w ↦
      gaussianPDF (linRegPostMean m₀ s₀ σ2 x y) (linRegPostVar s₀ σ2 x) w) := by
  have hf : Measurable fun a : (Fin n → ℝ) × ℝ ↦
      (linRegPostMean m₀ s₀ σ2 x a.1, linRegPostVar s₀ σ2 x, a.2) :=
    ((measurable_linRegPostMean m₀ s₀ σ2 x).comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd)
  exact measurable_uncurry_gaussianPDF.comp hf

theorem gaussianPDF_mul_linRegLikelihoodPDF (m₀ : ℝ) {s₀ σ2 : ℝ≥0} (h₀ : s₀ ≠ 0) (h : σ2 ≠ 0)
    (x : Fin n → ℝ) (w : ℝ) (y : Fin n → ℝ) :
    gaussianPDF m₀ s₀ w * linRegLikelihoodPDF σ2 x w y =
      ENNReal.ofReal (linRegEvidencePDFReal m₀ s₀ σ2 x y) *
        gaussianPDF (linRegPostMean m₀ s₀ σ2 x y) (linRegPostVar s₀ σ2 x) w := by
  rw [linRegLikelihoodPDF_eq, gaussianPDF, gaussianPDF,
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul (linRegEvidencePDFReal_pos m₀ h₀ h x y).le,
    gaussianPDFReal_mul_linRegLikelihoodPDFReal' m₀ h₀ h]

/-- **The evidence.** The marginal law of the responses has density `linRegEvidencePDFReal`. -/
theorem linRegLikelihood_comp_gaussianReal (m₀ : ℝ) {s₀ σ2 : ℝ≥0} (h₀ : s₀ ≠ 0) (h : σ2 ≠ 0)
    (x : Fin n → ℝ) :
    linRegLikelihood σ2 x ∘ₘ gaussianReal m₀ s₀ =
      volume.withDensity fun y ↦ ENNReal.ofReal (linRegEvidencePDFReal m₀ s₀ σ2 x y) :=
  comp_eq_withDensity_of_mul_eq (gaussianReal_of_var_ne_zero _ h₀)
    (linRegLikelihood_apply' h x) (measurable_gaussianPDF _ _)
    (measurable_linRegLikelihoodPDF σ2 x)
    (measurable_linRegEvidencePDFReal m₀ s₀ σ2 x).ennreal_ofReal
    (measurable_linRegPostMean_gaussianPDF m₀ s₀ σ2 x)
    (fun _ ↦ lintegral_gaussianPDF_eq_one _ (linRegPostVar_ne_zero h₀ h x))
    (gaussianPDF_mul_linRegLikelihoodPDF m₀ h₀ h x)

/-- **Bayesian linear regression** with one feature, a `N(m₀, s₀)` prior on the weight and known
noise variance `σ²`. For almost every response vector `y`, the posterior of the weight is Gaussian
with mean `(σ² m₀ + s₀ ∑ xᵢ yᵢ) / (σ² + s₀ ∑ xᵢ²)` and variance `s₀ σ² / (σ² + s₀ ∑ xᵢ²)`. -/
theorem posterior_linRegLikelihood_gaussianReal (m₀ : ℝ) {s₀ σ2 : ℝ≥0} [NeZero s₀] [NeZero σ2]
    (x : Fin n → ℝ) :
    ∀ᵐ y, ((linRegLikelihood σ2 x)†(gaussianReal m₀ s₀)) y =
      gaussianReal (linRegPostMean m₀ s₀ σ2 x y) (linRegPostVar s₀ σ2 x) := by
  have h₀ := NeZero.ne s₀
  have h := NeZero.ne σ2
  have hae := posterior_ae_eq_of_mul_eq (gaussianReal_of_var_ne_zero _ h₀)
    (linRegLikelihood_apply' h x) (measurable_gaussianPDF _ _)
    (measurable_linRegLikelihoodPDF σ2 x)
    (measurable_linRegEvidencePDFReal m₀ s₀ σ2 x).ennreal_ofReal
    (measurable_linRegPostMean_gaussianPDF m₀ s₀ σ2 x)
    (fun _ ↦ lintegral_gaussianPDF_eq_one _ (linRegPostVar_ne_zero h₀ h x))
    (gaussianPDF_mul_linRegLikelihoodPDF m₀ h₀ h x)
  rw [linRegLikelihood_comp_gaussianReal m₀ h₀ h x] at hae
  have hac : (volume : Measure (Fin n → ℝ)) ≪
      volume.withDensity fun y ↦ ENNReal.ofReal (linRegEvidencePDFReal m₀ s₀ σ2 x y) :=
    withDensity_absolutelyContinuous'
      (measurable_linRegEvidencePDFReal m₀ s₀ σ2 x).ennreal_ofReal.aemeasurable
      (ae_of_all _ fun y ↦ (ENNReal.ofReal_pos.mpr (linRegEvidencePDFReal_pos m₀ h₀ h x y)).ne')
  filter_upwards [hac hae] with y hy
  rw [hy, gaussianReal_of_var_ne_zero _ (linRegPostVar_ne_zero h₀ h x)]

/-! ### Prediction at a new input -/

/-- The law of the response at a new input `x'`: `y' ~ N(w x', σ²)`. -/
noncomputable def linRegPredictive (σ2 : ℝ≥0) (x' : ℝ) : Kernel ℝ ℝ :=
  (gaussianLikelihood σ2).comap (· * x') (measurable_mul_const x')

theorem linRegPredictive_comp (σ2 : ℝ≥0) (x' : ℝ) (μ : Measure ℝ) :
    linRegPredictive σ2 x' ∘ₘ μ = gaussianLikelihood σ2 ∘ₘ μ.map (· * x') := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map ((gaussianLikelihood σ2).measurable_coe hs) (measurable_mul_const x')]
  rfl

/-- **Posterior predictive at a new input.** After observing `y`, the response at an input `x'`
is `N(x' m, x'² v + σ²)`, where `m` and `v` are the posterior mean and variance. -/
theorem linRegPredictive_comp_posterior (m₀ : ℝ) {s₀ σ2 : ℝ≥0} [NeZero s₀] [NeZero σ2]
    (x : Fin n → ℝ) (x' : ℝ) :
    ∀ᵐ y, linRegPredictive σ2 x' ∘ₘ ((linRegLikelihood σ2 x)†(gaussianReal m₀ s₀)) y =
      gaussianReal (x' * linRegPostMean m₀ s₀ σ2 x y)
        (.mk (x' ^ 2) (sq_nonneg _) * linRegPostVar s₀ σ2 x + σ2) := by
  filter_upwards [posterior_linRegLikelihood_gaussianReal m₀ (s₀ := s₀) (σ2 := σ2) x] with y hy
  rw [hy, linRegPredictive_comp, gaussianReal_map_mul_const]
  by_cases hx' : x' = 0
  · subst hx'
    have h0 : NNReal.mk ((0 : ℝ) ^ 2) (sq_nonneg _) * linRegPostVar s₀ σ2 x = 0 := by
      ext
      simp
    rw [h0, zero_add, gaussianReal_zero_var, Measure.dirac_bind (gaussianLikelihood σ2).measurable,
      gaussianLikelihood_apply (NeZero.ne σ2)]
  have hx2 : NNReal.mk (x' ^ 2) (sq_nonneg _) ≠ 0 := by
    rw [← NNReal.coe_ne_zero, NNReal.coe_mk]
    positivity
  have hv : NNReal.mk (x' ^ 2) (sq_nonneg _) * linRegPostVar s₀ σ2 x ≠ 0 :=
    mul_ne_zero hx2 (linRegPostVar_ne_zero (NeZero.ne s₀) (NeZero.ne σ2) x)
  rw [gaussianLikelihood_comp_gaussianReal _ hv (NeZero.ne σ2)]

end Cslib.MachineLearning.Bayesian
