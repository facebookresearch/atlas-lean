/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.ErrorsInVariables.LogisticCalibration

/-! # Tests for `MathlibExt.Probability.Statistics.ErrorsInVariables.LogisticCalibration`

* Values of `discriminantSlope`, `discriminantIntercept`, `attenuationFactor`,
  `linearCalibration` and `bayesPosterior` computed from the definitions, including the
  boundaries: no measurement error (`attenuationFactor v 0 = 1`, no attenuation), equal class
  means (posterior equals the prior), and `ρ ∈ {0, 1}` for the calibration function.
* The marginal reliability ratio undercorrects: in the non-vacuity model below it turns the
  naive slope `1` into `3 / 2`, not the true slope `2`.
* Rare-event calibration at `β = 0`, computed directly from `integral_const`: the induced risk
  `exp α` agrees with the closed form, and the logistic gap `exp 0 - σ 0 = 1 / 2` is positive, so
  regression calibration of the logistic risk is approximate, not exact.
* Non-vacuity of `logistic_errorsInVariables_attenuation`: on `Bool × ℝ × ℝ` with a fair label
  and two independent standard Gaussian coordinates, `X = 2 [Y] + Z₁` and `U = Z₂` satisfy every
  hypothesis. There `β = 2`, `ρ = 1 / 2`, the naive slope is `1`, and the version statements are
  evaluated at `A = univ`, where `P(Y = 1) = 1 / 2` is computed from the definition of the
  measure.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
open MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables
open MathlibExt.Probability.Statistics.ErrorsInVariables.LogisticCalibration

namespace MathlibExtTest.LogisticCalibration

/-! ### Coefficients from the definitions -/

example : discriminantSlope 0 2 1 = 2 := by norm_num [discriminantSlope]

/-- With measurement-error variance `1`, the slope on `W` halves. -/
example : discriminantSlope 0 2 (1 + 1) = 1 := by norm_num [discriminantSlope]

example : attenuationFactor 1 1 = 1 / 2 := by norm_num [attenuationFactor]

/-- Boundary: without measurement error there is no attenuation. -/
example {v : ℝ} (hv : v ≠ 0) : attenuationFactor v 0 = 1 := by
  simp [attenuationFactor, hv]

/-- Measurement error strictly attenuates: `ρ < 1` when `v_u > 0`. -/
example {v vu : ℝ} (hv : 0 < v) (hvu : 0 < vu) : attenuationFactor v vu < 1 := by
  rw [attenuationFactor, div_lt_one (by linarith)]
  linarith

/-- The marginal reliability ratio undercorrects. With `p = 1 / 2`, `μ₀ = 0`, `μ₁ = 2`, `v = 1`,
`v_u = 1`, the marginal variance of `X` is `v + p (1 - p) (μ₁ - μ₀)² = 2`, so the marginal ratio
is `2 / 3`, and the naive slope `1` divided by it is `3 / 2`, not the true slope `2`. -/
example :
    discriminantSlope 0 2 (1 + 1) / attenuationFactor (1 + 1 / 2 * (1 - 1 / 2) * (2 - 0) ^ 2) 1 =
      3 / 2 ∧ discriminantSlope 0 2 1 = 2 := by
  norm_num [discriminantSlope, attenuationFactor]

/-- Boundary: equal class means give a flat logistic line. -/
example (μ v : ℝ) : discriminantSlope μ μ v = 0 := by simp [discriminantSlope]

/-- A fair prior with symmetric means `∓ 1` gives a zero intercept. -/
example (v : ℝ) : discriminantIntercept (1 / 2) (-1) 1 v = 0 := by
  norm_num [discriminantIntercept, discriminantSlope]

/-- Boundary: equal class densities give the prior as the posterior. -/
example (p : ℝ) (f : ℝ → ℝ) (x : ℝ) (hf : 0 < f x) : bayesPosterior p f f x = p := by
  rw [bayesPosterior, ← add_mul, show p + (1 - p) = 1 by ring, one_mul,
    mul_div_cancel_right₀ _ hf.ne']

example (μx w : ℝ) : linearCalibration μx 1 w = w := by simp [linearCalibration]

example (μx w : ℝ) : linearCalibration μx 0 w = μx := by simp [linearCalibration]

example : linearCalibration 1 (1 / 2) 3 = 2 := by norm_num [linearCalibration]

/-! ### Rare-event calibration at `β = 0`, from the definitions -/

/-- The induced log-linear risk at `β = 0`, computed with `integral_const`. -/
theorem integral_exp_const (α m : ℝ) (τ2 : ℝ≥0) :
    ∫ x, exp (α + 0 * x) ∂gaussianReal m τ2 = exp α := by
  simp

/-- The closed form of `integral_exp_affine_gaussianReal` agrees at `β = 0`. -/
example (α m : ℝ) (τ2 : ℝ≥0) : exp (α + 0 ^ 2 * τ2 / 2 + 0 * m) = exp α := by simp

/-- The induced logistic risk at `β = 0` is `σ(α)`. -/
theorem integral_sigmoid_const (α m : ℝ) (τ2 : ℝ≥0) :
    ∫ x, sigmoid (α + 0 * x) ∂gaussianReal m τ2 = sigmoid α := by
  simp

/-- The logistic risk and the calibrated log-linear risk differ: at `α = β = 0` the gap is
`1 - 1 / 2 = 1 / 2`, positive and within the bound `exp 0 = 1`. -/
example (m : ℝ) (τ2 : ℝ≥0) :
    exp (0 : ℝ) - ∫ x, sigmoid (0 + 0 * x) ∂gaussianReal m τ2 = 1 / 2 := by
  rw [integral_sigmoid_const, sigmoid_zero, exp_zero]
  norm_num

/-- At a rare-event scale `α = -5`, the gap `exp α - σ(α)` is below `exp (2 α)`. -/
example : exp (-5 : ℝ) - sigmoid (-5) ≤ exp (2 * -5) := exp_sub_sigmoid_le _

/-! ### Non-vacuity of the logistic errors-in-variables model -/

/-- A fair binary label. -/
noncomputable def ν : Measure Bool := (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure ν := ⟨by simp [ν, ENNReal.inv_two_add_inv_two]⟩

/-- Two independent standard Gaussian coordinates. -/
noncomputable def R : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure R := by unfold R; infer_instance

/-- The joint law: label independent of the two Gaussian coordinates. -/
noncomputable def P : Measure (Bool × ℝ × ℝ) := ν.prod R

instance : IsProbabilityMeasure P := by unfold P; infer_instance

/-- The label. -/
def Y : Bool × ℝ × ℝ → Bool := Prod.fst

/-- Class means `μ₀ = 0`, `μ₁ = 2`. -/
noncomputable def mean (y : Bool) : ℝ := if y then 2 else 0

/-- The true regressor `X = μ_Y + Z₁`. -/
noncomputable def X (ω : Bool × ℝ × ℝ) : ℝ := mean ω.1 + ω.2.1

/-- The measurement error `U = Z₂`. -/
def U (ω : Bool × ℝ × ℝ) : ℝ := ω.2.2

theorem measurable_Y : Measurable Y := measurable_fst

theorem measurable_X : Measurable X :=
  ((measurable_of_countable mean).comp measurable_fst).add (measurable_fst.comp measurable_snd)

theorem measurable_U : Measurable U := measurable_snd.comp measurable_snd

theorem ν_singleton (y : Bool) : ν {y} = 2⁻¹ := by
  cases y <;> simp [ν]

theorem preimage_Y (y : Bool) : Y ⁻¹' {y} = {y} ×ˢ Set.univ := by
  ext ω
  simp [Y]

/-- `P(Y = 1) = 1 / 2`, from the definition of `P`. -/
theorem probReal_Y_true : P.real (Y ⁻¹' {true}) = 1 / 2 := by
  rw [measureReal_def, preimage_Y, P, Measure.prod_prod, ν_singleton, measure_univ, mul_one]
  norm_num

/-- Conditionally on `Y = y`, the noise coordinates keep their product law. -/
theorem cond_P (y : Bool) : P[|Y ⁻¹' {y}] = R.map (Prod.mk y) := by
  rw [ProbabilityTheory.cond, preimage_Y, P, ← Measure.prod_restrict, Measure.restrict_singleton,
    Measure.restrict_univ, Measure.prod_smul_left, Measure.prod_prod, ν_singleton, measure_univ,
    mul_one, smul_smul, ENNReal.inv_mul_cancel (by simp) (by simp), one_smul, Measure.dirac_prod]

theorem hasLaw_X (y : Bool) : HasLaw X (gaussianReal (mean y) 1) P[|Y ⁻¹' {y}] := by
  rw [cond_P]
  refine ⟨measurable_X.aemeasurable, ?_⟩
  rw [Measure.map_map measurable_X (by fun_prop)]
  have : X ∘ Prod.mk y = (mean y + ·) ∘ Prod.fst := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), R, Measure.map_fst_prod, measure_univ,
    one_smul, gaussianReal_map_const_add, zero_add]

theorem hasLaw_U (y : Bool) : HasLaw U (gaussianReal 0 1) P[|Y ⁻¹' {y}] := by
  rw [cond_P]
  refine ⟨measurable_U.aemeasurable, ?_⟩
  rw [Measure.map_map measurable_U (by fun_prop)]
  have : U ∘ Prod.mk y = Prod.snd := rfl
  rw [this, R, Measure.map_snd_prod, measure_univ, one_smul]

theorem indepFun_X_U (y : Bool) : IndepFun X U P[|Y ⁻¹' {y}] := by
  rw [cond_P, indepFun_iff_map_prod_eq_prod_map_map measurable_X.aemeasurable
    measurable_U.aemeasurable, Measure.map_map (measurable_X.prodMk measurable_U) (by fun_prop),
    Measure.map_map measurable_X (by fun_prop), Measure.map_map measurable_U (by fun_prop)]
  have h1 : (fun ω => (X ω, U ω)) ∘ Prod.mk y = Prod.map (mean y + ·) id := rfl
  have h2 : X ∘ Prod.mk y = (mean y + ·) ∘ Prod.fst := rfl
  have h3 : U ∘ Prod.mk y = Prod.snd := rfl
  rw [h1, h2, h3, ← Measure.map_map (by fun_prop) (by fun_prop), R, Measure.map_fst_prod,
    Measure.map_snd_prod, measure_univ, one_smul,
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id]

/-- Every hypothesis of `logistic_errorsInVariables_attenuation` holds for this model; the
conclusions give `P(Y = 1) = 1 / 2` as the integral of the true and of the naive logistic
models over the whole space, and recover `β = 2` from the naive slope `1` and `ρ = 1 / 2`. -/
theorem nonvacuous :
    (∫ ω, sigmoid (discriminantIntercept (1 / 2) 0 2 1 + 2 * X ω) ∂P = 1 / 2) ∧
    (∫ ω, sigmoid (discriminantIntercept (1 / 2) 0 2 (1 + 1) + 1 / 2 * 2 * (X + U) ω) ∂P =
      1 / 2) ∧
    discriminantSlope 0 2 (1 + 1) / attenuationFactor 1 1 = 2 := by
  have hp₀ : 0 < P.real (Y ⁻¹' {true}) := by rw [probReal_Y_true]; norm_num
  have hp₁ : P.real (Y ⁻¹' {true}) < 1 := by rw [probReal_Y_true]; norm_num
  obtain ⟨h₁, h₂, h₃⟩ := logistic_errorsInVariables_attenuation (μ₀ := 0) (μ₁ := 2) (v := 1)
    (vu := 1) measurable_Y measurable_X measurable_U hp₀ hp₁ one_ne_zero (hasLaw_X false)
    (hasLaw_X true) (hasLaw_U false) (hasLaw_U true) (indepFun_X_U false) (indepFun_X_U true)
  have hβ : discriminantSlope 0 2 ((1 : ℝ≥0) : ℝ) = 2 := by norm_num [discriminantSlope]
  have hρ : attenuationFactor ((1 : ℝ≥0) : ℝ) ((1 : ℝ≥0) : ℝ) = 1 / 2 := by
    norm_num [attenuationFactor]
  have hP : P.real (Y ⁻¹' {true} ∩ Set.univ) = 1 / 2 := by
    rw [Set.inter_univ, probReal_Y_true]
  refine ⟨?_, ?_, ?_⟩
  · have := h₁ Set.univ MeasurableSet.univ
    simp only [Set.preimage_univ, Measure.restrict_univ, hβ, hP, probReal_Y_true] at this
    simpa using this
  · have := h₂ Set.univ MeasurableSet.univ
    simp only [Set.preimage_univ, Measure.restrict_univ, hβ, hρ, hP, probReal_Y_true] at this
    simpa using this
  · simp only [NNReal.coe_one] at h₃
    rw [h₃]
    norm_num [discriminantSlope]

#print axioms logistic_errorsInVariables_attenuation
#print axioms setIntegral_bayesPosterior_eq_measureReal_inter
#print axioms exp_sub_integral_sigmoid_affine_gaussianReal_le
#print axioms nonvacuous

end MathlibExtTest.LogisticCalibration
