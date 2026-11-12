/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Random assignment identifies the average treatment effect

If the treatment indicator `1_T` is independent of the potential outcomes `(Y₀, Y₁)` (random
assignment) and both groups have positive probability, then the difference of the observed
group means `E[Y | T] - E[Y | Tᶜ]` equals the average treatment effect `E[Y₁ - Y₀]`, where
`Y = observed T Y₀ Y₁` is the observed outcome (consistency) and `E[· | T]` is the mean under
the conditional measure `μ[|T]` (Imbens and Rubin 2015, §3.3 and Chapter 6; Hernán and Robins
2020, §2.1).

## Main results

* `integral_observed_cond_treated_of_indepFun`: `E[Y | T] = E[Y₁]` if `1_T` is independent of
  `Y₁` and `P(T) > 0`.
* `integral_observed_cond_control_of_indepFun`: `E[Y | Tᶜ] = E[Y₀]` if `1_T` is independent of
  `Y₀` and `P(T) < 1`.
* `diff_integral_observed_cond_eq_ate_of_indepFun`: identification of the ATE by the difference
  in group means.

This is the superpopulation statement. The finite-population (design-based) counterpart under
complete randomization is `randExp_diffInMeans` in
`MathlibExt/Probability/Causality/CausalIdentification.lean`; strong ignorability with a
covariate is `integral_ipw_ate` there.

## References

* G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
  Sciences*, Cambridge University Press (2015).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman & Hall/CRC (2020).
-/

@[expose] public section

namespace MathlibExt.Probability.Causality

open MeasureTheory ProbabilityTheory

/-- **Random assignment, treated arm**: if the treatment indicator `1_T` is independent of the
treated potential outcome `Y₁` and `P(T) > 0`, then `∫ Y ∂μ[|T] = ∫ Y₁ ∂μ` for the observed
outcome `Y = observed T Y₀ Y₁` (consistency). No integrability is assumed: the identity holds for
Bochner integrals in general, and when `Y₁` is integrable (as in
`diff_integral_observed_cond_eq_ate_of_indepFun`) both sides are genuine means,
`E[Y | T] = E[Y₁]`; for non-integrable `Y₁` both sides are the conventional value `0`. -/
theorem integral_observed_cond_treated_of_indepFun {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {Y₀ Y₁ : Ω → ℝ} (hY₁ : Measurable Y₁)
    (hind : IndepFun (T.indicator (1 : Ω → ℝ)) Y₁ μ) (hpos : 0 < μ.real T) :
    ∫ ω, observed T Y₀ Y₁ ω ∂μ[|T] = ∫ ω, Y₁ ω ∂μ := by
  have hT1 : Measurable (T.indicator (1 : Ω → ℝ)) := measurable_const.indicator hT
  have hmul : (T.indicator (1 : Ω → ℝ)) * Y₁ = T.indicator Y₁ := by
    funext ω
    by_cases hω : ω ∈ T <;> simp [hω, Pi.mul_apply]
  have hfact := hind.integral_mul_eq_mul_integral hT1.aestronglyMeasurable hY₁.aestronglyMeasurable
  rw [hmul, integral_indicator hT] at hfact
  have hint1 : ∫ ω, T.indicator (1 : Ω → ℝ) ω ∂μ = μ.real T := by
    rw [integral_indicator hT]
    simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]
  rw [hint1] at hfact
  have hobs : observed T Y₀ Y₁ =ᵐ[μ[|T]] Y₁ := by
    filter_upwards [ae_cond_mem hT] with ω hω
    simp [observed, hω]
  rw [integral_congr_ae hobs]
  have hcond : μ[|T] = (μ T)⁻¹ • μ.restrict T := rfl
  rw [hcond, integral_smul_measure]
  have hreal : ((μ T)⁻¹).toReal = (μ.real T)⁻¹ := by
    rw [ENNReal.toReal_inv, Measure.real_def]
  rw [hreal, smul_eq_mul]
  have hset : ∫ ω, Y₁ ω ∂(μ.restrict T) = ∫ ω in T, Y₁ ω ∂μ := rfl
  rw [hset, hfact]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]

/-- **Random assignment, control arm**: if `1_T` is independent of `Y₀` and `P(T) < 1`, the
mean observed outcome among the controls is `E[Y₀]`. -/
theorem integral_observed_cond_control_of_indepFun {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {Y₀ Y₁ : Ω → ℝ} (hY₀ : Measurable Y₀) (hY₀i : Integrable Y₀ μ)
    (hind : IndepFun (T.indicator (1 : Ω → ℝ)) Y₀ μ) (hlt : μ.real T < 1) :
    ∫ ω, observed T Y₀ Y₁ ω ∂μ[|Tᶜ] = ∫ ω, Y₀ ω ∂μ := by
  have hT1 : Measurable (T.indicator (1 : Ω → ℝ)) := measurable_const.indicator hT
  have hmul : (T.indicator (1 : Ω → ℝ)) * Y₀ = T.indicator Y₀ := by
    funext ω
    by_cases hω : ω ∈ T <;> simp [hω, Pi.mul_apply]
  have hfact := hind.integral_mul_eq_mul_integral hT1.aestronglyMeasurable hY₀.aestronglyMeasurable
  rw [hmul, integral_indicator hT] at hfact
  have hint1 : ∫ ω, T.indicator (1 : Ω → ℝ) ω ∂μ = μ.real T := by
    rw [integral_indicator hT]
    simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]
  rw [hint1] at hfact
  have hadd := integral_add_compl hT hY₀i
  have hcompl : ∫ ω in Tᶜ, Y₀ ω ∂μ = μ.real (Tᶜ) * ∫ ω, Y₀ ω ∂μ := by
    have hTc : μ.real (Tᶜ) = 1 - μ.real T := by
      rw [measureReal_compl hT, probReal_univ]
    rw [hTc]
    linarith [hfact, hadd]
  have hposC : 0 < μ.real (Tᶜ) := by
    rw [measureReal_compl hT, probReal_univ]
    linarith [hlt, measureReal_nonneg (μ := μ) (s := T)]
  have hobs : observed T Y₀ Y₁ =ᵐ[μ[|Tᶜ]] Y₀ := by
    filter_upwards [ae_cond_mem hT.compl] with ω hω
    simp [observed, hω]
    have : ω ∉ T := by simpa using hω
    simp [this]
  rw [integral_congr_ae hobs]
  have hcond : μ[|Tᶜ] = (μ Tᶜ)⁻¹ • μ.restrict Tᶜ := rfl
  rw [hcond, integral_smul_measure]
  have hreal : ((μ Tᶜ)⁻¹).toReal = (μ.real Tᶜ)⁻¹ := by
    rw [ENNReal.toReal_inv, Measure.real_def]
  rw [hreal, smul_eq_mul]
  have hset : ∫ ω, Y₀ ω ∂(μ.restrict Tᶜ) = ∫ ω in Tᶜ, Y₀ ω ∂μ := rfl
  rw [hset, hcompl]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hposC), one_mul]

/-- **Identification of the ATE under random assignment**: if the treatment indicator `1_T` is
independent of the pair of potential outcomes `(Y₀, Y₁)`, both arms have positive probability,
and the potential outcomes are integrable, then the difference of the observed group means
identifies the average treatment effect, `E[Y | T] - E[Y | Tᶜ] = E[Y₁ - Y₀]`, where
`Y = observed T Y₀ Y₁` (consistency). -/
theorem diff_integral_observed_cond_eq_ate_of_indepFun {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {Y₀ Y₁ : Ω → ℝ} (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁)
    (hY₀i : Integrable Y₀ μ) (hY₁i : Integrable Y₁ μ)
    (hind : IndepFun (T.indicator (1 : Ω → ℝ)) (fun ω => (Y₀ ω, Y₁ ω)) μ)
    (hpos : 0 < μ.real T) (hlt : μ.real T < 1) :
    ∫ ω, observed T Y₀ Y₁ ω ∂μ[|T] - ∫ ω, observed T Y₀ Y₁ ω ∂μ[|Tᶜ] =
      ∫ ω, (Y₁ ω - Y₀ ω) ∂μ := by
  have hind0 : IndepFun (T.indicator (1 : Ω → ℝ)) Y₀ μ := by
    have h := hind.comp measurable_id measurable_fst
    refine h.congr (Filter.Eventually.of_forall fun ω => rfl)
      (Filter.Eventually.of_forall fun ω => rfl)
  have hind1 : IndepFun (T.indicator (1 : Ω → ℝ)) Y₁ μ := by
    have h := hind.comp measurable_id measurable_snd
    refine h.congr (Filter.Eventually.of_forall fun ω => rfl)
      (Filter.Eventually.of_forall fun ω => rfl)
  have h1 : ∫ ω, observed T Y₀ Y₁ ω ∂μ[|T] = ∫ ω, Y₁ ω ∂μ :=
    integral_observed_cond_treated_of_indepFun hT hY₁ hind1 hpos
  have h0 : ∫ ω, observed T Y₀ Y₁ ω ∂μ[|Tᶜ] = ∫ ω, Y₀ ω ∂μ :=
    integral_observed_cond_control_of_indepFun hT hY₀ hY₀i hind0 hlt
  rw [h1, h0, ← integral_sub hY₁i hY₀i]

end MathlibExt.Probability.Causality
