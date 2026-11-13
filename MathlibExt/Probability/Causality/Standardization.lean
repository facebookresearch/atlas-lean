/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification
public import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.BigOperators.Fin

/-!
# Standardization: identification under conditional exchangeability

For a covariate `X` with finitely many values, conditional exchangeability `T ⊥ Y_t | X` with
overlap `0 < P(T | X = x) < 1` (Atlas's `StronglyIgnorable`) identifies the mean potential
outcomes by standardization (the g-formula, direct adjustment):
`E[Y₁] = ∑_x P(X = x) E[Y | T, X = x]`, `E[Y₀] = ∑_x P(X = x) E[Y | Tᶜ, X = x]`, and the
average treatment effect is the difference (Hernán and Robins 2020, §2.3 and §12–13; Imbens and
Rubin 2015, §12). Here `Y = observed T Y₀ Y₁` is the observed outcome (consistency) and
`E[· | A]` is the mean under the conditional measure `μ[|A]`; covariate values of probability
zero contribute `0`.

## Main results

* `integral_eq_sum_standardized_treated`, `integral_eq_sum_standardized_control`: the
  per-arm standardization formulas.
* `integral_sub_eq_sum_standardized`: identification of the ATE by standardization.

The inverse-probability-weighting form of the same identification is `integral_ipw_ate` in
`MathlibExt/Probability/Causality/CausalIdentification.lean`; the per-cell step uses its public
`setIntegral_inter_eq_propensity_mul`. The graphical (do-calculus) counterpart is
`BayesNet.backdoor_adjustment` in CSLib.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman & Hall/CRC (2020).
* G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
  Sciences*, Cambridge University Press (2015).
-/

@[expose] public section

namespace MathlibExt.Probability.Causality

open MeasureTheory ProbabilityTheory

/-- Integral against the conditional measure `μ[|s]` as a scaled set integral. -/
theorem integral_cond_eq_inv_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) (f : Ω → ℝ) :
    ∫ ω, f ω ∂μ[|s] = (μ.real s)⁻¹ * ∫ ω in s, f ω ∂μ := by
  unfold ProbabilityTheory.cond Measure.real
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]

/-- The observed outcome agrees with `Y₁` on the treated event. -/
theorem observed_eq_on_treated {Ω : Type*} [MeasurableSpace Ω] (T : Set Ω)
    (Y₀ Y₁ : Ω → ℝ) : Set.EqOn (observed T Y₀ Y₁) Y₁ T := by
  intro ω hω
  simp [observed, hω]

/-- The observed outcome agrees with `Y₀` off the treated event. -/
theorem observed_eq_on_control {Ω : Type*} [MeasurableSpace Ω] (T : Set Ω)
    (Y₀ Y₁ : Ω → ℝ) : Set.EqOn (observed T Y₀ Y₁) Y₀ Tᶜ := by
  intro ω hω
  simp [observed, Set.notMem_of_mem_compl hω, hω]

/-- Splitting an integral over the finitely many level sets of `X`. -/
theorem integral_eq_sum_preimage {Ω 𝒳 : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype 𝒳] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]
    {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ} (hYi : Integrable Y μ) :
    ∫ ω, Y ω ∂μ = ∑ x, ∫ ω in X ⁻¹' {x}, Y ω ∂μ := by
  have hU : (⋃ x, X ⁻¹' {x}) = Set.univ := by ext ω; simp
  have hA : ∀ x : 𝒳, MeasurableSet (X ⁻¹' {x}) := fun x => hX (measurableSet_singleton x)
  have hdisj : Pairwise (Function.onFun Disjoint fun x : 𝒳 => X ⁻¹' {x}) := fun x y hxy =>
    Set.disjoint_left.2 fun ω h1 h2 => hxy (h1.symm.trans h2)
  rw [← setIntegral_univ, ← hU, integral_iUnion_fintype hA hdisj (fun x => hYi.integrableOn)]

/-- Per-cell standardization identity, treated arm. -/
theorem per_cell_treated {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {T : Set Ω} (hT : MeasurableSet T) {X : Ω → 𝒳}
    (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ} (hY₁ : Measurable Y₁)
    (h : StronglyIgnorable μ T Y₁ X) (x : 𝒳) :
    μ.real (X ⁻¹' {x}) * ∫ ω, observed T Y₀ Y₁ ω ∂μ[|T ∩ X ⁻¹' {x}] =
      ∫ ω in X ⁻¹' {x}, Y₁ ω ∂μ := by
  have hA : MeasurableSet (X ⁻¹' {x}) := hX (measurableSet_singleton x)
  have hS : MeasurableSet (T ∩ X ⁻¹' {x}) := hT.inter hA
  by_cases hA0 : μ.real (X ⁻¹' {x}) = 0
  · have hμA0 : μ (X ⁻¹' {x}) = 0 := (measureReal_eq_zero_iff).1 hA0
    rw [hA0, zero_mul, Measure.restrict_eq_zero.2 hμA0]
    simp
  · have hμA : μ (X ⁻¹' {x}) ≠ 0 := fun hcon => hA0 ((measureReal_eq_zero_iff).2 hcon)
    obtain ⟨hpos, -⟩ := h.2 x hμA
    have he : propensity μ T X x ≠ 0 := ne_of_gt hpos
    have h_int : ∫ ω in T ∩ X ⁻¹' {x}, Y₁ ω ∂μ =
        propensity μ T X x * ∫ ω in X ⁻¹' {x}, Y₁ ω ∂μ :=
      setIntegral_inter_eq_propensity_mul hY₁ h.1 x
    have h_meas : μ.real (T ∩ X ⁻¹' {x}) =
        propensity μ T X x * μ.real (X ⁻¹' {x}) :=
      measureReal_inter_preimage_eq_propensity_mul x
    have h_obs : (observed T Y₀ Y₁) =ᵐ[μ[|T ∩ X ⁻¹' {x}]] Y₁ := by
      filter_upwards [ae_cond_mem hS] with ω hω
      exact observed_eq_on_treated T Y₀ Y₁ hω.1
    rw [integral_congr_ae h_obs, integral_cond_eq_inv_mul, h_int, h_meas]
    have hprod : propensity μ T X x * μ.real (X ⁻¹' {x}) ≠ 0 := mul_ne_zero he hA0
    have hring : μ.real (X ⁻¹' {x}) * ((propensity μ T X x * μ.real (X ⁻¹' {x}))⁻¹ *
        (propensity μ T X x * ∫ ω in X ⁻¹' {x}, Y₁ ω ∂μ)) =
        ((propensity μ T X x * μ.real (X ⁻¹' {x}))⁻¹ *
          (propensity μ T X x * μ.real (X ⁻¹' {x}))) * ∫ ω in X ⁻¹' {x}, Y₁ ω ∂μ := by
      ring
    rw [hring, inv_mul_cancel₀ hprod, one_mul]

/-- Per-cell standardization identity, control arm. -/
theorem per_cell_control {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {T : Set Ω} (hT : MeasurableSet T) {X : Ω → 𝒳}
    (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ} (hY₀ : Measurable Y₀)
    (hY₀i : Integrable Y₀ μ) (h : StronglyIgnorable μ T Y₀ X) (x : 𝒳) :
    μ.real (X ⁻¹' {x}) * ∫ ω, observed T Y₀ Y₁ ω ∂μ[|Tᶜ ∩ X ⁻¹' {x}] =
      ∫ ω in X ⁻¹' {x}, Y₀ ω ∂μ := by
  have hA : MeasurableSet (X ⁻¹' {x}) := hX (measurableSet_singleton x)
  have hSc : MeasurableSet (Tᶜ ∩ X ⁻¹' {x}) := hT.compl.inter hA
  by_cases hA0 : μ.real (X ⁻¹' {x}) = 0
  · have hμA0 : μ (X ⁻¹' {x}) = 0 := (measureReal_eq_zero_iff).1 hA0
    rw [hA0, zero_mul, Measure.restrict_eq_zero.2 hμA0]
    simp
  · have hμA : μ (X ⁻¹' {x}) ≠ 0 := fun hcon => hA0 ((measureReal_eq_zero_iff).2 hcon)
    obtain ⟨-, hlt⟩ := h.2 x hμA
    have h1e : (1 - propensity μ T X x) ≠ 0 := ne_of_gt (sub_pos.2 hlt)
    have hc : Tᶜ ∩ X ⁻¹' {x} = X ⁻¹' {x} \ T := by ext ω; simp [and_comm]
    have hsplit : ∫ ω in X ⁻¹' {x} ∩ T, Y₀ ω ∂μ + ∫ ω in X ⁻¹' {x} \ T, Y₀ ω ∂μ =
        ∫ ω in X ⁻¹' {x}, Y₀ ω ∂μ :=
      integral_inter_add_sdiff hT hY₀i.integrableOn
    have h_int_T : ∫ ω in T ∩ X ⁻¹' {x}, Y₀ ω ∂μ =
        propensity μ T X x * ∫ ω in X ⁻¹' {x}, Y₀ ω ∂μ :=
      setIntegral_inter_eq_propensity_mul hY₀ h.1 x
    rw [Set.inter_comm (X ⁻¹' {x}) T] at hsplit
    rw [h_int_T] at hsplit
    have h_int_C : ∫ ω in Tᶜ ∩ X ⁻¹' {x}, Y₀ ω ∂μ =
        (1 - propensity μ T X x) * ∫ ω in X ⁻¹' {x}, Y₀ ω ∂μ := by
      rw [hc]
      linear_combination hsplit
    have h_meas_T : μ.real (T ∩ X ⁻¹' {x}) =
        propensity μ T X x * μ.real (X ⁻¹' {x}) :=
      measureReal_inter_preimage_eq_propensity_mul x
    have h_union : (T ∩ X ⁻¹' {x}) ∪ (Tᶜ ∩ X ⁻¹' {x}) = X ⁻¹' {x} := by
      ext ω
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
      by_cases h : ω ∈ T <;> simp [h]
    have h_disj : Disjoint (T ∩ X ⁻¹' {x}) (Tᶜ ∩ X ⁻¹' {x}) :=
      Set.disjoint_left.2 fun ω h1 h2 => h2.1 h1.1
    have h_real_add : μ.real (X ⁻¹' {x}) =
        μ.real (T ∩ X ⁻¹' {x}) + μ.real (Tᶜ ∩ X ⁻¹' {x}) := by
      have hru : μ.real ((T ∩ X ⁻¹' {x}) ∪ (Tᶜ ∩ X ⁻¹' {x})) =
          μ.real (T ∩ X ⁻¹' {x}) + μ.real (Tᶜ ∩ X ⁻¹' {x}) :=
        measureReal_union h_disj hSc
      rw [h_union] at hru
      exact hru
    have h_meas_C : μ.real (Tᶜ ∩ X ⁻¹' {x}) =
        (1 - propensity μ T X x) * μ.real (X ⁻¹' {x}) := by
      have h1 := h_real_add
      rw [h_meas_T] at h1
      linear_combination -h1
    have h_obs : (observed T Y₀ Y₁) =ᵐ[μ[|Tᶜ ∩ X ⁻¹' {x}]] Y₀ := by
      filter_upwards [ae_cond_mem hSc] with ω hω
      exact observed_eq_on_control T Y₀ Y₁ hω.1
    rw [integral_congr_ae h_obs, integral_cond_eq_inv_mul, h_int_C, h_meas_C]
    have hprod : (1 - propensity μ T X x) * μ.real (X ⁻¹' {x}) ≠ 0 :=
      mul_ne_zero h1e hA0
    have hring : μ.real (X ⁻¹' {x}) * (((1 - propensity μ T X x) * μ.real (X ⁻¹' {x}))⁻¹ *
        ((1 - propensity μ T X x) * ∫ ω in X ⁻¹' {x}, Y₀ ω ∂μ)) =
        (((1 - propensity μ T X x) * μ.real (X ⁻¹' {x}))⁻¹ *
          ((1 - propensity μ T X x) * μ.real (X ⁻¹' {x}))) * ∫ ω in X ⁻¹' {x}, Y₀ ω ∂μ := by
      ring
    rw [hring, inv_mul_cancel₀ hprod, one_mul]


/-- **Standardization, treated arm** (the g-formula for a finite covariate): under conditional
exchangeability `T ⊥ Y₁ | X` with overlap (`StronglyIgnorable μ T Y₁ X`), for a measurable,
integrable treated potential outcome `Y₁` and a covariate `X` with finitely many values,
`E[Y₁] = ∑_x P(X = x) E[Y | T, X = x]` with `Y = observed T Y₀ Y₁` (consistency) and
`E[· | T, X = x]` the mean under the conditional law `μ[|T ∩ {X = x}]`. Covariate values of
probability zero contribute `0`. -/
theorem integral_eq_sum_standardized_treated {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype 𝒳] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {T : Set Ω} (hT : MeasurableSet T) {X : Ω → 𝒳}
    (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ} (hY₁ : Measurable Y₁) (hY₁i : Integrable Y₁ μ)
    (h : StronglyIgnorable μ T Y₁ X) :
    ∫ ω, Y₁ ω ∂μ =
      ∑ x, μ.real (X ⁻¹' {x}) * ∫ ω, observed T Y₀ Y₁ ω ∂μ[|T ∩ X ⁻¹' {x}] := by
  rw [integral_eq_sum_preimage hX hY₁i]
  exact Finset.sum_congr rfl fun x _ => (per_cell_treated hT hX hY₁ h x).symm

/-- **Standardization, control arm**: under `StronglyIgnorable μ T Y₀ X`, for a measurable,
integrable `Y₀`, `E[Y₀] = ∑_x P(X = x) E[Y | Tᶜ, X = x]`. -/
theorem integral_eq_sum_standardized_control {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype 𝒳] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {T : Set Ω} (hT : MeasurableSet T) {X : Ω → 𝒳}
    (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ} (hY₀ : Measurable Y₀) (hY₀i : Integrable Y₀ μ)
    (h : StronglyIgnorable μ T Y₀ X) :
    ∫ ω, Y₀ ω ∂μ =
      ∑ x, μ.real (X ⁻¹' {x}) * ∫ ω, observed T Y₀ Y₁ ω ∂μ[|Tᶜ ∩ X ⁻¹' {x}] := by
  rw [integral_eq_sum_preimage hX hY₀i]
  exact Finset.sum_congr rfl fun x _ => (per_cell_control hT hX hY₀ hY₀i h x).symm

/-- **Identification of the ATE by standardization**: under conditional exchangeability of the
treatment for the pair `(Y₀, Y₁)` given a finitely-valued covariate `X`, with overlap
`0 < P(T | X = x) < 1` on every value of positive probability (`StronglyIgnorable`), and
measurable integrable potential outcomes,
`E[Y₁ - Y₀] = ∑_x P(X = x) (E[Y | T, X = x] - E[Y | Tᶜ, X = x])`. -/
theorem integral_sub_eq_sum_standardized {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype 𝒳] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {T : Set Ω} (hT : MeasurableSet T) {X : Ω → 𝒳}
    (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ} (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁)
    (hY₀i : Integrable Y₀ μ) (hY₁i : Integrable Y₁ μ)
    (h : StronglyIgnorable μ T (fun ω => (Y₀ ω, Y₁ ω)) X) :
    ∫ ω, (Y₁ ω - Y₀ ω) ∂μ =
      ∑ x, μ.real (X ⁻¹' {x}) *
        (∫ ω, observed T Y₀ Y₁ ω ∂μ[|T ∩ X ⁻¹' {x}] -
          ∫ ω, observed T Y₀ Y₁ ω ∂μ[|Tᶜ ∩ X ⁻¹' {x}]) := by
  have h1 : StronglyIgnorable μ T Y₁ X := h.comp measurable_snd
  have h0 : StronglyIgnorable μ T Y₀ X := h.comp measurable_fst
  have e1 := integral_eq_sum_standardized_treated (Y₀ := Y₀) hT hX hY₁ hY₁i h1
  have e0 := integral_eq_sum_standardized_control (Y₁ := Y₁) hT hX hY₀ hY₀i h0
  rw [integral_sub hY₁i hY₀i, e1, e0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_sub]

end MathlibExt.Probability.Causality
