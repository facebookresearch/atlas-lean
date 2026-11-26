/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.Standardization

import Mathlib.Tactic.FieldSimp

/-!
# Inverse probability weighting equals standardization

For finitely many covariate values, the inverse-probability-weighted mean of an observed
outcome in a treatment arm equals its standardized mean. Only positivity of that arm's
propensity in strata of positive mass is required for this observed-law identity.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality

open MeasureTheory ProbabilityTheory

/-- **Inverse probability weighting equals standardization** (Hernán and Robins,
*Causal Inference: What If*, Technical Point 2.3). Let `μ` be a probability measure, `T` a
measurable event, `X` a finitely-valued measurable covariate and `Y` an integrable observed
outcome. If `e(x) = P(T | X = x)` is positive on every stratum of positive mass, then
`1_T Y / e(X)` is integrable and its mean is `∑ x, P(X = x) E[Y | T, X = x]`, with each
conditional mean taken under the corresponding conditional measure. Null strata contribute
zero; no conditional exchangeability or upper bound strictly below one for `e` is needed. -/
theorem integral_ipw_eq_sum_standardized {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype 𝒳] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {T : Set Ω} (hT : MeasurableSet T) {X : Ω → 𝒳}
    (hX : Measurable X) {Y : Ω → ℝ} (hYi : Integrable Y μ)
    (hpos : ∀ x, μ (X ⁻¹' {x}) ≠ 0 → 0 < propensity μ T X x) :
    Integrable (T.indicator fun ω => Y ω / propensity μ T X (X ω)) μ ∧
      (∫ ω, T.indicator (fun ω => Y ω / propensity μ T X (X ω)) ω ∂μ) =
        ∑ x, μ.real (X ⁻¹' {x}) * ∫ ω, Y ω ∂μ[|T ∩ X ⁻¹' {x}] := by
  have hA (x : 𝒳) : MeasurableSet (X ⁻¹' {x}) := hX (measurableSet_singleton x)
  have heq (x : 𝒳) :
      Set.EqOn (T.indicator fun ω => Y ω / propensity μ T X (X ω))
        (fun ω => T.indicator Y ω * (propensity μ T X x)⁻¹) (X ⁻¹' {x}) := by
    intro ω hω
    have hx : X ω = x := hω
    by_cases hωT : ω ∈ T <;> simp [hωT, hx, div_eq_mul_inv]
  have hon (x : 𝒳) :
      IntegrableOn (T.indicator fun ω => Y ω / propensity μ T X (X ω)) (X ⁻¹' {x}) μ :=
    (((hYi.indicator hT).mul_const (propensity μ T X x)⁻¹).integrableOn).congr_fun
      (heq x).symm (hA x)
  have hint : Integrable (T.indicator fun ω => Y ω / propensity μ T X (X ω)) μ := by
    have hU : (⋃ x, X ⁻¹' {x}) = Set.univ := by ext ω; simp
    rw [← integrableOn_univ, ← hU]
    exact integrableOn_finite_iUnion.2 hon
  refine ⟨hint, ?_⟩
  rw [integral_eq_sum_preimage hX hint]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [setIntegral_congr_fun (hA x) (heq x), integral_mul_const, setIntegral_indicator hT,
    Set.inter_comm (X ⁻¹' {x}) T, integral_cond_eq_inv_mul]
  by_cases hx : μ (X ⁻¹' {x}) = 0
  · have htx : μ (T ∩ X ⁻¹' {x}) = 0 := measure_mono_null Set.inter_subset_right hx
    simp [Measure.restrict_eq_zero.2 htx, measureReal_def, hx]
  · have he := (hpos x hx).ne'
    have hxR := (measureReal_ne_zero_iff (measure_ne_top _ _)).2 hx
    rw [measureReal_inter_preimage_eq_propensity_mul]
    field_simp

end MathlibExt.Probability.Causality
