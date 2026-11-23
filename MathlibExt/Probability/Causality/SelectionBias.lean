/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification
public import Mathlib.Probability.ConditionalProbability

/-!
# Selection bias: the observed difference in means is the ATT plus selection bias

For potential outcomes `Y₀, Y₁`, a treatment event `T` and the observed outcome
`Y = observed T Y₀ Y₁` (consistency), the observed difference in group means decomposes as
`E[Y | T] - E[Y | Tᶜ] = E[Y₁ - Y₀ | T] + (E[Y₀ | T] - E[Y₀ | Tᶜ])`: the average treatment effect
on the treated plus the selection bias, the difference between the groups in the untreated
outcome (Angrist and Pischke 2009, §2.1). Conditional means are integrals under Mathlib's
conditional measure `μ[|T]`.

## Main definitions

* `att`: the average treatment effect on the treated `E[Y₁ - Y₀ | T]`.
* `diffInGroupMeans`: the observed difference in group means `E[Y | T] - E[Y | Tᶜ]`.
* `selectionBias`: `E[Y₀ | T] - E[Y₀ | Tᶜ]`.

## Main results

* `diffInGroupMeans_observed_eq_att_add_selectionBias`: the decomposition, for integrable
  potential outcomes. No positivity is needed for the identity; when `0 < P(T) < 1` all terms
  are genuine conditional means.

## References

* J. D. Angrist and J.-S. Pischke, *Mostly Harmless Econometrics*, Princeton University Press
  (2009), §2.1.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality

open MeasureTheory ProbabilityTheory

/-- The **average treatment effect on the treated** `E[Y₁ - Y₀ | T]`, the mean of the unit
effect under the conditional law `μ[|T]` given the treated event `T`. -/
noncomputable def att {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : Set Ω)
    (Y₀ Y₁ : Ω → ℝ) : ℝ :=
  ∫ ω, (Y₁ ω - Y₀ ω) ∂μ[|T]

/-- The **observed difference in group means** `E[Y | T] - E[Y | Tᶜ]` of an outcome `Y`
(conditional means under `μ[|T]` and `μ[|Tᶜ]`). -/
noncomputable def diffInGroupMeans {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : Set Ω)
    (Y : Ω → ℝ) : ℝ :=
  ∫ ω, Y ω ∂μ[|T] - ∫ ω, Y ω ∂μ[|Tᶜ]

/-- The **selection bias** `E[Y₀ | T] - E[Y₀ | Tᶜ]`: the difference between the treated and
the control units in the untreated potential outcome. -/
noncomputable def selectionBias {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : Set Ω)
    (Y₀ : Ω → ℝ) : ℝ :=
  ∫ ω, Y₀ ω ∂μ[|T] - ∫ ω, Y₀ ω ∂μ[|Tᶜ]

/-- **Selection-bias decomposition**: for integrable potential outcomes and the observed
outcome `observed T Y₀ Y₁` (consistency), the observed difference in group means equals the
average treatment effect on the treated plus the selection bias,
`E[Y | T] - E[Y | Tᶜ] = E[Y₁ - Y₀ | T] + (E[Y₀ | T] - E[Y₀ | Tᶜ])`. No positivity is needed for
the identity; when `0 < P(T) < 1` the three terms are genuine conditional means. -/
theorem diffInGroupMeans_observed_eq_att_add_selectionBias {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {Y₀ Y₁ : Ω → ℝ} (hY₀ : Integrable Y₀ μ) (hY₁ : Integrable Y₁ μ) :
    diffInGroupMeans μ T (observed T Y₀ Y₁) = att μ T Y₀ Y₁ + selectionBias μ T Y₀ := by
  have hTc : MeasurableSet Tᶜ := hT.compl
  have hptT : ∀ ω ∈ T, observed T Y₀ Y₁ ω = Y₁ ω := by
    intro ω hω
    have hωTc : ω ∉ Tᶜ := by simpa using hω
    simp only [observed, Pi.add_apply, Set.indicator_of_mem hω (f := Y₁),
      Set.indicator_of_notMem hωTc (f := Y₀), add_zero, zero_add]
  have hptTc : ∀ ω ∈ Tᶜ, observed T Y₀ Y₁ ω = Y₀ ω := by
    intro ω hω
    have hωT : ω ∉ T := by simpa using hω
    simp only [observed, Pi.add_apply, Set.indicator_of_notMem hωT (f := Y₁),
      Set.indicator_of_mem hω (f := Y₀), add_zero, zero_add]
  have hsetT : ∫ ω in T, observed T Y₀ Y₁ ω ∂μ = ∫ ω in T, Y₁ ω ∂μ :=
    MeasureTheory.setIntegral_congr_fun (f := _) (g := _) hT hptT
  have hsetTc : ∫ ω in Tᶜ, observed T Y₀ Y₁ ω ∂μ = ∫ ω in Tᶜ, Y₀ ω ∂μ :=
    MeasureTheory.setIntegral_congr_fun (f := _) (g := _) hTc hptTc
  have hcondT : μ[|T] = (μ T)⁻¹ • μ.restrict T := rfl
  have hcondTc : μ[|Tᶜ] = (μ Tᶜ)⁻¹ • μ.restrict Tᶜ := rfl
  have hCT : ∫ ω, observed T Y₀ Y₁ ω ∂μ[|T] = ∫ ω, Y₁ ω ∂μ[|T] := by
    simp only [hcondT, MeasureTheory.integral_smul_measure, hsetT]
  have hCTc : ∫ ω, observed T Y₀ Y₁ ω ∂μ[|Tᶜ] = ∫ ω, Y₀ ω ∂μ[|Tᶜ] := by
    simp only [hcondTc, MeasureTheory.integral_smul_measure, hsetTc]
  have hY₁r : Integrable Y₁ (μ.restrict T) := hY₁.integrableOn (s := T)
  have hY₀r : Integrable Y₀ (μ.restrict T) := hY₀.integrableOn (s := T)
  have hSUB : ∫ ω, (Y₁ ω - Y₀ ω) ∂μ[|T]
      = ∫ ω, Y₁ ω ∂μ[|T] - ∫ ω, Y₀ ω ∂μ[|T] := by
    simp only [hcondT, MeasureTheory.integral_smul_measure,
      MeasureTheory.integral_sub hY₁r hY₀r, smul_eq_mul, mul_sub]
  simp only [diffInGroupMeans, att, selectionBias, hCT, hCTc, hSUB]
  ring

end MathlibExt.Probability.Causality
