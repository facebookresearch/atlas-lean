/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# The augmented inverse-probability-weighted (AIPW) score with fixed nuisance functions

A binary treatment is the event `T`, `X : Ω → 𝒳` is the covariate, `Y` the observed outcome and
`Y₀, Y₁` the potential outcomes. The *candidate* nuisance functions are fixed functions of the
covariate value: a propensity `e : 𝒳 → ℝ` and outcome regressions `m₀, m₁ : 𝒳 → ℝ` (written
`μ₀, μ₁` in most texts). They are arguments, not estimates: nothing in this file is fitted to data.

The AIPW score for the average treatment effect `E[Y₁ - Y₀]` (Robins, Rotnitzky & Zhao 1994) is
`ψ = m₁(X) - m₀(X) + 1_T (Y - m₁(X)) / e(X) - 1_{Tᶜ} (Y - m₀(X)) / (1 - e(X))`.

## Main definitions

* `aipwScore T X Y e m₀ m₁`: the score above, a function of the observed data `(T, X, Y)`.
* `AIPWAssumptions μ T X Y Y₀ Y₁`: the identifying assumptions in primitive terms, with the true
  propensity `π = P(T | X) = μ[1_T | σ(X)]`: consistency `Y = observed T Y₀ Y₁`, mean
  exchangeability `E[1_T Y₁ | X] = π E[Y₁ | X]` and `E[1_{Tᶜ} Y₀ | X] = P(Tᶜ | X) E[Y₀ | X]`, and
  positivity (strong overlap) `ε ≤ π ≤ 1 - ε` almost surely for some `ε > 0`.

## Main results

* `aipwScore_of_mem`, `aipwScore_of_notMem`: the score on treated and on control units.
* `aipwScore_eq_of_consistency`: under consistency, the score in terms of the potential outcomes.
* Form when the propensity is correct: `aipwScore_eq_ipw_sub` writes the score as the IPW
  contrast `1_T Y / e(X) - 1_{Tᶜ} Y / (1 - e(X))` minus the propensity residual `1_T - e(X)`
  times a function of `X`, and `condExp_propensityResidual_mul` shows that this residual term
  has conditional mean zero given `X` when `e(X) = P(T | X)`.
* Form when the outcome regressions are correct: by definition the score is the regression
  contrast `m₁(X) - m₀(X)` plus inverse-propensity-weighted outcome residuals, and
  `condExp_outcomeResidual_treated`, `condExp_outcomeResidual_control` show that each weighted
  residual has conditional mean zero given `X` when `m_a(X) = E[Y_a | X]`, under consistency and
  mean exchangeability, for any candidate propensity bounded away from `0` and `1`.

## Not covered

Double robustness (`E[ψ] = E[Y₁ - Y₀]` when either the propensity or the outcome regressions are
correct) is not stated here, nor any property of estimated nuisance functions (cross-fitting,
rates, asymptotic normality), nor missing-outcome versions of the score.

## Reuse search (API-00)

Searched Mathlib `v4.35.0`, cslib, Physlib and this repository at `origin/main` `53666a3c1`
for `AIPW`, `augmented inverse`, `doubly robust` and `inverse probability`: no AIPW score exists.
`observed` (consistency) is reused from `MathlibExt.Probability.Causality.CausalIdentification`,
whose `integral_ipw_treated_condExp` uses the same conditional-expectation form of mean
exchangeability and of the propensity as `AIPWAssumptions`.

## References

* J. M. Robins, A. Rotnitzky and L. P. Zhao, *Estimation of regression coefficients when some
  regressors are not always observed*, JASA 89(427) (1994), 846–866.
* H. Bang and J. M. Robins, *Doubly robust estimation in missing data and causal inference
  models*, Biometrics 61(4) (2005), 962–973.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality

open MeasureTheory Filter

section Score

variable {Ω 𝒳 : Type*}

/-- The **AIPW score** for the average treatment effect with candidate propensity `e` and
candidate outcome regressions `m₀, m₁`, all fixed functions of the covariate value:
`m₁(X) - m₀(X) + 1_T (Y - m₁(X)) / e(X) - 1_{Tᶜ} (Y - m₀(X)) / (1 - e(X))`. Since Lean sets
`x / 0 = 0`, a unit with `e(X) = 0` (resp. `e(X) = 1`) has its treated (resp. control) residual
dropped; positivity of the candidate rules this out. -/
noncomputable def aipwScore (T : Set Ω) (X : Ω → 𝒳) (Y : Ω → ℝ) (e m₀ m₁ : 𝒳 → ℝ) (ω : Ω) :
    ℝ :=
  m₁ (X ω) - m₀ (X ω) + T.indicator (fun ω => (Y ω - m₁ (X ω)) / e (X ω)) ω -
    Tᶜ.indicator (fun ω => (Y ω - m₀ (X ω)) / (1 - e (X ω))) ω

variable {T : Set Ω} {X : Ω → 𝒳} {Y Y₀ Y₁ : Ω → ℝ} {e m₀ m₁ : 𝒳 → ℝ} {ω : Ω}

/-- The AIPW score of a treated unit. -/
theorem aipwScore_of_mem (h : ω ∈ T) :
    aipwScore T X Y e m₀ m₁ ω = m₁ (X ω) - m₀ (X ω) + (Y ω - m₁ (X ω)) / e (X ω) := by
  simp [aipwScore, h]

/-- The AIPW score of a control unit. -/
theorem aipwScore_of_notMem (h : ω ∉ T) :
    aipwScore T X Y e m₀ m₁ ω = m₁ (X ω) - m₀ (X ω) - (Y ω - m₀ (X ω)) / (1 - e (X ω)) := by
  simp [aipwScore, h]

/-- Under consistency, `Y = observed T Y₀ Y₁`, the AIPW score in terms of the potential
outcomes: the treated residual uses `Y₁`, the control residual `Y₀`. -/
theorem aipwScore_eq_of_consistency (hY : ∀ ω, Y ω = observed T Y₀ Y₁ ω) (ω : Ω) :
    aipwScore T X Y e m₀ m₁ ω = m₁ (X ω) - m₀ (X ω) +
      T.indicator (fun ω => (Y₁ ω - m₁ (X ω)) / e (X ω)) ω -
        Tᶜ.indicator (fun ω => (Y₀ ω - m₀ (X ω)) / (1 - e (X ω))) ω := by
  by_cases h : ω ∈ T <;> simp [aipwScore, hY, observed, h]

/-- **The AIPW score as an augmented IPW contrast.** When `e(X) ∉ {0, 1}`, the score is the IPW
contrast `1_T Y / e(X) - 1_{Tᶜ} Y / (1 - e(X))` minus the propensity residual `1_T - e(X)`
times `m₁(X) / e(X) + m₀(X) / (1 - e(X))`. When `e` is the true propensity this residual term
has conditional mean zero given `X` (`condExp_propensityResidual_mul`). -/
theorem aipwScore_eq_ipw_sub (he₀ : e (X ω) ≠ 0) (he₁ : e (X ω) ≠ 1) :
    aipwScore T X Y e m₀ m₁ ω =
      T.indicator (fun ω => Y ω / e (X ω)) ω - Tᶜ.indicator (fun ω => Y ω / (1 - e (X ω))) ω -
        (T.indicator 1 ω - e (X ω)) * (m₁ (X ω) / e (X ω) + m₀ (X ω) / (1 - e (X ω))) := by
  have he₁' : 1 - e (X ω) ≠ 0 := sub_ne_zero.2 he₁.symm
  by_cases h : ω ∈ T <;> simp [aipwScore, h] <;> field_simp <;> ring

end Score

section Assumptions

variable {Ω 𝒳 : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [m𝒳 : MeasurableSpace 𝒳]

/-- The identifying assumptions for the average treatment effect of a binary treatment `T` given
a covariate `X`, in primitive terms. With `σ(X) = MeasurableSpace.comap X m𝒳` and the true
propensity `π = μ[1_T | σ(X)]`:
* consistency: the observed outcome is `Y₁` on `T` and `Y₀` off it;
* mean exchangeability: `E[1_T Y₁ | X] = π E[Y₁ | X]` and `E[1_{Tᶜ} Y₀ | X] = P(Tᶜ | X) E[Y₀ | X]`
  (implied by `Y_a ⊥ T | X`);
* positivity (strong overlap): `ε ≤ π ≤ 1 - ε` almost surely, for some `ε > 0`. -/
structure AIPWAssumptions (μ : Measure Ω) (T : Set Ω) (X : Ω → 𝒳) (Y Y₀ Y₁ : Ω → ℝ) :
    Prop where
  consistency : ∀ ω, Y ω = observed T Y₀ Y₁ ω
  meanExch_treated : μ[T.indicator Y₁ | m𝒳.comap X] =ᵐ[μ]
    μ[T.indicator (1 : Ω → ℝ) | m𝒳.comap X] * μ[Y₁ | m𝒳.comap X]
  meanExch_control : μ[Tᶜ.indicator Y₀ | m𝒳.comap X] =ᵐ[μ]
    μ[Tᶜ.indicator (1 : Ω → ℝ) | m𝒳.comap X] * μ[Y₀ | m𝒳.comap X]
  positivity : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε ≤ μ[T.indicator (1 : Ω → ℝ) | m𝒳.comap X] ω ∧
    μ[T.indicator (1 : Ω → ℝ) | m𝒳.comap X] ω ≤ 1 - ε

/-- **Correct propensity: the augmentation has conditional mean zero.** If the candidate
propensity is the true one, `e(X) = μ[1_T | σ(X)]` a.s., then for every bounded measurable
`h`, `E[(1_T - e(X)) h(X) | X] = 0`. With `h = m₁ / e + m₀ / (1 - e)` this is the term that
`aipwScore_eq_ipw_sub` subtracts from the IPW contrast. -/
theorem condExp_propensityResidual_mul [IsFiniteMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) {e h : 𝒳 → ℝ} (he : Measurable e) (hh : Measurable h)
    {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C)
    (hprop : μ[T.indicator 1 | m𝒳.comap X] =ᵐ[μ] fun ω => e (X ω)) :
    μ[fun ω => (T.indicator 1 ω - e (X ω)) * h (X ω) | m𝒳.comap X] =ᵐ[μ] 0 := by
  have hm : m𝒳.comap X ≤ mΩ := hX.comap_le
  have hXm : Measurable[m𝒳.comap X] X := comap_measurable X
  have hhX : StronglyMeasurable[m𝒳.comap X] fun ω => h (X ω) := (hh.comp hXm).stronglyMeasurable
  have heX : StronglyMeasurable[m𝒳.comap X] fun ω => e (X ω) := (he.comp hXm).stronglyMeasurable
  have h1 : Integrable (T.indicator (1 : Ω → ℝ)) μ := (integrable_const 1).indicator hT
  have heXi : Integrable (fun ω => e (X ω)) μ := integrable_condExp.congr hprop
  have hg : Integrable (T.indicator 1 - fun ω => e (X ω)) μ := h1.sub heXi
  have hfg : Integrable ((fun ω => h (X ω)) * (T.indicator 1 - fun ω => e (X ω))) μ :=
    hg.bdd_mul (hhX.mono hm).aestronglyMeasurable (Eventually.of_forall fun ω => hC _)
  have hcomm : (fun ω => (T.indicator 1 ω - e (X ω)) * h (X ω)) =
      (fun ω => h (X ω)) * (T.indicator 1 - fun ω => e (X ω)) := by
    funext ω; simp [mul_comm]
  rw [hcomm]
  have hsub := condExp_sub h1 heXi (m𝒳.comap X)
  rw [condExp_of_stronglyMeasurable hm heX heXi] at hsub
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hhX hfg hg, hsub, hprop]
    with ω h₁ h₂ h₃
  simp [h₁, h₂, h₃]

/-- **Correct outcome regression, treated arm: the weighted residual has conditional mean zero.**
Under consistency and mean exchangeability for `Y₁`, if the candidate regression is correct,
`m₁(X) = E[Y₁ | X]` a.s., then `E[1_T (Y - m₁(X)) / e(X) | X] = 0` for every measurable candidate
propensity with `e ≥ ε > 0`; the propensity need not be correct. -/
theorem condExp_outcomeResidual_treated [IsFiniteMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) {Y Y₀ Y₁ : Ω → ℝ}
    (hcons : ∀ ω, Y ω = observed T Y₀ Y₁ ω) (hY₁ : Integrable Y₁ μ)
    (hexch : μ[T.indicator Y₁ | m𝒳.comap X] =ᵐ[μ]
      μ[T.indicator 1 | m𝒳.comap X] * μ[Y₁ | m𝒳.comap X])
    {e m₁ : 𝒳 → ℝ} (he : Measurable e) (hm₁ : Measurable m₁) {ε : ℝ} (hε : 0 < ε)
    (heε : ∀ x, ε ≤ e x) (hout : μ[Y₁ | m𝒳.comap X] =ᵐ[μ] fun ω => m₁ (X ω)) :
    μ[T.indicator (fun ω => (Y ω - m₁ (X ω)) / e (X ω)) | m𝒳.comap X] =ᵐ[μ] 0 := by
  have hm : m𝒳.comap X ≤ mΩ := hX.comap_le
  have hXm : Measurable[m𝒳.comap X] X := comap_measurable X
  have hfX : StronglyMeasurable[m𝒳.comap X] fun ω => (e (X ω))⁻¹ :=
    ((he.comp hXm).inv).stronglyMeasurable
  have hmX : StronglyMeasurable[m𝒳.comap X] fun ω => m₁ (X ω) :=
    (hm₁.comp hXm).stronglyMeasurable
  have hmXi : Integrable (fun ω => m₁ (X ω)) μ := integrable_condExp.congr hout
  have hTY : Integrable (T.indicator Y₁) μ := hY₁.indicator hT
  have hTm : Integrable (T.indicator fun ω => m₁ (X ω)) μ := hmXi.indicator hT
  have hg : Integrable (T.indicator Y₁ - T.indicator fun ω => m₁ (X ω)) μ := hTY.sub hTm
  have hpt : T.indicator (fun ω => (Y ω - m₁ (X ω)) / e (X ω)) =
      (fun ω => (e (X ω))⁻¹) * (T.indicator Y₁ - T.indicator fun ω => m₁ (X ω)) := by
    funext ω
    by_cases h : ω ∈ T <;> simp [hcons, observed, h, div_eq_inv_mul]
  have hbdd : ∀ᵐ ω ∂μ, ‖(e (X ω))⁻¹‖ ≤ ε⁻¹ := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hε.trans_le (heε _))]
    exact inv_anti₀ hε (heε _)
  have hfg : Integrable ((fun ω => (e (X ω))⁻¹) *
      (T.indicator Y₁ - T.indicator fun ω => m₁ (X ω))) μ :=
    hg.bdd_mul (hfX.mono hm).aestronglyMeasurable hbdd
  have hTm' : (T.indicator fun ω => m₁ (X ω)) = (fun ω => m₁ (X ω)) * T.indicator 1 := by
    funext ω; by_cases h : ω ∈ T <;> simp [h]
  have hpull : μ[T.indicator (fun ω => m₁ (X ω)) | m𝒳.comap X] =ᵐ[μ]
      (fun ω => m₁ (X ω)) * μ[T.indicator 1 | m𝒳.comap X] := by
    rw [hTm']
    exact condExp_mul_of_stronglyMeasurable_left hmX (hTm' ▸ hTm)
      ((integrable_const 1).indicator hT)
  rw [hpt]
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hfX hfg hg,
    condExp_sub hTY hTm (m𝒳.comap X), hexch, hpull, hout] with ω h₁ h₂ h₃ h₄ h₅
  rw [h₁, Pi.mul_apply, h₂, Pi.sub_apply, h₃, h₄, Pi.mul_apply, Pi.mul_apply, h₅,
    Pi.zero_apply]
  ring

/-- **Correct outcome regression, control arm**: under consistency and mean exchangeability for
`Y₀`, if `m₀(X) = E[Y₀ | X]` a.s., then `E[1_{Tᶜ} (Y - m₀(X)) / (1 - e(X)) | X] = 0` for every
measurable candidate propensity with `e ≤ 1 - ε`, `ε > 0`. -/
theorem condExp_outcomeResidual_control [IsFiniteMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) {Y Y₀ Y₁ : Ω → ℝ}
    (hcons : ∀ ω, Y ω = observed T Y₀ Y₁ ω) (hY₀ : Integrable Y₀ μ)
    (hexch : μ[Tᶜ.indicator Y₀ | m𝒳.comap X] =ᵐ[μ]
      μ[Tᶜ.indicator 1 | m𝒳.comap X] * μ[Y₀ | m𝒳.comap X])
    {e m₀ : 𝒳 → ℝ} (he : Measurable e) (hm₀ : Measurable m₀) {ε : ℝ} (hε : 0 < ε)
    (heε : ∀ x, e x ≤ 1 - ε) (hout : μ[Y₀ | m𝒳.comap X] =ᵐ[μ] fun ω => m₀ (X ω)) :
    μ[Tᶜ.indicator (fun ω => (Y ω - m₀ (X ω)) / (1 - e (X ω))) | m𝒳.comap X] =ᵐ[μ] 0 := by
  have hcons' : ∀ ω, Y ω = observed Tᶜ Y₁ Y₀ ω := fun ω => by
    rw [hcons, observed, observed, compl_compl, add_comm]
  exact condExp_outcomeResidual_treated hT.compl hX hcons' hY₀ hexch (measurable_const.sub he)
    hm₀ hε (fun x => show ε ≤ 1 - e x by linarith [heε x]) hout

/-- `condExp_outcomeResidual_treated` under the bundled assumptions. -/
theorem AIPWAssumptions.condExp_outcomeResidual_treated [IsFiniteMeasure μ] {T : Set Ω}
    {X : Ω → 𝒳} {Y Y₀ Y₁ : Ω → ℝ} (hA : AIPWAssumptions μ T X Y Y₀ Y₁) (hT : MeasurableSet T)
    (hX : Measurable X) (hY₁ : Integrable Y₁ μ) {e m₁ : 𝒳 → ℝ} (he : Measurable e)
    (hm₁ : Measurable m₁) {ε : ℝ} (hε : 0 < ε) (heε : ∀ x, ε ≤ e x)
    (hout : μ[Y₁ | m𝒳.comap X] =ᵐ[μ] fun ω => m₁ (X ω)) :
    μ[T.indicator (fun ω => (Y ω - m₁ (X ω)) / e (X ω)) | m𝒳.comap X] =ᵐ[μ] 0 :=
  MathlibExt.Probability.Causality.condExp_outcomeResidual_treated hT hX hA.consistency hY₁
    hA.meanExch_treated he hm₁ hε heε hout

/-- `condExp_outcomeResidual_control` under the bundled assumptions. -/
theorem AIPWAssumptions.condExp_outcomeResidual_control [IsFiniteMeasure μ] {T : Set Ω}
    {X : Ω → 𝒳} {Y Y₀ Y₁ : Ω → ℝ} (hA : AIPWAssumptions μ T X Y Y₀ Y₁) (hT : MeasurableSet T)
    (hX : Measurable X) (hY₀ : Integrable Y₀ μ) {e m₀ : 𝒳 → ℝ} (he : Measurable e)
    (hm₀ : Measurable m₀) {ε : ℝ} (hε : 0 < ε) (heε : ∀ x, e x ≤ 1 - ε)
    (hout : μ[Y₀ | m𝒳.comap X] =ᵐ[μ] fun ω => m₀ (X ω)) :
    μ[Tᶜ.indicator (fun ω => (Y ω - m₀ (X ω)) / (1 - e (X ω))) | m𝒳.comap X] =ᵐ[μ] 0 :=
  MathlibExt.Probability.Causality.condExp_outcomeResidual_control hT hX hA.consistency hY₀
    hA.meanExch_control he hm₀ hε heε hout

end Assumptions

end MathlibExt.Probability.Causality
