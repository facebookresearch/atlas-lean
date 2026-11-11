/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.DoubleRobustness

/-!
# Tests for double robustness of the AIPW score

A randomized experiment on four equally likely units, with no covariates (the trivial
σ-algebra `⊥`): units `0, 1` are treated, `Y₁ = (2, 0, 0, 2)`, `Y₀ = (0, 1, 1, 0)`. The true
nuisances are `e* = 1/2`, `μ₁* = 1`, `μ₀* = 1/2`, and the ATE is `1/2`. Candidate nuisances are
constants `e, g₀, g₁`, and the expectation of the AIPW score is computed directly as a finite sum:

* both nuisances wrong (`e = 1/4`, `g₀ = g₁ = 0`): bias `7/6 ≠ 0`, which also equals the
  product-of-errors formula of `integral_aipwScore_sub`;
* propensity correct only (`e = 1/2`, `g₀ = g₁ = 0`): bias `0`;
* outcome regressions correct only (`e = 1/4`, `g₀ = 1/2`, `g₁ = 1`): bias `0`.

Then the hypotheses of the theorems are verified on the model (non-vacuity), and the theorems
are applied to it.
-/

@[expose] public section

open MeasureTheory MathlibExt.Probability.Causality

namespace MathlibExtTest.Probability.Causality.AugmentedIPW

/-- The uniform law on four units. -/
noncomputable def unif4 : Measure (Fin 4) :=
  (4⁻¹ : ENNReal) • Measure.count

instance : IsProbabilityMeasure unif4 := by
  constructor
  rw [unif4, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  simp [ENat.card_eq_coe_fintype_card]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma unif4_real_singleton (i : Fin 4) : unif4.real {i} = 1 / 4 := by
  simp [unif4, measureReal_def]

lemma integral_unif4 (f : Fin 4 → ℝ) :
    ∫ i, f i ∂unif4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  rw [integral_fintype Integrable.of_finite]
  simp only [unif4_real_singleton, smul_eq_mul, Fin.sum_univ_four]
  ring

/-- The treated units. -/
def T : Set (Fin 4) := {0, 1}

/-- Treated potential outcomes. -/
def Y₁ : Fin 4 → ℝ := ![2, 0, 0, 2]

/-- Control potential outcomes. -/
def Y₀ : Fin 4 → ℝ := ![0, 1, 1, 0]

/-- The AIPW score with constant candidate nuisances, at the observed outcome. -/
noncomputable abbrev score (e g₀ g₁ : ℝ) : Fin 4 → ℝ :=
  aipwScore T (observed T Y₀ Y₁) (fun _ => e) (fun _ => g₀) (fun _ => g₁)

/-- The expectation of the score as an explicit function of the constant nuisances. -/
lemma integral_score (e g₀ g₁ : ℝ) :
    ∫ i, score e g₀ g₁ i ∂unif4 =
      g₁ - g₀ + (1 - g₁) / e / 2 - (1 - 2 * g₀) / (1 - e) / 4 := by
  rw [integral_unif4]
  simp [aipwScore, observed, T, Y₀, Y₁, Set.indicator]
  ring

/-- The average treatment effect of the model is `1/2`. -/
lemma integral_ate : ∫ i, (Y₁ i - Y₀ i) ∂unif4 = 1 / 2 := by
  rw [integral_unif4]
  simp [Y₀, Y₁]
  norm_num

/-! ### Direct computations on the finite model -/

/-- **Both nuisances wrong**: `e = 1/4 ≠ 1/2`, `g₁ = 0 ≠ 1`, `g₀ = 0 ≠ 1/2`. The AIPW score is
biased: `E[ψ] - ATE = 7/6`. -/
theorem bias_both_wrong : ∫ i, score (1 / 4) 0 0 i ∂unif4 - ∫ i, (Y₁ i - Y₀ i) ∂unif4 = 7 / 6 := by
  rw [integral_score, integral_ate]
  norm_num

theorem bias_both_wrong_ne_zero :
    ∫ i, score (1 / 4) 0 0 i ∂unif4 ≠ ∫ i, (Y₁ i - Y₀ i) ∂unif4 := by
  intro h
  have := bias_both_wrong
  rw [h, sub_self] at this
  norm_num at this

/-- The bias `7/6` is the product-of-errors formula
`(e* - e) ((μ₁* - g₁) / e + (μ₀* - g₀) / (1 - e))` at `e* = 1/2`, `μ₁* = 1`, `μ₀* = 1/2`. -/
example : ((1 : ℝ) / 2 - 1 / 4) * ((1 - 0) / (1 / 4) + (1 / 2 - 0) / (1 - 1 / 4)) = 7 / 6 := by
  norm_num

/-- **Propensity correct only**: `e = 1/2 = e*`, while `g₁ = 0 ≠ 1` and `g₀ = 0 ≠ 1/2`. -/
theorem bias_propensity_correct_only :
    ∫ i, score (1 / 2) 0 0 i ∂unif4 = ∫ i, (Y₁ i - Y₀ i) ∂unif4 := by
  rw [integral_score, integral_ate]
  norm_num

/-- **Outcome regressions correct only**: `g₁ = 1 = μ₁*`, `g₀ = 1/2 = μ₀*`, while
`e = 1/4 ≠ 1/2`. -/
theorem bias_outcome_correct_only :
    ∫ i, score (1 / 4) (1 / 2) 1 i ∂unif4 = ∫ i, (Y₁ i - Y₀ i) ∂unif4 := by
  rw [integral_score, integral_ate]
  norm_num

/-! ### The true nuisances, and the hypotheses of the theorems on the model -/

lemma propensity_true : unif4[T.indicator (1 : Fin 4 → ℝ) | ⊥] = fun _ => 1 / 2 := by
  rw [condExp_bot, integral_unif4]
  simp [T, Set.indicator]
  norm_num

lemma outcome₁_true : unif4[Y₁ | ⊥] = fun _ => 1 := by
  rw [condExp_bot, integral_unif4]
  simp [Y₁]
  norm_num

lemma outcome₀_true : unif4[Y₀ | ⊥] = fun _ => 1 / 2 := by
  rw [condExp_bot, integral_unif4]
  simp [Y₀]
  norm_num

/-- Mean exchangeability for the treated arm holds on the model. -/
lemma hex₁ :
    unif4[T.indicator Y₁ | ⊥] =ᵐ[unif4] unif4[T.indicator 1 | ⊥] * unif4[Y₁ | ⊥] := by
  refine Filter.Eventually.of_forall fun _ => ?_
  rw [propensity_true, outcome₁_true, condExp_bot, integral_unif4]
  simp [T, Y₁, Set.indicator]
  norm_num

/-- Mean exchangeability for the control arm holds on the model. -/
lemma hex₀ :
    unif4[Tᶜ.indicator Y₀ | ⊥] =ᵐ[unif4] (1 - unif4[T.indicator 1 | ⊥]) * unif4[Y₀ | ⊥] := by
  refine Filter.Eventually.of_forall fun _ => ?_
  rw [propensity_true, outcome₀_true, condExp_bot, integral_unif4]
  simp [T, Y₀, Set.indicator]
  norm_num

lemma hT : MeasurableSet T := .of_discrete

/-- `ε ≤ e ≤ 1 - ε` for the candidate propensities `1/4` and `1/2`, with `ε = 1/4`. -/
lemma bounded (e : ℝ) (h₀ : 1 / 4 ≤ e) (h₁ : e ≤ 3 / 4) :
    ∀ᵐ _ ∂unif4, (1 : ℝ) / 4 ≤ e ∧ e ≤ 1 - 1 / 4 :=
  Filter.Eventually.of_forall fun _ => ⟨h₀, by linarith⟩

/-! ### The theorems applied to the model -/

/-- The exact identity on the both-wrong candidates reproduces the bias `7/6`. -/
example : ∫ i, score (1 / 4) 0 0 i ∂unif4 - ∫ i, (Y₁ i - Y₀ i) ∂unif4 = 7 / 6 := by
  rw [integral_aipwScore_sub bot_le hT (Filter.EventuallyEq.refl _ _) .of_finite .of_finite
    hex₁ hex₀ stronglyMeasurable_const stronglyMeasurable_const stronglyMeasurable_const
    (integrable_const _) (integrable_const _) (by norm_num : (0 : ℝ) < 1 / 4)
    (bounded _ le_rfl (by norm_num)), propensity_true, outcome₀_true, outcome₁_true]
  simp only [integral_const, probReal_univ, one_smul]
  norm_num

/-- `integral_aipwScore_of_propensity` on the model: propensity correct, outcomes wrong. -/
example : ∫ i, score (1 / 2) 0 0 i ∂unif4 = ∫ i, (Y₁ i - Y₀ i) ∂unif4 :=
  integral_aipwScore_of_propensity bot_le hT (Filter.EventuallyEq.refl _ _) .of_finite .of_finite
    hex₁ hex₀ stronglyMeasurable_const stronglyMeasurable_const stronglyMeasurable_const
    (integrable_const _) (integrable_const _) (by norm_num : (0 : ℝ) < 1 / 4)
    (bounded _ (by norm_num) (by norm_num)) (by rw [propensity_true])

/-- `integral_aipwScore_of_outcome` on the model: outcomes correct, propensity wrong. -/
example : ∫ i, score (1 / 4) (1 / 2) 1 i ∂unif4 = ∫ i, (Y₁ i - Y₀ i) ∂unif4 :=
  integral_aipwScore_of_outcome bot_le hT (Filter.EventuallyEq.refl _ _) .of_finite .of_finite
    hex₁ hex₀ stronglyMeasurable_const stronglyMeasurable_const stronglyMeasurable_const
    (integrable_const _) (integrable_const _) (by norm_num : (0 : ℝ) < 1 / 4)
    (bounded _ le_rfl (by norm_num)) (by rw [outcome₀_true]) (by rw [outcome₁_true])

/-- `integrable_aipwScore` on the model. -/
example : Integrable (score (1 / 4) 0 0) unif4 :=
  integrable_aipwScore hT (Filter.EventuallyEq.refl _ _) .of_finite .of_finite
    aestronglyMeasurable_const (integrable_const _) (integrable_const _)
    (by norm_num : (0 : ℝ) < 1 / 4) (bounded _ le_rfl (by norm_num))

end MathlibExtTest.Probability.Causality.AugmentedIPW
