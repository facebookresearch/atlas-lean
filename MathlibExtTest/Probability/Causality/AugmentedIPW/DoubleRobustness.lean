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
  product-of-errors formula of `integral_aipwScoreOfSigma_sub`;
* propensity correct only (`e = 1/2`, `g₀ = g₁ = 0`): bias `0`;
* outcome regressions correct only (`e = 1/4`, `g₀ = 1/2`, `g₁ = 1`): bias `0`.

Then the hypotheses of the theorems are verified on the model (non-vacuity), and the theorems
are applied to it. Finally, a six-unit model with a binary covariate `X` and `m = σ(X)` applies
the theorems with a nontrivial σ-algebra and non-constant nuisances.
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
  aipwScoreOfSigma T (observed T Y₀ Y₁) (fun _ => e) (fun _ => g₀) (fun _ => g₁)

/-- The expectation of the score as an explicit function of the constant nuisances. -/
lemma integral_score (e g₀ g₁ : ℝ) :
    ∫ i, score e g₀ g₁ i ∂unif4 =
      g₁ - g₀ + (1 - g₁) / e / 2 - (1 - 2 * g₀) / (1 - e) / 4 := by
  rw [integral_unif4]
  simp [aipwScoreOfSigma, observed, T, Y₀, Y₁, Set.indicator]
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
  rw [integral_aipwScoreOfSigma_sub bot_le hT (Filter.EventuallyEq.refl _ _) .of_finite .of_finite
    hex₁ hex₀ stronglyMeasurable_const stronglyMeasurable_const stronglyMeasurable_const
    (integrable_const _) (integrable_const _) (by norm_num : (0 : ℝ) < 1 / 4)
    (bounded _ le_rfl (by norm_num)), propensity_true, outcome₀_true, outcome₁_true]
  simp only [integral_const, probReal_univ, one_smul]
  norm_num

/-- `integral_aipwScoreOfSigma_of_propensity` on the model: propensity correct, outcomes wrong. -/
example : ∫ i, score (1 / 2) 0 0 i ∂unif4 = ∫ i, (Y₁ i - Y₀ i) ∂unif4 :=
  integral_aipwScoreOfSigma_of_propensity bot_le hT (Filter.EventuallyEq.refl _ _) .of_finite
    .of_finite hex₁ hex₀ stronglyMeasurable_const stronglyMeasurable_const stronglyMeasurable_const
    (integrable_const _) (integrable_const _) (by norm_num : (0 : ℝ) < 1 / 4)
    (bounded _ (by norm_num) (by norm_num)) (by rw [propensity_true])

/-- `integral_aipwScoreOfSigma_of_outcome` on the model: outcomes correct, propensity wrong. -/
example : ∫ i, score (1 / 4) (1 / 2) 1 i ∂unif4 = ∫ i, (Y₁ i - Y₀ i) ∂unif4 :=
  integral_aipwScoreOfSigma_of_outcome bot_le hT (Filter.EventuallyEq.refl _ _) .of_finite
    .of_finite hex₁ hex₀ stronglyMeasurable_const stronglyMeasurable_const stronglyMeasurable_const
    (integrable_const _) (integrable_const _) (by norm_num : (0 : ℝ) < 1 / 4)
    (bounded _ le_rfl (by norm_num)) (by rw [outcome₀_true]) (by rw [outcome₁_true])

/-- `integrable_aipwScoreOfSigma` on the model. -/
example : Integrable (score (1 / 4) 0 0) unif4 :=
  integrable_aipwScoreOfSigma hT (Filter.EventuallyEq.refl _ _) .of_finite .of_finite
    aestronglyMeasurable_const (integrable_const _) (integrable_const _)
    (by norm_num : (0 : ℝ) < 1 / 4) (bounded _ le_rfl (by norm_num))

/-! ### A nontrivial covariate σ-algebra and non-constant nuisances

Six equally likely units, a binary covariate `X = 1{ω < 2}` with cells `{0, 1}` and
`{2, 3, 4, 5}`, and covariate information `m = σ(X)`. Units `0, 2` are treated, so the true
propensity is `1/2` on the first cell and `1/4` on the second. With `Y₁ = (3, 3, 2, 0, 2, 4)` and
`Y₀ = (1, 1, 0, 1, 0, -1)` mean exchangeability holds within each cell, and the true outcome
regressions are `μ₁* = (3 | 2)`, `μ₀* = (1 | 0)` on the two cells. -/

namespace Covariate

/-- The uniform law on six units. -/
noncomputable def unif6 : Measure (Fin 6) :=
  (6⁻¹ : ENNReal) • Measure.count

instance : IsProbabilityMeasure unif6 := by
  constructor
  rw [unif6, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  simp [ENat.card_eq_coe_fintype_card]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma unif6_real_singleton (i : Fin 6) : unif6.real {i} = 1 / 6 := by
  simp [unif6, measureReal_def]

lemma integral_unif6 (f : Fin 6 → ℝ) :
    ∫ i, f i ∂unif6 = (f 0 + f 1 + f 2 + f 3 + f 4 + f 5) / 6 := by
  rw [integral_fintype Integrable.of_finite]
  simp only [unif6_real_singleton, smul_eq_mul, Fin.sum_univ_six]
  ring

/-- The binary covariate. -/
def X (i : Fin 6) : Bool := decide (i.val < 2)

/-- The covariate information, `σ(X)`. -/
abbrev mX : MeasurableSpace (Fin 6) := MeasurableSpace.comap X inferInstance

lemma mX_le : mX ≤ (inferInstance : MeasurableSpace (Fin 6)) :=
  (measurable_of_finite X).comap_le

/-- A function of the covariate, `a` on the first cell and `c` on the second. -/
def cell (a c : ℝ) (i : Fin 6) : ℝ := cond (X i) a c

lemma stronglyMeasurable_cell (a c : ℝ) : StronglyMeasurable[mX] (cell a c) :=
  ((Measurable.of_discrete (f := fun b : Bool => cond b a c)).comp
    (comap_measurable X)).stronglyMeasurable

/-- The conditional expectation given `X` is the cell average. -/
lemma condExp_eq_cell (f : Fin 6 → ℝ) :
    unif6[f | mX] =ᵐ[unif6]
      cell ((f 0 + f 1) / 2) ((f 2 + f 3 + f 4 + f 5) / 4) := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq mX_le Integrable.of_finite
    (fun _ _ _ => Integrable.of_finite.integrableOn) ?_
    (stronglyMeasurable_cell _ _).aestronglyMeasurable).symm
  rintro _ ⟨t, -, rfl⟩ -
  rw [← integral_indicator .of_discrete, ← integral_indicator .of_discrete, integral_unif6,
    integral_unif6]
  by_cases h1 : true ∈ t <;> by_cases h0 : false ∈ t <;>
    simp [Set.indicator, cell, X, h0, h1] <;> ring

/-- The treated units. -/
def T : Set (Fin 6) := {0, 2}

/-- Treated potential outcomes. -/
def Y₁ : Fin 6 → ℝ := ![3, 3, 2, 0, 2, 4]

/-- Control potential outcomes. -/
def Y₀ : Fin 6 → ℝ := ![1, 1, 0, 1, 0, -1]

lemma propensity_true : unif6[T.indicator 1 | mX] =ᵐ[unif6] cell (1 / 2) (1 / 4) :=
  (condExp_eq_cell _).trans (Filter.Eventually.of_forall fun i => by
    simp [T, Set.indicator])

lemma outcome₁_true : unif6[Y₁ | mX] =ᵐ[unif6] cell 3 2 :=
  (condExp_eq_cell _).trans (Filter.Eventually.of_forall fun i => by simp [Y₁]; norm_num)

lemma outcome₀_true : unif6[Y₀ | mX] =ᵐ[unif6] cell 1 0 :=
  (condExp_eq_cell _).trans (Filter.Eventually.of_forall fun i => by simp [Y₀])

lemma hex₁ :
    unif6[T.indicator Y₁ | mX] =ᵐ[unif6] unif6[T.indicator 1 | mX] * unif6[Y₁ | mX] := by
  filter_upwards [condExp_eq_cell (T.indicator Y₁), propensity_true, outcome₁_true]
    with i h h₁ h₂
  rw [h, Pi.mul_apply, h₁, h₂]
  fin_cases i <;> simp [cell, X, T, Y₁, Set.indicator] <;> norm_num

lemma hex₀ :
    unif6[Tᶜ.indicator Y₀ | mX] =ᵐ[unif6] (1 - unif6[T.indicator 1 | mX]) * unif6[Y₀ | mX] := by
  filter_upwards [condExp_eq_cell (Tᶜ.indicator Y₀), propensity_true, outcome₀_true]
    with i h h₁ h₂
  rw [h, Pi.mul_apply, Pi.sub_apply, h₁, h₂]
  fin_cases i <;> simp [cell, X, T, Y₀, Set.indicator] <;> norm_num

lemma hT : MeasurableSet T := .of_discrete

lemma bounded {a c : ℝ} (ha₀ : 1 / 4 ≤ a) (ha₁ : a ≤ 3 / 4) (hc₀ : 1 / 4 ≤ c) (hc₁ : c ≤ 3 / 4) :
    ∀ᵐ i ∂unif6, (1 : ℝ) / 4 ≤ cell a c i ∧ cell a c i ≤ 1 - 1 / 4 :=
  Filter.Eventually.of_forall fun i => by
    cases h : X i <;> simp only [cell, h, Bool.cond_true, Bool.cond_false] <;> constructor <;>
      linarith

/-- **Propensity correct only, non-constant nuisances**: `e = e* = (1/2 | 1/4)` and the wrong
regressions `g₁ = (0 | 5)`, `g₀ = (-1 | 2)`. -/
example :
    ∫ i, aipwScoreOfSigma T (observed T Y₀ Y₁) (cell (1 / 2) (1 / 4)) (cell (-1) 2) (cell 0 5) i
      ∂unif6 = ∫ i, (Y₁ i - Y₀ i) ∂unif6 :=
  integral_aipwScoreOfSigma_of_propensity mX_le hT (Filter.EventuallyEq.refl _ _) .of_finite
    .of_finite hex₁ hex₀ (stronglyMeasurable_cell _ _) (stronglyMeasurable_cell _ _)
    (stronglyMeasurable_cell _ _) .of_finite .of_finite (by norm_num : (0 : ℝ) < 1 / 4)
    (bounded (by norm_num) (by norm_num) (by norm_num) (by norm_num)) propensity_true.symm

/-- **Outcome regressions correct only, non-constant nuisances**: `g₁ = μ₁* = (3 | 2)`,
`g₀ = μ₀* = (1 | 0)` and the wrong propensity `e = (1/4 | 3/4)`. -/
example :
    ∫ i, aipwScoreOfSigma T (observed T Y₀ Y₁) (cell (1 / 4) (3 / 4)) (cell 1 0) (cell 3 2) i
      ∂unif6 = ∫ i, (Y₁ i - Y₀ i) ∂unif6 :=
  integral_aipwScoreOfSigma_of_outcome mX_le hT (Filter.EventuallyEq.refl _ _) .of_finite
    .of_finite hex₁ hex₀ (stronglyMeasurable_cell _ _) (stronglyMeasurable_cell _ _)
    (stronglyMeasurable_cell _ _) .of_finite .of_finite (by norm_num : (0 : ℝ) < 1 / 4)
    (bounded (by norm_num) (by norm_num) (by norm_num) (by norm_num)) outcome₀_true.symm
    outcome₁_true.symm

/-- A direct finite-sum check of the outcome-correct example: both sides equal `2`. -/
example :
    ∫ i, aipwScoreOfSigma T (observed T Y₀ Y₁) (cell (1 / 4) (3 / 4)) (cell 1 0) (cell 3 2) i
      ∂unif6 = 2 ∧ ∫ i, (Y₁ i - Y₀ i) ∂unif6 = 2 := by
  rw [integral_unif6, integral_unif6]
  simp [aipwScoreOfSigma, observed, cell, X, T, Y₀, Y₁, Set.indicator]
  norm_num

end Covariate

end MathlibExtTest.Probability.Causality.AugmentedIPW
