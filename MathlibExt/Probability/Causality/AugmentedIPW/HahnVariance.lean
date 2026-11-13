/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.Score
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Probability.Moments.Variance

/-!
# Hahn's variance formula for the AIPW score and efficiency in the augmented IPW class

A binary treatment is the event `T`, `X : Ω → 𝒳` is the covariate, `Y` the observed outcome and
`Y₀, Y₁` the potential outcomes, as in `AugmentedIPW.Score`. The true nuisances are functions of
the covariate value: the propensity `e(x) = P(T | X = x)`, the outcome regressions
`m_a(x) = E[Y_a | X = x]` and the conditional variances `s_a(x) = Var(Y_a | X = x)` (written
`σ_a²(x)` in most texts). With `τ(x) = m₁(x) - m₀(x)` and `τ = E[Y₁ - Y₀]`, the AIPW score at the
true nuisances is
`ψ = τ(X) + 1_T (Y - m₁(X)) / e(X) - 1_{Tᶜ} (Y - m₀(X)) / (1 - e(X))`
and `φ = ψ - τ` is the efficient influence function of the average treatment effect.

## Main definitions

* `HahnSetup μ T X Y Y₀ Y₁ e m₀ m₁ s₀ s₁`: the assumptions, in conditional-expectation form
  given `σ(X)`: consistency, square-integrable potential outcomes, `e, m₀, m₁` the true
  propensity and outcome regressions, `s₀, s₁` the conditional variances of the potential
  outcomes, mean and second-moment exchangeability, and strong overlap `ε ≤ e ≤ 1 - ε`.
* `hahnBound μ X e m₀ m₁ s₀ s₁ τ`: Hahn's expression
  `E[s₁(X) / e(X) + s₀(X) / (1 - e(X)) + (τ(X) - τ)²]`.
* `augmentedIPWScore T X Y e h`: the Robins-Rotnitzky-Zhao augmented IPW score
  `1_T Y / e(X) - 1_{Tᶜ} Y / (1 - e(X)) - (1_T - e(X)) h(X)` for an augmentation function `h`.
* `efficientAugmentation e m₀ m₁ = m₁ / e + m₀ / (1 - e)`: the augmentation of the AIPW score.

## Main results

* `HahnSetup.integral_aipwScore`: `E[ψ] = E[Y₁ - Y₀]`.
* `HahnSetup.integral_sq_aipwScore_sub`: for every real `c`,
  `E[(ψ - c)²] = E[s₁(X) / e(X) + s₀(X) / (1 - e(X)) + (τ(X) - c)²]`.
* `HahnSetup.variance_aipwScore`: **Hahn's formula**, `Var(φ) = Var(ψ) = hahnBound … τ` with
  `τ = E[Y₁ - Y₀]` (Hahn 1998, Theorem 1).
* `HahnSetup.aipwScore_eq_augmentedIPWScore`: the AIPW score is the augmented IPW score with
  augmentation `efficientAugmentation e m₀ m₁`.
* `HahnSetup.integral_augmentedIPWScore`: every augmented IPW score with a square-integrable
  augmentation `h(X)` has mean `E[Y₁ - Y₀]`.
* `HahnSetup.variance_augmentedIPWScore`: `Var(ψ_h) = Var(ψ) + E[e(X)(1 - e(X))(h*(X) - h(X))²]`
  with `h* = efficientAugmentation e m₀ m₁`.
* `HahnSetup.hahnBound_le_variance_augmentedIPWScore`: Hahn's bound is the minimum variance in
  the augmented IPW class, attained by the AIPW score (Robins, Rotnitzky and Zhao 1994).

## Scope: what "efficiency bound" means here

The efficiency statement proved here is variance minimality within the class of augmented IPW
scores `ψ_h`, all of which are unbiased for the average treatment effect at the true propensity.
That every influence function of a regular asymptotically linear estimator in the
nonparametric model has the form `φ + (element orthogonal to the tangent space)`, and hence that
`Var(φ)` lower-bounds the asymptotic variance of every regular estimator (Hahn 1998, Theorem 1,
via pathwise differentiability and the convolution theorem), is not formalized: no tangent-space
or local asymptotic normality framework is available in the library.

## Hypotheses taken from sibling results

The AIPW variance decomposition of T143 (`AugmentedIPW/Variance.lean`, open PR #1863),
`Var(ψ) = E[(ψ - τ)²]` with `E[ψ] = τ`, is not imported. It is not needed as a hypothesis
either: `HahnSetup.integral_aipwScore` proves the mean identity and Mathlib's
`ProbabilityTheory.variance_eq_integral` gives the second-moment form, so `variance_aipwScore`
states Hahn's formula for `Var[ψ; μ]`, the variance that T143's limit theorems use, with no
extra assumption.

## Source receipt (API-00)

* Source: J. Hahn (1998), Theorem 1 (the efficiency bound
  `E[σ₁²(X) / p(X) + σ₀²(X) / (1 - p(X)) + (β(X) - β)²]` for the average treatment effect
  without knowledge of the propensity score) and A. A. Tsiatis, *Semiparametric Theory and
  Missing Data* (2006), Chapter 13 (the augmented IPW class for the average treatment effect and
  its optimal augmentation `m₁ / e + m₀ / (1 - e)`).
* Reused: `aipwScore`, `aipwScore_eq`, `aipwScore_eq_ipw_sub`, `condExp_outcomeResidual_treated`,
  `condExp_outcomeResidual_control` and `condExp_propensityResidual_mul` from
  `AugmentedIPW.Score`; `observed` from `CausalIdentification`; Mathlib's
  `condExp_mul_of_stronglyMeasurable_left`, `integral_condExp`, `MemLp.condExp`,
  `variance_eq_integral`.
* Proved here: the second-moment computation of the score and of the augmented IPW class.

## References

* J. Hahn, *On the role of the propensity score in efficient semiparametric estimation of
  average treatment effects*, Econometrica 66(2) (1998), 315–331.
* J. M. Robins, A. Rotnitzky and L. P. Zhao, *Estimation of regression coefficients when some
  regressors are not always observed*, JASA 89(427) (1994), 846–866.
* A. A. Tsiatis, *Semiparametric Theory and Missing Data*, Springer (2006).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

namespace MathlibExt.Probability.Causality.AugmentedIPW.HahnVariance

open MathlibExt.Probability.Causality

section Definitions

variable {Ω 𝒳 : Type*}

/-- **Hahn's variance bound** for the average treatment effect at centering `τ`:
`E[s₁(X) / e(X) + s₀(X) / (1 - e(X)) + (m₁(X) - m₀(X) - τ)²]`, where `s_a` is the conditional
variance of `Y_a` given `X`. -/
noncomputable def hahnBound [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → 𝒳)
    (e m₀ m₁ s₀ s₁ : 𝒳 → ℝ) (τ : ℝ) : ℝ :=
  ∫ ω, (s₁ (X ω) / e (X ω) + s₀ (X ω) / (1 - e (X ω)) + (m₁ (X ω) - m₀ (X ω) - τ) ^ 2) ∂μ

/-- The **augmented IPW score** with augmentation function `h`:
`1_T Y / e(X) - 1_{Tᶜ} Y / (1 - e(X)) - (1_T - e(X)) h(X)`. With `h = 0` it is the IPW
contrast; with `h = efficientAugmentation e m₀ m₁` it is the AIPW score. -/
noncomputable def augmentedIPWScore (T : Set Ω) (X : Ω → 𝒳) (Y : Ω → ℝ) (e h : 𝒳 → ℝ) :
    Ω → ℝ := fun ω =>
  T.indicator (fun ω => Y ω / e (X ω)) ω - Tᶜ.indicator (fun ω => Y ω / (1 - e (X ω))) ω -
    (T.indicator 1 ω - e (X ω)) * h (X ω)

/-- The augmentation of the AIPW score, `m₁ / e + m₀ / (1 - e)`. -/
noncomputable def efficientAugmentation (e m₀ m₁ : 𝒳 → ℝ) : 𝒳 → ℝ :=
  fun x => m₁ x / e x + m₀ x / (1 - e x)

end Definitions

section Setup

variable {Ω 𝒳 : Type*} {mΩ : MeasurableSpace Ω} [m𝒳 : MeasurableSpace 𝒳]

/-- The assumptions of Hahn's variance formula. With `σ(X) = MeasurableSpace.comap X m𝒳`:
* `T` and `X` are measurable, and the observed outcome is `Y = observed T Y₀ Y₁` (consistency);
* the potential outcomes are square integrable;
* `e` is the true propensity, `E[1_T | X] = e(X)`, and satisfies strong overlap
  `ε ≤ e ≤ 1 - ε` everywhere on `𝒳` for some `ε > 0`;
* `m_a` is the true outcome regression, `E[Y_a | X] = m_a(X)`;
* `s_a` is the conditional variance, `E[(Y_a - m_a(X))² | X] = s_a(X)`;
* mean exchangeability `E[1_T Y₁ | X] = E[1_T | X] E[Y₁ | X]` (and the control analogue) and
  second-moment exchangeability `E[1_T (Y₁ - m₁(X))² | X] = E[1_T | X] E[(Y₁ - m₁(X))² | X]`
  (and the control analogue); both follow from `Y_a ⊥ T | X`. -/
structure HahnSetup (μ : Measure Ω) (T : Set Ω) (X : Ω → 𝒳) (Y Y₀ Y₁ : Ω → ℝ)
    (e m₀ m₁ s₀ s₁ : 𝒳 → ℝ) : Prop where
  measurableSet_T : MeasurableSet T
  measurable_X : Measurable X
  consistency : ∀ ω, Y ω = observed T Y₀ Y₁ ω
  memLp_Y₀ : MemLp Y₀ 2 μ
  memLp_Y₁ : MemLp Y₁ 2 μ
  measurable_e : Measurable e
  measurable_m₀ : Measurable m₀
  measurable_m₁ : Measurable m₁
  overlap : ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε ≤ e x ∧ e x ≤ 1 - ε
  propensity : μ[T.indicator (1 : Ω → ℝ) | m𝒳.comap X] =ᵐ[μ] fun ω => e (X ω)
  regression₀ : μ[Y₀ | m𝒳.comap X] =ᵐ[μ] fun ω => m₀ (X ω)
  regression₁ : μ[Y₁ | m𝒳.comap X] =ᵐ[μ] fun ω => m₁ (X ω)
  condVar₀ : μ[fun ω => (Y₀ ω - m₀ (X ω)) ^ 2 | m𝒳.comap X] =ᵐ[μ] fun ω => s₀ (X ω)
  condVar₁ : μ[fun ω => (Y₁ ω - m₁ (X ω)) ^ 2 | m𝒳.comap X] =ᵐ[μ] fun ω => s₁ (X ω)
  meanExch₀ : μ[Tᶜ.indicator Y₀ | m𝒳.comap X] =ᵐ[μ]
    μ[Tᶜ.indicator (1 : Ω → ℝ) | m𝒳.comap X] * μ[Y₀ | m𝒳.comap X]
  meanExch₁ : μ[T.indicator Y₁ | m𝒳.comap X] =ᵐ[μ]
    μ[T.indicator (1 : Ω → ℝ) | m𝒳.comap X] * μ[Y₁ | m𝒳.comap X]
  varExch₀ : μ[Tᶜ.indicator (fun ω => (Y₀ ω - m₀ (X ω)) ^ 2) | m𝒳.comap X] =ᵐ[μ]
    μ[Tᶜ.indicator (1 : Ω → ℝ) | m𝒳.comap X] * μ[fun ω => (Y₀ ω - m₀ (X ω)) ^ 2 | m𝒳.comap X]
  varExch₁ : μ[T.indicator (fun ω => (Y₁ ω - m₁ (X ω)) ^ 2) | m𝒳.comap X] =ᵐ[μ]
    μ[T.indicator (1 : Ω → ℝ) | m𝒳.comap X] * μ[fun ω => (Y₁ ω - m₁ (X ω)) ^ 2 | m𝒳.comap X]

end Setup

section Helpers

variable {Ω 𝒳 : Type*} {mΩ : MeasurableSpace Ω} [m𝒳 : MeasurableSpace 𝒳] {μ : Measure Ω}
  [IsFiniteMeasure μ] {X : Ω → 𝒳}

/-- Tower property with a function of `X` pulled out: if `E[g | X] = k(X)`, then
`E[f(X) g] = E[f(X) k(X)]`. -/
theorem integral_comp_mul_eq_of_condExp (hX : Measurable X) {f k : 𝒳 → ℝ} (hf : Measurable f)
    {g : Ω → ℝ} (hg : Integrable g μ) (hfg : Integrable (fun ω => f (X ω) * g ω) μ)
    (hk : μ[g | m𝒳.comap X] =ᵐ[μ] fun ω => k (X ω)) :
    ∫ ω, f (X ω) * g ω ∂μ = ∫ ω, f (X ω) * k (X ω) ∂μ := by
  have hm : m𝒳.comap X ≤ mΩ := hX.comap_le
  have hfX : StronglyMeasurable[m𝒳.comap X] fun ω => f (X ω) :=
    (hf.comp (comap_measurable X)).stronglyMeasurable
  calc ∫ ω, f (X ω) * g ω ∂μ = ∫ ω, μ[fun ω => f (X ω) * g ω | m𝒳.comap X] ω ∂μ :=
        (integral_condExp hm).symm
    _ = _ := by
      refine integral_congr_ae ?_
      filter_upwards [condExp_mul_of_stronglyMeasurable_left hfX hfg hg, hk] with ω h₁ h₂
      refine h₁.trans ?_
      rw [Pi.mul_apply, h₂]

/-- Special case of `integral_comp_mul_eq_of_condExp` with `E[g | X] = 0`. -/
theorem integral_comp_mul_eq_zero_of_condExp (hX : Measurable X) {f : 𝒳 → ℝ} (hf : Measurable f)
    {g : Ω → ℝ} (hg : Integrable g μ) (hfg : Integrable (fun ω => f (X ω) * g ω) μ)
    (hk : μ[g | m𝒳.comap X] =ᵐ[μ] 0) : ∫ ω, f (X ω) * g ω ∂μ = 0 := by
  rw [integral_comp_mul_eq_of_condExp (k := fun _ => 0) hX hf hg hfg hk]
  simp

/-- The conditional probability of the complement of `T`. -/
theorem condExp_indicator_compl {T : Set Ω} (hT : MeasurableSet T) (hX : Measurable X)
    {e : 𝒳 → ℝ} (hprop : μ[T.indicator (1 : Ω → ℝ) | m𝒳.comap X] =ᵐ[μ] fun ω => e (X ω)) :
    μ[Tᶜ.indicator (1 : Ω → ℝ) | m𝒳.comap X] =ᵐ[μ] fun ω => 1 - e (X ω) := by
  have hm : m𝒳.comap X ≤ mΩ := hX.comap_le
  rw [Set.indicator_compl]
  have h1 : Integrable (T.indicator (1 : Ω → ℝ)) μ := (integrable_const 1).indicator hT
  filter_upwards [condExp_sub (integrable_const (1 : ℝ)) h1 (m𝒳.comap X), hprop] with ω h₁ h₂
  have hc : μ[fun _ => (1 : ℝ) | m𝒳.comap X] = fun _ => 1 := condExp_const hm (1 : ℝ)
  refine h₁.trans ?_
  rw [Pi.sub_apply, h₂, hc]

omit [IsFiniteMeasure μ] in
/-- A bounded function of `X` times an `L²` function is in `L²`. -/
theorem memLp_comp_mul (hX : Measurable X) {f : 𝒳 → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) {g : Ω → ℝ} (hg : MemLp g 2 μ) :
    MemLp (fun ω => f (X ω) * g ω) 2 μ :=
  MemLp.mul (p := ⊤) (q := 2) (r := 2) (memLp_top_of_bound (hf.comp hX).aestronglyMeasurable C
    (Eventually.of_forall fun _ => hC _)) hg

end Helpers

section Arm

variable {Ω 𝒳 : Type*} {mΩ : MeasurableSpace Ω} [m𝒳 : MeasurableSpace 𝒳] {μ : Measure Ω}
  [IsFiniteMeasure μ] {X : Ω → 𝒳}

/-- One arm of the score: for an event `S` with conditional probability `p(X) ≥ ε > 0` and an
`L²` residual `R` with `E[1_S R² | X] = p(X) s(X)`, the weighted residual `1_S R / p(X)` is in
`L²` and its second moment is `E[s(X) / p(X)]`. -/
theorem arm_memLp_integral_sq {S : Set Ω} (hS : MeasurableSet S) (hX : Measurable X)
    {p s : 𝒳 → ℝ} (hp : Measurable p) {ε : ℝ} (hε : 0 < ε) (hpε : ∀ x, ε ≤ p x)
    {R : Ω → ℝ} (hR : MemLp R 2 μ)
    (hs : μ[S.indicator (fun ω => R ω ^ 2) | m𝒳.comap X] =ᵐ[μ] fun ω => p (X ω) * s (X ω)) :
    MemLp (S.indicator fun ω => R ω / p (X ω)) 2 μ ∧
      Integrable (fun ω => s (X ω) / p (X ω)) μ ∧
      ∫ ω, (S.indicator (fun ω => R ω / p (X ω)) ω) ^ 2 ∂μ = ∫ ω, s (X ω) / p (X ω) ∂μ := by
  have hp0 : ∀ x, 0 < p x := fun x => hε.trans_le (hpε x)
  have hinv : ∀ x, ‖(p x)⁻¹‖ ≤ ε⁻¹ := fun x => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hp0 x)]
    exact inv_anti₀ hε (hpε x)
  have hinv2 : ∀ x, ‖((p x) ^ 2)⁻¹‖ ≤ (ε ^ 2)⁻¹ := fun x => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (pow_pos (hp0 x) 2)]
    exact inv_anti₀ (pow_pos hε 2) (pow_le_pow_left₀ hε.le (hpε x) 2)
  have hpt : (S.indicator fun ω => R ω / p (X ω)) = fun ω => (p (X ω))⁻¹ * S.indicator R ω := by
    funext ω; by_cases h : ω ∈ S <;> simp [h, div_eq_inv_mul]
  have hmem : MemLp (S.indicator fun ω => R ω / p (X ω)) 2 μ := by
    rw [hpt]; exact memLp_comp_mul hX hp.inv hinv (hR.indicator hS.nullMeasurableSet)
  have hg : Integrable (S.indicator fun ω => R ω ^ 2) μ := hR.integrable_sq.indicator hS
  have hfg : Integrable (fun ω => ((p (X ω)) ^ 2)⁻¹ * S.indicator (fun ω => R ω ^ 2) ω) μ :=
    hg.bdd_mul ((hp.pow_const 2).inv.comp hX).aestronglyMeasurable
      (Eventually.of_forall fun _ => hinv2 _)
  have hsX : Integrable (fun ω => p (X ω) * s (X ω)) μ := integrable_condExp.congr hs
  have hsp : (fun ω => s (X ω) / p (X ω)) = fun ω => (p (X ω) ^ 2)⁻¹ * (p (X ω) * s (X ω)) := by
    funext ω; have := (hp0 (X ω)).ne'; field_simp
  refine ⟨hmem, ?_, ?_⟩
  · rw [hsp]
    exact hsX.bdd_mul ((hp.pow_const 2).inv.comp hX).aestronglyMeasurable
      (Eventually.of_forall fun _ => hinv2 _)
  · have hsq : (fun ω => (S.indicator (fun ω => R ω / p (X ω)) ω) ^ 2) =
        fun ω => ((p (X ω)) ^ 2)⁻¹ * S.indicator (fun ω => R ω ^ 2) ω := by
      funext ω; by_cases h : ω ∈ S <;> simp [h, div_eq_inv_mul, mul_pow, inv_pow]
    rw [hsq, integral_comp_mul_eq_of_condExp (f := fun x => (p x ^ 2)⁻¹) (k := fun x => p x * s x)
      hX (hp.pow_const 2).inv hg hfg hs, hsp]

end Arm

section Main

variable {Ω 𝒳 : Type*} {mΩ : MeasurableSpace Ω} [m𝒳 : MeasurableSpace 𝒳] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {T : Set Ω} {X : Ω → 𝒳} {Y Y₀ Y₁ : Ω → ℝ} {e m₀ m₁ s₀ s₁ : 𝒳 → ℝ}

namespace HahnSetup

variable (hH : HahnSetup μ T X Y Y₀ Y₁ e m₀ m₁ s₀ s₁)
include hH

omit [IsProbabilityMeasure μ] in
/-- The true outcome regression `m₀(X)` is square integrable. -/
theorem memLp_m₀ : MemLp (fun ω => m₀ (X ω)) 2 μ :=
  (MemLp.condExp (m := m𝒳.comap X) one_le_two hH.memLp_Y₀).ae_eq hH.regression₀

omit [IsProbabilityMeasure μ] in
/-- The true outcome regression `m₁(X)` is square integrable. -/
theorem memLp_m₁ : MemLp (fun ω => m₁ (X ω)) 2 μ :=
  (MemLp.condExp (m := m𝒳.comap X) one_le_two hH.memLp_Y₁).ae_eq hH.regression₁

/-- The treated weighted residual: in `L²`, conditional mean zero given `X`, and second moment
`E[s₁(X) / e(X)]`. -/
theorem treated_residual :
    MemLp (T.indicator fun ω => (Y ω - m₁ (X ω)) / e (X ω)) 2 μ ∧
      Integrable (fun ω => s₁ (X ω) / e (X ω)) μ ∧
      ∫ ω, (T.indicator (fun ω => (Y ω - m₁ (X ω)) / e (X ω)) ω) ^ 2 ∂μ =
        ∫ ω, s₁ (X ω) / e (X ω) ∂μ ∧
      μ[T.indicator (fun ω => (Y ω - m₁ (X ω)) / e (X ω)) | m𝒳.comap X] =ᵐ[μ] 0 := by
  obtain ⟨ε, hε, heε⟩ := hH.overlap
  have hY : (T.indicator fun ω => (Y ω - m₁ (X ω)) / e (X ω)) =
      T.indicator fun ω => (Y₁ ω - m₁ (X ω)) / e (X ω) := by
    funext ω; by_cases h : ω ∈ T <;> simp [h, hH.consistency, observed]
  have hs : μ[T.indicator (fun ω => (Y₁ ω - m₁ (X ω)) ^ 2) | m𝒳.comap X] =ᵐ[μ]
      fun ω => e (X ω) * s₁ (X ω) := by
    filter_upwards [hH.varExch₁, hH.propensity, hH.condVar₁] with ω h₁ h₂ h₃
    rw [h₁, Pi.mul_apply, h₂, h₃]
  obtain ⟨h₁, h₂, h₃⟩ := arm_memLp_integral_sq (R := fun ω => Y₁ ω - m₁ (X ω)) hH.measurableSet_T
    hH.measurable_X hH.measurable_e hε (fun x => (heε x).1) (hH.memLp_Y₁.sub hH.memLp_m₁) hs
  refine ⟨hY ▸ h₁, h₂, hY ▸ h₃, ?_⟩
  exact condExp_outcomeResidual_treated hH.measurableSet_T hH.measurable_X hH.consistency
    (hH.memLp_Y₁.integrable one_le_two) hH.meanExch₁ hH.measurable_e hH.measurable_m₁ hε
    (fun x => (heε x).1) hH.regression₁

/-- The control weighted residual: in `L²`, conditional mean zero given `X`, and second moment
`E[s₀(X) / (1 - e(X))]`. -/
theorem control_residual :
    MemLp (Tᶜ.indicator fun ω => (Y ω - m₀ (X ω)) / (1 - e (X ω))) 2 μ ∧
      Integrable (fun ω => s₀ (X ω) / (1 - e (X ω))) μ ∧
      ∫ ω, (Tᶜ.indicator (fun ω => (Y ω - m₀ (X ω)) / (1 - e (X ω))) ω) ^ 2 ∂μ =
        ∫ ω, s₀ (X ω) / (1 - e (X ω)) ∂μ ∧
      μ[Tᶜ.indicator (fun ω => (Y ω - m₀ (X ω)) / (1 - e (X ω))) | m𝒳.comap X] =ᵐ[μ] 0 := by
  obtain ⟨ε, hε, heε⟩ := hH.overlap
  have hY : (Tᶜ.indicator fun ω => (Y ω - m₀ (X ω)) / (1 - e (X ω))) =
      Tᶜ.indicator fun ω => (Y₀ ω - m₀ (X ω)) / (1 - e (X ω)) := by
    funext ω; by_cases h : ω ∈ T <;> simp [h, hH.consistency, observed]
  have hs : μ[Tᶜ.indicator (fun ω => (Y₀ ω - m₀ (X ω)) ^ 2) | m𝒳.comap X] =ᵐ[μ]
      fun ω => (1 - e (X ω)) * s₀ (X ω) := by
    filter_upwards [hH.varExch₀, condExp_indicator_compl hH.measurableSet_T hH.measurable_X
      hH.propensity, hH.condVar₀] with ω h₁ h₂ h₃
    rw [h₁, Pi.mul_apply, h₂, h₃]
  obtain ⟨h₁, h₂, h₃⟩ := arm_memLp_integral_sq (R := fun ω => Y₀ ω - m₀ (X ω))
    (p := fun x => 1 - e x)
    hH.measurableSet_T.compl hH.measurable_X (measurable_const.sub hH.measurable_e) hε
    (fun x => by linarith [(heε x).2]) (hH.memLp_Y₀.sub hH.memLp_m₀) hs
  refine ⟨hY ▸ h₁, h₂, hY ▸ h₃, ?_⟩
  exact condExp_outcomeResidual_control hH.measurableSet_T hH.measurable_X hH.consistency
    (hH.memLp_Y₀.integrable one_le_two) hH.meanExch₀ hH.measurable_e hH.measurable_m₀ hε
    (fun x => (heε x).2) hH.regression₀

/-- The AIPW score at the true nuisances is square integrable. -/
theorem memLp_aipwScore : MemLp (aipwScore T X Y e m₀ m₁) 2 μ := by
  have h := ((hH.memLp_m₁.sub hH.memLp_m₀).add hH.treated_residual.1).sub hH.control_residual.1
  refine h.ae_eq (Eventually.of_forall fun ω => ?_)
  simp only [Pi.sub_apply, Pi.add_apply, aipwScore_eq]

/-- **Mean of the AIPW score**: `E[ψ] = E[Y₁ - Y₀]`. -/
theorem integral_aipwScore : ∫ ω, aipwScore T X Y e m₀ m₁ ω ∂μ = ∫ ω, (Y₁ ω - Y₀ ω) ∂μ := by
  have hm : m𝒳.comap X ≤ mΩ := hH.measurable_X.comap_le
  obtain ⟨hB, -, -, hBc⟩ := hH.treated_residual
  obtain ⟨hC, -, -, hCc⟩ := hH.control_residual
  have i₁ := hH.memLp_m₁.integrable one_le_two
  have i₀ := hH.memLp_m₀.integrable one_le_two
  have iB := hB.integrable one_le_two
  have iC := hC.integrable one_le_two
  have hzero : ∀ {g : Ω → ℝ}, μ[g | m𝒳.comap X] =ᵐ[μ] 0 → ∫ ω, g ω ∂μ = 0 := fun hg =>
    (integral_condExp hm).symm.trans ((integral_congr_ae hg).trans (by simp))
  have hreg : ∀ {g : Ω → ℝ} {k : 𝒳 → ℝ}, μ[g | m𝒳.comap X] =ᵐ[μ] (fun ω => k (X ω)) →
      ∫ ω, k (X ω) ∂μ = ∫ ω, g ω ∂μ := fun hg =>
    (integral_congr_ae hg.symm).trans (integral_condExp hm)
  simp_rw [aipwScore_eq]
  rw [integral_sub, integral_add, integral_sub, hzero hBc, hzero hCc, hreg hH.regression₁,
    hreg hH.regression₀, integral_sub (hH.memLp_Y₁.integrable one_le_two)
      (hH.memLp_Y₀.integrable one_le_two)]
  · ring
  · exact i₁
  · exact i₀
  · exact i₁.sub i₀
  · exact iB
  · exact (i₁.sub i₀).add iB
  · exact iC

/-- **Second moment of the AIPW score about any center** `c`:
`E[(ψ - c)²] = E[s₁(X) / e(X) + s₀(X) / (1 - e(X)) + (τ(X) - c)²]`. -/
theorem integral_sq_aipwScore_sub (c : ℝ) :
    ∫ ω, (aipwScore T X Y e m₀ m₁ ω - c) ^ 2 ∂μ = hahnBound μ X e m₀ m₁ s₀ s₁ c := by
  obtain ⟨hB, hsB, hB2, hBc⟩ := hH.treated_residual
  obtain ⟨hC, hsC, hC2, hCc⟩ := hH.control_residual
  set B := T.indicator fun ω => (Y ω - m₁ (X ω)) / e (X ω) with hBdef
  set C := Tᶜ.indicator fun ω => (Y ω - m₀ (X ω)) / (1 - e (X ω)) with hCdef
  set a : 𝒳 → ℝ := fun x => m₁ x - m₀ x - c with hadef
  have ha : Measurable a := (hH.measurable_m₁.sub hH.measurable_m₀).sub measurable_const
  have haL : MemLp (fun ω => a (X ω)) 2 μ := (hH.memLp_m₁.sub hH.memLp_m₀).sub (memLp_const c)
  have hBC : ∀ ω, B ω * C ω = 0 := fun ω => by
    by_cases h : ω ∈ T <;> simp [hBdef, hCdef, h]
  have hpt : ∀ ω, (aipwScore T X Y e m₀ m₁ ω - c) ^ 2 =
      a (X ω) ^ 2 + B ω ^ 2 + C ω ^ 2 + 2 * (a (X ω) * B ω) - 2 * (a (X ω) * C ω) := fun ω => by
    have h := hBC ω
    rw [aipwScore_eq]
    simp only [hadef, hBdef, hCdef] at h ⊢
    linear_combination (-2 : ℝ) * h
  have ia2 : Integrable (fun ω => a (X ω) ^ 2) μ := haL.integrable_sq
  have iB2 : Integrable (fun ω => B ω ^ 2) μ := hB.integrable_sq
  have iC2 : Integrable (fun ω => C ω ^ 2) μ := hC.integrable_sq
  have iaB : Integrable (fun ω => a (X ω) * B ω) μ := haL.integrable_mul hB
  have iaC : Integrable (fun ω => a (X ω) * C ω) μ := haL.integrable_mul hC
  have haB : ∫ ω, a (X ω) * B ω ∂μ = 0 :=
    integral_comp_mul_eq_zero_of_condExp hH.measurable_X ha (hB.integrable one_le_two) iaB hBc
  have haC : ∫ ω, a (X ω) * C ω ∂μ = 0 :=
    integral_comp_mul_eq_zero_of_condExp hH.measurable_X ha (hC.integrable one_le_two) iaC hCc
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub, integral_add, integral_add,
    integral_add, integral_const_mul, integral_const_mul, haB, haC, hB2, hC2, hahnBound,
    integral_add, integral_add]
  · ring
  all_goals first
    | exact hsB | exact hsC | exact hsB.add hsC | exact ia2 | exact iB2 | exact iC2
    | exact ia2.add iB2 | exact (ia2.add iB2).add iC2 | exact iaB.const_mul 2
    | exact iaC.const_mul 2 | exact ((ia2.add iB2).add iC2).add (iaB.const_mul 2)

/-- **Hahn's variance formula.** The variance of the AIPW score at the true nuisances, which is
the variance of the efficient influence function `φ = ψ - τ`, is
`E[s₁(X) / e(X) + s₀(X) / (1 - e(X)) + (τ(X) - τ)²]` with `τ = E[Y₁ - Y₀]`. -/
theorem variance_aipwScore :
    Var[aipwScore T X Y e m₀ m₁; μ] = hahnBound μ X e m₀ m₁ s₀ s₁ (∫ ω, (Y₁ ω - Y₀ ω) ∂μ) := by
  rw [variance_eq_integral hH.memLp_aipwScore.aestronglyMeasurable.aemeasurable,
    hH.integral_aipwScore, hH.integral_sq_aipwScore_sub]

omit [IsProbabilityMeasure μ] in
/-- The AIPW score is the augmented IPW score with augmentation `m₁ / e + m₀ / (1 - e)`. -/
theorem aipwScore_eq_augmentedIPWScore :
    aipwScore T X Y e m₀ m₁ = augmentedIPWScore T X Y e (efficientAugmentation e m₀ m₁) := by
  obtain ⟨ε, hε, heε⟩ := hH.overlap
  funext ω
  have he₀ : e (X ω) ≠ 0 := (hε.trans_le (heε (X ω)).1).ne'
  have he₁ : e (X ω) ≠ 1 := by linarith [(heε (X ω)).2]
  rw [aipwScore_eq_ipw_sub he₀ he₁]
  rfl

omit [IsProbabilityMeasure μ] in
/-- An augmented IPW score differs from the AIPW score by the propensity residual
`1_T - e(X)` times `h*(X) - h(X)`, where `h* = efficientAugmentation e m₀ m₁`. -/
theorem augmentedIPWScore_eq_add (h : 𝒳 → ℝ) (ω : Ω) :
    augmentedIPWScore T X Y e h ω = aipwScore T X Y e m₀ m₁ ω +
      (T.indicator 1 ω - e (X ω)) * (efficientAugmentation e m₀ m₁ (X ω) - h (X ω)) := by
  rw [hH.aipwScore_eq_augmentedIPWScore]
  simp only [augmentedIPWScore]
  ring

omit [IsProbabilityMeasure μ] in
/-- The efficient augmentation evaluated at `X` is square integrable. -/
theorem memLp_efficientAugmentation :
    MemLp (fun ω => efficientAugmentation e m₀ m₁ (X ω)) 2 μ := by
  obtain ⟨ε, hε, heε⟩ := hH.overlap
  have hb₁ : ∀ x, ‖(e x)⁻¹‖ ≤ ε⁻¹ := fun x => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hε.trans_le (heε x).1)]
    exact inv_anti₀ hε (heε x).1
  have hb₀ : ∀ x, ‖(1 - e x)⁻¹‖ ≤ ε⁻¹ := fun x => by
    have : ε ≤ 1 - e x := by linarith [(heε x).2]
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hε.trans_le this)]
    exact inv_anti₀ hε this
  have h := (memLp_comp_mul hH.measurable_X hH.measurable_e.inv hb₁ hH.memLp_m₁).add
    (memLp_comp_mul hH.measurable_X (measurable_const.sub hH.measurable_e).inv hb₀ hH.memLp_m₀)
  refine h.ae_eq (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, Pi.inv_apply, Pi.sub_apply, efficientAugmentation, div_eq_inv_mul]

/-- The second-moment identity for the augmented IPW class: for a square-integrable
augmentation `h(X)` and every center `c`,
`E[(ψ_h - c)²] = E[(ψ - c)²] + E[e(X)(1 - e(X))(h*(X) - h(X))²]`, and `E[ψ_h] = E[ψ]`. -/
theorem integral_augmentedIPWScore_aux {h : 𝒳 → ℝ} (hh : Measurable h)
    (hhL : MemLp (fun ω => h (X ω)) 2 μ) (c : ℝ) :
    ∫ ω, augmentedIPWScore T X Y e h ω ∂μ = ∫ ω, aipwScore T X Y e m₀ m₁ ω ∂μ ∧
    ∫ ω, (augmentedIPWScore T X Y e h ω - c) ^ 2 ∂μ =
      ∫ ω, (aipwScore T X Y e m₀ m₁ ω - c) ^ 2 ∂μ +
        ∫ ω, e (X ω) * (1 - e (X ω)) * (efficientAugmentation e m₀ m₁ (X ω) - h (X ω)) ^ 2 ∂μ ∧
    MemLp (augmentedIPWScore T X Y e h) 2 μ := by
  obtain ⟨ε, hε, heε⟩ := hH.overlap
  obtain ⟨hB, -, -, hBc⟩ := hH.treated_residual
  obtain ⟨hC, -, -, hCc⟩ := hH.control_residual
  have hX := hH.measurable_X
  have hT := hH.measurableSet_T
  have he := hH.measurable_e
  set B := T.indicator fun ω => (Y ω - m₁ (X ω)) / e (X ω) with hBdef
  set C := Tᶜ.indicator fun ω => (Y ω - m₀ (X ω)) / (1 - e (X ω)) with hCdef
  set a : 𝒳 → ℝ := fun x => m₁ x - m₀ x - c with hadef
  set g : 𝒳 → ℝ := fun x => efficientAugmentation e m₀ m₁ x - h x with hgdef
  set D : Ω → ℝ := fun ω => T.indicator 1 ω - e (X ω) with hDdef
  have ha : Measurable a := (hH.measurable_m₁.sub hH.measurable_m₀).sub measurable_const
  have haL : MemLp (fun ω => a (X ω)) 2 μ := (hH.memLp_m₁.sub hH.memLp_m₀).sub (memLp_const c)
  have hg : Measurable g :=
    ((hH.measurable_m₁.div he).add (hH.measurable_m₀.div (measurable_const.sub he))).sub hh
  have hgL : MemLp (fun ω => g (X ω)) 2 μ := hH.memLp_efficientAugmentation.sub hhL
  have he01 : ∀ x, 0 ≤ e x ∧ e x ≤ 1 := fun x =>
    ⟨hε.le.trans (heε x).1, by linarith [(heε x).2]⟩
  have hDm : Measurable D := (measurable_const.indicator hT).sub (he.comp hX)
  have hDb : ∀ ω, ‖D ω‖ ≤ 1 := fun ω => by
    rw [Real.norm_eq_abs, abs_le]
    by_cases hω : ω ∈ T <;> simp [hDdef, hω] <;> constructor <;> linarith [he01 (X ω)]
  have hDc : μ[D | m𝒳.comap X] =ᵐ[μ] 0 := by
    have h1 := condExp_propensityResidual_mul (h := fun _ => (1 : ℝ)) hT hX he measurable_const
      (C := 1) (fun _ => by simp) hH.propensity
    simpa [hDdef] using h1
  have iD : Integrable D μ := (integrable_const (1 : ℝ)).bdd_mul hDm.aestronglyMeasurable
    (Eventually.of_forall hDb) |>.congr (Eventually.of_forall fun ω => by simp)
  -- the score difference
  have hdiff : ∀ ω, augmentedIPWScore T X Y e h ω = aipwScore T X Y e m₀ m₁ ω + D ω * g (X ω) :=
    hH.augmentedIPWScore_eq_add h
  have hψ := hH.memLp_aipwScore
  have hDgL : MemLp (fun ω => D ω * g (X ω)) 2 μ := by
    have := MemLp.mul (p := ⊤) (q := 2) (r := 2)
      (memLp_top_of_bound hDm.aestronglyMeasurable 1 (Eventually.of_forall hDb)) hgL
    exact this
  have hψh : MemLp (augmentedIPWScore T X Y e h) 2 μ :=
    (hψ.add hDgL).ae_eq (Eventually.of_forall fun ω => (hdiff ω).symm)
  -- the mean
  have iDg : Integrable (fun ω => g (X ω) * D ω) μ :=
    (hDgL.integrable one_le_two).congr (Eventually.of_forall fun ω => mul_comm _ _)
  have hmeanDg : ∫ ω, g (X ω) * D ω ∂μ = 0 :=
    integral_comp_mul_eq_zero_of_condExp hX hg iD iDg hDc
  have hmean : ∫ ω, augmentedIPWScore T X Y e h ω ∂μ = ∫ ω, aipwScore T X Y e m₀ m₁ ω ∂μ := by
    simp_rw [hdiff]
    rw [integral_add (hψ.integrable one_le_two) (hDgL.integrable one_le_two)]
    simp_rw [mul_comm (D _)]
    rw [hmeanDg, add_zero]
  refine ⟨hmean, ?_, hψh⟩
  -- the cross term vanishes
  have hψc : ∀ ω, aipwScore T X Y e m₀ m₁ ω - c = a (X ω) + B ω - C ω := fun ω => by
    rw [aipwScore_eq]
    simp only [hadef, hBdef, hCdef]
    ring
  have hBD : ∀ ω, B ω * D ω = (1 - e (X ω)) * B ω := fun ω => by
    by_cases hω : ω ∈ T
    · simp [hBdef, hDdef, hω]; ring
    · simp [hBdef, hDdef, hω]
  have hCD : ∀ ω, C ω * D ω = -e (X ω) * C ω := fun ω => by
    by_cases hω : ω ∈ T
    · simp [hCdef, hDdef, hω]
    · simp [hCdef, hDdef, hω]; ring
  have hcross_pt : ∀ ω, (aipwScore T X Y e m₀ m₁ ω - c) * (D ω * g (X ω)) =
      (a (X ω) * g (X ω)) * D ω + ((1 - e (X ω)) * g (X ω)) * B ω +
        (e (X ω) * g (X ω)) * C ω := fun ω => by
    rw [hψc]
    have h1 := hBD ω
    have h2 := hCD ω
    linear_combination g (X ω) * h1 - g (X ω) * h2
  have hagL : Integrable (fun ω => a (X ω) * g (X ω)) μ := haL.integrable_mul hgL
  have i1 : Integrable (fun ω => (a (X ω) * g (X ω)) * D ω) μ :=
    (hagL.bdd_mul hDm.aestronglyMeasurable (Eventually.of_forall hDb)).congr
      (Eventually.of_forall fun ω => mul_comm _ _)
  have heb : ∀ x, ‖1 - e x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [he01 x]
  have heb' : ∀ x, ‖e x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [he01 x]
  have i2 : Integrable (fun ω => ((1 - e (X ω)) * g (X ω)) * B ω) μ :=
    (memLp_comp_mul hX (measurable_const.sub he) heb hgL).integrable_mul hB
  have i3 : Integrable (fun ω => (e (X ω) * g (X ω)) * C ω) μ :=
    (memLp_comp_mul hX he heb' hgL).integrable_mul hC
  have z1 : ∫ ω, (a (X ω) * g (X ω)) * D ω ∂μ = 0 :=
    integral_comp_mul_eq_zero_of_condExp (f := fun x => a x * g x) hX (ha.mul hg) iD i1 hDc
  have z2 : ∫ ω, ((1 - e (X ω)) * g (X ω)) * B ω ∂μ = 0 :=
    integral_comp_mul_eq_zero_of_condExp (f := fun x => (1 - e x) * g x) hX
      ((measurable_const.sub he).mul hg) (hB.integrable one_le_two) i2 hBc
  have z3 : ∫ ω, (e (X ω) * g (X ω)) * C ω ∂μ = 0 :=
    integral_comp_mul_eq_zero_of_condExp (f := fun x => e x * g x) hX (he.mul hg)
      (hC.integrable one_le_two) i3 hCc
  have hcross : ∫ ω, (aipwScore T X Y e m₀ m₁ ω - c) * (D ω * g (X ω)) ∂μ = 0 := by
    rw [integral_congr_ae (Eventually.of_forall hcross_pt), integral_add, integral_add, z1, z2, z3]
    · ring
    · exact i1
    · exact i2
    · exact i1.add i2
    · exact i3
  -- the quadratic term
  have hD2 : ∀ ω, (D ω * g (X ω)) ^ 2 =
      (g (X ω) ^ 2 * (1 - 2 * e (X ω))) * T.indicator 1 ω + g (X ω) ^ 2 * e (X ω) ^ 2 :=
    fun ω => by by_cases hω : ω ∈ T <;> simp [hDdef, hω] <;> ring
  have hg2 : Integrable (fun ω => g (X ω) ^ 2) μ := hgL.integrable_sq
  have hb12 : ∀ x, ‖1 - 2 * e x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [he01 x]
  have hbe2 : ∀ x, ‖e x ^ 2‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [he01 x]
  have hbe3 : ∀ x, ‖e x * (1 - e x)‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [he01 x]
  have i4' : Integrable (fun ω => g (X ω) ^ 2 * (1 - 2 * e (X ω))) μ :=
    (hg2.bdd_mul ((measurable_const.sub (measurable_const.mul he)).comp hX).aestronglyMeasurable
      (Eventually.of_forall fun ω => hb12 (X ω))).congr
      (Eventually.of_forall fun ω => mul_comm _ _)
  have i1T : Integrable (T.indicator (1 : Ω → ℝ)) μ := (integrable_const 1).indicator hT
  have i4 : Integrable (fun ω => (g (X ω) ^ 2 * (1 - 2 * e (X ω))) * T.indicator 1 ω) μ := by
    refine (i4'.bdd_mul (c := 1) i1T.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)).congr (Eventually.of_forall fun ω => mul_comm _ _)
    exact (norm_indicator_le_norm_self _ _).trans (by simp)
  have i5 : Integrable (fun ω => g (X ω) ^ 2 * e (X ω) ^ 2) μ :=
    (hg2.bdd_mul ((he.pow_const 2).comp hX).aestronglyMeasurable
      (Eventually.of_forall fun ω => hbe2 (X ω))).congr
      (Eventually.of_forall fun ω => mul_comm _ _)
  have i6 : Integrable (fun ω => g (X ω) ^ 2 * (1 - 2 * e (X ω)) * e (X ω)) μ :=
    (i4'.bdd_mul (he.comp hX).aestronglyMeasurable
      (Eventually.of_forall fun ω => heb' (X ω))).congr
      (Eventually.of_forall fun ω => mul_comm _ _)
  have hquad : ∫ ω, (D ω * g (X ω)) ^ 2 ∂μ =
      ∫ ω, e (X ω) * (1 - e (X ω)) * g (X ω) ^ 2 ∂μ := by
    rw [integral_congr_ae (Eventually.of_forall hD2), integral_add i4 i5,
      integral_comp_mul_eq_of_condExp (f := fun x => g x ^ 2 * (1 - 2 * e x)) (k := e) hX
        ((hg.pow_const 2).mul (measurable_const.sub (measurable_const.mul he))) i1T i4
        hH.propensity, ← integral_add i6 i5]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  -- assemble
  have hsq : ∀ ω, (augmentedIPWScore T X Y e h ω - c) ^ 2 = (aipwScore T X Y e m₀ m₁ ω - c) ^ 2 +
      2 * ((aipwScore T X Y e m₀ m₁ ω - c) * (D ω * g (X ω))) + (D ω * g (X ω)) ^ 2 :=
    fun ω => by rw [hdiff]; ring
  have iψc : MemLp (fun ω => aipwScore T X Y e m₀ m₁ ω - c) 2 μ := hψ.sub (memLp_const c)
  have j1 : Integrable (fun ω => (aipwScore T X Y e m₀ m₁ ω - c) ^ 2) μ := iψc.integrable_sq
  have j2 : Integrable (fun ω => (aipwScore T X Y e m₀ m₁ ω - c) * (D ω * g (X ω))) μ :=
    iψc.integrable_mul hDgL
  have j3 : Integrable (fun ω => (D ω * g (X ω)) ^ 2) μ := hDgL.integrable_sq
  rw [integral_congr_ae (Eventually.of_forall hsq), integral_add, integral_add, integral_const_mul,
    hcross, hquad]
  · ring
  · exact j1
  · exact j2.const_mul 2
  · exact j1.add (j2.const_mul 2)
  · exact j3

/-- **Every augmented IPW score is unbiased**: for a square-integrable augmentation `h(X)`,
`E[ψ_h] = E[Y₁ - Y₀]`. -/
theorem integral_augmentedIPWScore {h : 𝒳 → ℝ} (hh : Measurable h)
    (hhL : MemLp (fun ω => h (X ω)) 2 μ) :
    ∫ ω, augmentedIPWScore T X Y e h ω ∂μ = ∫ ω, (Y₁ ω - Y₀ ω) ∂μ :=
  (hH.integral_augmentedIPWScore_aux hh hhL 0).1.trans hH.integral_aipwScore

/-- **Variance in the augmented IPW class**: for a square-integrable augmentation `h(X)`,
`Var(ψ_h) = Var(ψ) + E[e(X)(1 - e(X))(h*(X) - h(X))²]` with
`h* = efficientAugmentation e m₀ m₁`. -/
theorem variance_augmentedIPWScore {h : 𝒳 → ℝ} (hh : Measurable h)
    (hhL : MemLp (fun ω => h (X ω)) 2 μ) :
    Var[augmentedIPWScore T X Y e h; μ] = Var[aipwScore T X Y e m₀ m₁; μ] +
      ∫ ω, e (X ω) * (1 - e (X ω)) * (efficientAugmentation e m₀ m₁ (X ω) - h (X ω)) ^ 2 ∂μ := by
  obtain ⟨hmean, hsq, hmem⟩ := hH.integral_augmentedIPWScore_aux hh hhL
    (∫ ω, aipwScore T X Y e m₀ m₁ ω ∂μ)
  rw [variance_eq_integral hmem.aestronglyMeasurable.aemeasurable,
    variance_eq_integral hH.memLp_aipwScore.aestronglyMeasurable.aemeasurable, hmean, hsq]

/-- **Hahn's bound is the minimum variance in the augmented IPW class.** Every augmented IPW
score with a square-integrable augmentation `h(X)` has variance at least
`E[s₁(X) / e(X) + s₀(X) / (1 - e(X)) + (τ(X) - τ)²]`, and the AIPW score attains it
(`variance_aipwScore`). -/
theorem hahnBound_le_variance_augmentedIPWScore {h : 𝒳 → ℝ} (hh : Measurable h)
    (hhL : MemLp (fun ω => h (X ω)) 2 μ) :
    hahnBound μ X e m₀ m₁ s₀ s₁ (∫ ω, (Y₁ ω - Y₀ ω) ∂μ) ≤ Var[augmentedIPWScore T X Y e h; μ] := by
  obtain ⟨ε, hε, heε⟩ := hH.overlap
  rw [hH.variance_augmentedIPWScore hh hhL, hH.variance_aipwScore, le_add_iff_nonneg_right]
  refine integral_nonneg fun ω => mul_nonneg (mul_nonneg ?_ ?_) (sq_nonneg _)
  · exact hε.le.trans (heε (X ω)).1
  · linarith [(heε (X ω)).2]

end HahnSetup

end Main

end MathlibExt.Probability.Causality.AugmentedIPW.HahnVariance
