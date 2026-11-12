/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# Augmented inverse probability weighting with missing outcomes

An outcome `Y` is observed only on the *response* event `R`; a covariate `X` with finitely many
values is always observed. The *augmented inverse probability weighted* (AIPW) score for the
population mean `E[Y]`, with a fixed response propensity `π` and a fixed outcome regression `m`
(both functions of the covariate value), is

`ψ = m(X) + 1_R (Y - m(X)) / π(X)`.

It depends on `Y` only on `R` (`aipwScore_congr`), so it is a statistic of the observed data. The
average treatment effect is the response-indicator interpretation applied twice: the treated
potential outcome `Y₁` is "observed" on the treated event `T`, the control potential outcome `Y₀`
on `Tᶜ`, and the ATE score is the difference of the two missing-outcome scores.

## Main definitions

* `outcomeRegression μ Y X x`: the full-data regression `E[Y | X = x]`, for a discrete `X`.
* `MissingAtRandom μ R Y X`: missing at random, the response event is conditionally independent
  of the outcome given the covariate (`CondIndepDiscrete`, a primitive statement about joint
  probabilities of `R`, `{Y ∈ B}` and `{X = x}`).
* `ResponsePositivity μ R X`: the response propensity `P(R | X = x)` is bounded below by some
  `ε > 0` on all covariate values of positive probability.
* `aipwScore R X π m Y`: the AIPW score above; `aipwATEScore T X e m₀ m₁ Y`: the AIPW score for
  the average treatment effect.

## Main results

* `integral_aipwScore_eq`: under MAR alone, the exact bias of the AIPW score,
  `E[ψ] - E[Y] = ∑ₓ (e(x) / π(x) - 1) (E[Y; X = x] - m(x) P(X = x))` with `e(x) = P(R | X = x)`:
  a sum over covariate values of the product of the response-propensity error and the
  regression error.
* **Double robustness**, in exactly two nuisances, the response propensity `π` and the outcome
  regression `m`: `integral_aipwScore` proves `E[ψ] = E[Y]` under MAR and positivity when
  either `π(x) = P(R | X = x)` or `m(x) = E[Y | X = x]` on every covariate value of positive
  probability. The two branches are `integral_aipwScore_of_propensity` (uses MAR and
  positivity) and `integral_aipwScore_of_regression` (uses MAR only; positivity is what makes
  this `m` identifiable from responders, not what the identity needs).
* `integral_aipwATEScore`: under strong ignorability of the treatment given `X`, the ATE score
  of the observed outcome has mean `E[Y₁ - Y₀]` when either the treatment propensity `e` is
  correct, or both arm regressions `m₀`, `m₁` are.
* `responsePositivity_iff`: for a covariate with finitely many values, positivity is the
  pointwise condition `P(R | X = x) > 0` on values of positive probability.
* `propensity_compl`, `condIndepDiscrete_compl`: the control arm `Tᶜ` inherits the propensity
  `1 - e` and the conditional independence of the treated arm.

## Scope: fixed nuisances, no inference

The nuisances `π`, `m`, `e`, `m₀`, `m₁` are **fixed functions** of the covariate value. Nothing
here concerns estimated or cross-fitted nuisances, and **no inference is claimed**: no standard
errors, rates, asymptotic normality, efficiency or semiparametric bounds. The results are
population (expectation) identities, stated for a probability measure `μ` so that integrals
are means. The covariate takes finitely many values; general
covariates are not covered. Missing-not-at-random identification is not covered; the tests
contain an MNAR example where both nuisances are correct and the score is biased.

## Source receipt (API-00 reuse gate)

Reuse search (2026-11-11, base `origin/main` `53666a3c1`): the terms `aipw`, `augmented ipw`,
`doubly robust`, `double robust`, `MissingAtRandom`, `missing at random` have no match in
`MathlibExt`, `MathlibExtTest`, `WantedExt`, `CSLibExt`, `blueprint`, `docs`, nor (with
`inverse probability`) in Mathlib `v4.35.0`. Reused from
`MathlibExt/Probability/Causality/CausalIdentification.lean` (on `origin/main`):
`CondIndepDiscrete`, `propensity`, `observed`, `StronglyIgnorable`, `StronglyIgnorable.comp`,
`measureReal_inter_preimage_eq_propensity_mul`, `setIntegral_inter_eq_propensity_mul` (the last
two made public in that file for this reuse).
From Mathlib: `integral_iUnion_fintype`, `integrableOn_finite_iUnion`, `setIntegral_indicator`,
`measureReal_inter_add_sdiff`, `integral_map`. The AIPW score is defined locally; no unmerged
sibling file is imported.

## References

* D. B. Rubin, *Inference and missing data*, Biometrika 63(3) (1976), 581–592.
* J. M. Robins, A. Rotnitzky and L. P. Zhao, *Estimation of regression coefficients when some
  regressors are not always observed*, JASA 89(427) (1994), 846–866.
* H. Bang and J. M. Robins, *Doubly robust estimation in missing data and causal inference
  models*, Biometrics 61(4) (2005), 962–973.
* A. A. Tsiatis, *Semiparametric Theory and Missing Data*, Springer (2006).
-/

@[expose] public section

open MeasureTheory Finset

namespace MathlibExt.Probability.Causality.MissingOutcomes

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The full-data outcome regression `E[Y | X = x] = E[Y; X = x] / P(X = x)` for a discrete
covariate. It is `0` (a junk value) when `P(X = x) = 0`. -/
noncomputable def outcomeRegression (μ : Measure Ω) (Y : Ω → ℝ) (X : Ω → 𝒳) (x : 𝒳) : ℝ :=
  (∫ ω in X ⁻¹' {x}, Y ω ∂μ) / μ.real (X ⁻¹' {x})

/-- **Missing at random** (Rubin 1976), for a discrete covariate: the response event `R` is
conditionally independent of the outcome `Y` given `X`, stated through joint probabilities,
`P(R, Y ∈ B, X = x) P(X = x) = P(R, X = x) P(Y ∈ B, X = x)`. It holds vacuously when every
level set `{X = x}` is null (an atomless `X`); every result here that uses MAR assumes `X` has
finitely many values, where this cannot happen under a nonzero measure. -/
def MissingAtRandom (μ : Measure Ω) (R : Set Ω) (Y : Ω → ℝ) (X : Ω → 𝒳) : Prop :=
  CondIndepDiscrete μ R Y X

/-- **Positivity** of the response: `P(R | X = x) ≥ ε` for some `ε > 0` and every covariate
value of positive probability. -/
def ResponsePositivity (μ : Measure Ω) (R : Set Ω) (X : Ω → 𝒳) : Prop :=
  ∃ ε > 0, ∀ x, μ (X ⁻¹' {x}) ≠ 0 → ε ≤ propensity μ R X x

/-- The **AIPW score** for the mean of an outcome `Y` observed on the response event `R`, with a
fixed response propensity `π` and a fixed outcome regression `m`:
`ψ = m(X) + 1_R (Y - m(X)) / π(X)`.

Convention at `π(x) = 0`: Lean sets `a / 0 = 0`, so on a stratum with `π(x) = 0` the score is
`m(X)` (the residual term is dropped), and the factor `e(x) / π(x) - 1` of
`integral_aipwScore_eq` is `-1`. In ordinary notation the score is undefined there. -/
noncomputable def aipwScore (R : Set Ω) (X : Ω → 𝒳) (π m : 𝒳 → ℝ) (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω => m (X ω) + R.indicator (fun ω => (Y ω - m (X ω)) / π (X ω)) ω

/-- The **AIPW score for the average treatment effect** with treatment event `T`, a fixed
treatment propensity `e` and fixed arm regressions `m₀`, `m₁`: the missing-outcome score of the
treated arm (response event `T`, propensity `e`) minus that of the control arm (response event
`Tᶜ`, propensity `1 - e`). Applied to the observed outcome `observed T Y₀ Y₁`.

It equals, pointwise, the AIPW ATE score of `AugmentedIPW/Score.lean` (task T28, not merged at
the time of writing), `aipwScore T X Y e m₀ m₁` there, up to argument order; the two are to be
unified at integration. -/
noncomputable def aipwATEScore (T : Set Ω) (X : Ω → 𝒳) (e m₀ m₁ : 𝒳 → ℝ) (Y : Ω → ℝ) :
    Ω → ℝ :=
  fun ω => aipwScore T X e m₁ Y ω - aipwScore Tᶜ X (fun x => 1 - e x) m₀ Y ω

omit [MeasurableSpace Ω] in
/-- The AIPW score is a statistic of the observed data: it depends on `Y` only on `R`. -/
theorem aipwScore_congr {R : Set Ω} {X : Ω → 𝒳} {π m : 𝒳 → ℝ} {Y Y' : Ω → ℝ}
    (h : Set.EqOn Y Y' R) : aipwScore R X π m Y = aipwScore R X π m Y' := by
  funext ω
  by_cases hω : ω ∈ R
  · simp [aipwScore, hω, h hω]
  · simp [aipwScore, hω]

/-- For a covariate with finitely many values, positivity is the pointwise condition
`P(R | X = x) > 0` on values of positive probability. -/
theorem responsePositivity_iff [Finite 𝒳] {R : Set Ω} {X : Ω → 𝒳} :
    ResponsePositivity μ R X ↔ ∀ x, μ (X ⁻¹' {x}) ≠ 0 → 0 < propensity μ R X x := by
  constructor
  · rintro ⟨ε, hε, h⟩ x hx
    exact hε.trans_le (h x hx)
  · intro h
    have := Fintype.ofFinite 𝒳
    classical
    set S := univ.filter fun x => μ (X ⁻¹' {x}) ≠ 0
    rcases S.eq_empty_or_nonempty with hS | hS
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have hx' : x ∈ S := mem_filter.2 ⟨mem_univ x, hx⟩
      simp [hS] at hx'
    · obtain ⟨x₀, hx₀, hmin⟩ := S.exists_min_image (fun x => propensity μ R X x) hS
      exact ⟨_, h x₀ (mem_filter.1 hx₀).2, fun x hx => hmin x (mem_filter.2 ⟨mem_univ x, hx⟩)⟩

/-- `P(Rᶜ | X = x) = 1 - P(R | X = x)` on a covariate value of positive probability. -/
theorem propensity_compl [IsFiniteMeasure μ] {R : Set Ω} (hR : MeasurableSet R) {X : Ω → 𝒳}
    {x : 𝒳} (hx : μ (X ⁻¹' {x}) ≠ 0) :
    propensity μ Rᶜ X x = 1 - propensity μ R X x := by
  have h0 : μ.real (X ⁻¹' {x}) ≠ 0 := fun h => hx ((measureReal_eq_zero_iff).1 h)
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := X ⁻¹' {x}) hR
  have e1 : Rᶜ ∩ X ⁻¹' {x} = X ⁻¹' {x} \ R := by ext; simp [and_comm]
  rw [propensity, propensity, e1, Set.inter_comm R, eq_sub_iff_add_eq, ← add_div,
    add_comm (μ.real (X ⁻¹' {x} \ R)), hsplit, div_self h0]

/-- Conditional independence of an event and a variable given a discrete variable passes to the
complementary event. -/
theorem condIndepDiscrete_compl {β γ : Type*} [MeasurableSpace β] [IsFiniteMeasure μ]
    {T : Set Ω} (hT : MeasurableSet T) {V : Ω → β} {W : Ω → γ}
    (h : CondIndepDiscrete μ T V W) : CondIndepDiscrete μ Tᶜ V W := by
  intro B hB w
  have h1 := measureReal_inter_add_sdiff (μ := μ) (s := V ⁻¹' B ∩ W ⁻¹' {w}) hT
  have h2 := measureReal_inter_add_sdiff (μ := μ) (s := W ⁻¹' {w}) hT
  have e1 : Tᶜ ∩ V ⁻¹' B ∩ W ⁻¹' {w} = (V ⁻¹' B ∩ W ⁻¹' {w}) \ T := by
    ext; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto
  have e2 : Tᶜ ∩ W ⁻¹' {w} = W ⁻¹' {w} \ T := by
    ext; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto
  have e3 : V ⁻¹' B ∩ W ⁻¹' {w} ∩ T = T ∩ V ⁻¹' B ∩ W ⁻¹' {w} := by
    ext; simp only [Set.mem_inter_iff]; tauto
  rw [e3] at h1
  rw [Set.inter_comm] at h2
  rw [e1, e2]
  linear_combination μ.real (W ⁻¹' {w}) * h1 - μ.real (V ⁻¹' B ∩ W ⁻¹' {w}) * h2 - h B hB w

/-- On a covariate value of probability zero the regression error term vanishes. -/
private lemma stratumError_eq_zero {Y : Ω → ℝ} {X : Ω → 𝒳} {m : 𝒳 → ℝ} {x : 𝒳}
    (h : μ (X ⁻¹' {x}) = 0) :
    ∫ ω in X ⁻¹' {x}, Y ω ∂μ - m x * μ.real (X ⁻¹' {x}) = 0 := by
  rw [Measure.restrict_eq_zero.2 h, integral_zero_measure, measureReal_def, h]
  simp

section Finite

variable [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]

/-- The AIPW score on one covariate stratum: integrable there, with integral
`E[Y; X = x] + (e(x) / π(x) - 1) (E[Y; X = x] - m(x) P(X = x))` under MAR. -/
private lemma setIntegral_aipwScore [IsFiniteMeasure μ] {R : Set Ω} (hR : MeasurableSet R)
    {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ} (hY : Measurable Y) (hYi : Integrable Y μ)
    (hmar : MissingAtRandom μ R Y X) (π m : 𝒳 → ℝ) (x : 𝒳) :
    IntegrableOn (aipwScore R X π m Y) (X ⁻¹' {x}) μ ∧
      ∫ ω in X ⁻¹' {x}, aipwScore R X π m Y ω ∂μ =
        ∫ ω in X ⁻¹' {x}, Y ω ∂μ + (propensity μ R X x / π x - 1) *
          (∫ ω in X ⁻¹' {x}, Y ω ∂μ - m x * μ.real (X ⁻¹' {x})) := by
  set A := X ⁻¹' {x}
  have hA : MeasurableSet A := hX (measurableSet_singleton x)
  have heq : Set.EqOn (aipwScore R X π m Y)
      (fun ω => m x + (π x)⁻¹ * R.indicator (fun ω => Y ω - m x) ω) A := by
    intro ω hω
    have hω' : X ω = x := hω
    by_cases hr : ω ∈ R <;> simp [aipwScore, hr, hω', div_eq_inv_mul]
  have hYm : Integrable (fun ω => Y ω - m x) μ := hYi.sub (integrable_const _)
  have hg : Integrable (fun ω => m x + (π x)⁻¹ * R.indicator (fun ω => Y ω - m x) ω) μ :=
    (integrable_const _).add ((hYm.indicator hR).const_mul _)
  refine ⟨hg.integrableOn.congr_fun heq.symm hA, ?_⟩
  rw [setIntegral_congr_fun hA heq, integral_add (integrable_const _)
    ((hYm.indicator hR).const_mul _).integrableOn, setIntegral_const, integral_const_mul,
    setIntegral_indicator hR, integral_sub hYi.integrableOn (integrable_const _),
    setIntegral_const, Set.inter_comm, setIntegral_inter_eq_propensity_mul hY hmar,
    measureReal_inter_preimage_eq_propensity_mul, smul_eq_mul, smul_eq_mul, div_eq_mul_inv]
  ring

/-- **Exact bias of the AIPW score under MAR**: for a covariate with finitely many values, the
score is integrable and
`E[ψ] = E[Y] + ∑ₓ (e(x) / π(x) - 1) (E[Y; X = x] - m(x) P(X = x))`, `e(x) = P(R | X = x)`.
Each term is the product of the response-propensity error and the regression error on the
stratum `X = x`. Neither positivity nor any condition on `π`, `m` is assumed; for `π(x) = 0`
the identity uses the convention in `aipwScore` (the factor is `-1`). -/
theorem integral_aipwScore_eq [Fintype 𝒳] [IsProbabilityMeasure μ] {R : Set Ω}
    (hR : MeasurableSet R) {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ} (hY : Measurable Y)
    (hYi : Integrable Y μ) (hmar : MissingAtRandom μ R Y X) (π m : 𝒳 → ℝ) :
    Integrable (aipwScore R X π m Y) μ ∧
      ∫ ω, aipwScore R X π m Y ω ∂μ = ∫ ω, Y ω ∂μ +
        ∑ x, (propensity μ R X x / π x - 1) *
          (∫ ω in X ⁻¹' {x}, Y ω ∂μ - m x * μ.real (X ⁻¹' {x})) := by
  have hU : (⋃ x, X ⁻¹' {x}) = Set.univ := by ext ω; simp
  have hA : ∀ x : 𝒳, MeasurableSet (X ⁻¹' {x}) := fun x => hX (measurableSet_singleton x)
  have hdisj : Pairwise (Function.onFun Disjoint fun x : 𝒳 => X ⁻¹' {x}) := fun x y hxy =>
    Set.disjoint_left.2 fun ω h1 h2 => hxy (h1.symm.trans h2)
  have hstr := setIntegral_aipwScore hR hX hY hYi hmar π m
  have hint : Integrable (aipwScore R X π m Y) μ := by
    rw [← integrableOn_univ, ← hU]
    exact integrableOn_finite_iUnion.2 fun x => (hstr x).1
  refine ⟨hint, ?_⟩
  have hsplit : ∀ g : Ω → ℝ, (∀ x, IntegrableOn g (X ⁻¹' {x}) μ) →
      ∫ ω, g ω ∂μ = ∑ x, ∫ ω in X ⁻¹' {x}, g ω ∂μ := by
    intro g hg
    rw [← setIntegral_univ, ← hU, integral_iUnion_fintype hA hdisj hg]
  rw [hsplit _ fun x => (hstr x).1, hsplit _ fun x => hYi.integrableOn, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => (hstr x).2

/-- **Double robustness, propensity branch**: under MAR and positivity, if the response
propensity is correct, `π(x) = P(R | X = x)` on covariate values of positive probability, the
AIPW score is unbiased for `E[Y]` whatever the regression `m`. -/
theorem integral_aipwScore_of_propensity [Finite 𝒳] [IsProbabilityMeasure μ] {R : Set Ω}
    (hR : MeasurableSet R) {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ} (hY : Measurable Y)
    (hYi : Integrable Y μ) (hmar : MissingAtRandom μ R Y X) (hpos : ResponsePositivity μ R X)
    {π : 𝒳 → ℝ} (m : 𝒳 → ℝ) (hπ : ∀ x, μ (X ⁻¹' {x}) ≠ 0 → π x = propensity μ R X x) :
    ∫ ω, aipwScore R X π m Y ω ∂μ = ∫ ω, Y ω ∂μ := by
  have := Fintype.ofFinite 𝒳
  rw [(integral_aipwScore_eq hR hX hY hYi hmar π m).2, add_eq_left]
  refine sum_eq_zero fun x _ => ?_
  by_cases h0 : μ (X ⁻¹' {x}) = 0
  · rw [stratumError_eq_zero h0, mul_zero]
  · obtain ⟨ε, hε, hle⟩ := hpos
    rw [hπ x h0, div_self (hε.trans_le (hle x h0)).ne', sub_self, zero_mul]

/-- **Double robustness, regression branch**: under MAR, if the outcome regression is correct,
`m(x) = E[Y | X = x]` on covariate values of positive probability, the AIPW score is unbiased
for `E[Y]` whatever the response propensity `π` (including `π(x) = 0`, with the convention in
`aipwScore`). Positivity is not used by this identity; it is
what makes this `m` identifiable from the responders (`E[Y | X = x] = E[Y | R, X = x]`). -/
theorem integral_aipwScore_of_regression [Finite 𝒳] [IsProbabilityMeasure μ] {R : Set Ω}
    (hR : MeasurableSet R) {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ} (hY : Measurable Y)
    (hYi : Integrable Y μ) (hmar : MissingAtRandom μ R Y X) (π : 𝒳 → ℝ) {m : 𝒳 → ℝ}
    (hm : ∀ x, μ (X ⁻¹' {x}) ≠ 0 → m x = outcomeRegression μ Y X x) :
    ∫ ω, aipwScore R X π m Y ω ∂μ = ∫ ω, Y ω ∂μ := by
  have := Fintype.ofFinite 𝒳
  rw [(integral_aipwScore_eq hR hX hY hYi hmar π m).2, add_eq_left]
  refine sum_eq_zero fun x _ => ?_
  by_cases h0 : μ (X ⁻¹' {x}) = 0
  · rw [stratumError_eq_zero h0, mul_zero]
  · have h0' : μ.real (X ⁻¹' {x}) ≠ 0 := fun h => h0 ((measureReal_eq_zero_iff).1 h)
    rw [hm x h0, outcomeRegression, div_mul_cancel₀ _ h0', sub_self, mul_zero]

/-- **Double robustness of the AIPW score with missing outcomes** (Robins, Rotnitzky & Zhao
1994; Bang & Robins 2005): for a covariate with finitely many values, under missing at random
and positivity of the response, `E[m(X) + 1_R (Y - m(X)) / π(X)] = E[Y]` when **either** the
response propensity is correct (`π(x) = P(R | X = x)`) **or** the outcome regression is correct
(`m(x) = E[Y | X = x]`), on every covariate value of positive probability. The nuisances are
fixed functions. -/
theorem integral_aipwScore [Finite 𝒳] [IsProbabilityMeasure μ] {R : Set Ω}
    (hR : MeasurableSet R) {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ} (hY : Measurable Y)
    (hYi : Integrable Y μ) (hmar : MissingAtRandom μ R Y X) (hpos : ResponsePositivity μ R X)
    (π m : 𝒳 → ℝ)
    (hnuis : (∀ x, μ (X ⁻¹' {x}) ≠ 0 → π x = propensity μ R X x) ∨
      (∀ x, μ (X ⁻¹' {x}) ≠ 0 → m x = outcomeRegression μ Y X x)) :
    ∫ ω, aipwScore R X π m Y ω ∂μ = ∫ ω, Y ω ∂μ := by
  rcases hnuis with hπ | hm
  · exact integral_aipwScore_of_propensity hR hX hY hYi hmar hpos m hπ
  · exact integral_aipwScore_of_regression hR hX hY hYi hmar π hm

/-- **Double robustness of the AIPW score for the average treatment effect**: for a covariate
with finitely many values, under strong ignorability of the treatment `T` given `X` for the pair
of potential outcomes (`CondIndepDiscrete` plus overlap `0 < P(T | X = x) < 1`), the ATE score
of the observed outcome has mean `E[Y₁ - Y₀]` when **either** the treatment propensity is correct
(`e(x) = P(T | X = x)`) **or** both arm regressions are correct (`m₀(x) = E[Y₀ | X = x]` and
`m₁(x) = E[Y₁ | X = x]`), on every covariate value of positive probability. -/
theorem integral_aipwATEScore [Finite 𝒳] [IsProbabilityMeasure μ] {T : Set Ω}
    (hT : MeasurableSet T) {X : Ω → 𝒳} (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ}
    (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁) (hY₀i : Integrable Y₀ μ)
    (hY₁i : Integrable Y₁ μ) (h : StronglyIgnorable μ T (fun ω => (Y₀ ω, Y₁ ω)) X)
    (e m₀ m₁ : 𝒳 → ℝ)
    (hnuis : (∀ x, μ (X ⁻¹' {x}) ≠ 0 → e x = propensity μ T X x) ∨
      ((∀ x, μ (X ⁻¹' {x}) ≠ 0 → m₀ x = outcomeRegression μ Y₀ X x) ∧
        (∀ x, μ (X ⁻¹' {x}) ≠ 0 → m₁ x = outcomeRegression μ Y₁ X x))) :
    ∫ ω, aipwATEScore T X e m₀ m₁ (observed T Y₀ Y₁) ω ∂μ = ∫ ω, (Y₁ ω - Y₀ ω) ∂μ := by
  have := Fintype.ofFinite 𝒳
  have hmar₁ : MissingAtRandom μ T Y₁ X := (h.comp measurable_snd).1
  have hmar₀ : MissingAtRandom μ Tᶜ Y₀ X := condIndepDiscrete_compl hT (h.comp measurable_fst).1
  have hpos₁ : ResponsePositivity μ T X := responsePositivity_iff.2 fun x hx => (h.2 x hx).1
  have hpos₀ : ResponsePositivity μ Tᶜ X := responsePositivity_iff.2 fun x hx => by
    rw [propensity_compl hT hx]
    exact sub_pos.2 (h.2 x hx).2
  have hobs₁ : aipwScore T X e m₁ (observed T Y₀ Y₁) = aipwScore T X e m₁ Y₁ :=
    aipwScore_congr fun ω hω => by simp [observed, hω]
  have hobs₀ : aipwScore Tᶜ X (fun x => 1 - e x) m₀ (observed T Y₀ Y₁) =
      aipwScore Tᶜ X (fun x => 1 - e x) m₀ Y₀ :=
    aipwScore_congr fun ω hω => by simp [observed, Set.notMem_of_mem_compl hω, hω]
  have hi₁ := (integral_aipwScore_eq hT hX hY₁ hY₁i hmar₁ e m₁).1
  have hi₀ := (integral_aipwScore_eq hT.compl hX hY₀ hY₀i hmar₀ (fun x => 1 - e x) m₀).1
  simp only [aipwATEScore, hobs₁, hobs₀]
  rw [integral_sub hi₁ hi₀, integral_sub hY₁i hY₀i]
  congr 1
  · exact integral_aipwScore hT hX hY₁ hY₁i hmar₁ hpos₁ e m₁
      (hnuis.imp id fun hm => hm.2)
  · refine integral_aipwScore hT.compl hX hY₀ hY₀i hmar₀ hpos₀ (fun x => 1 - e x) m₀
      (hnuis.imp (fun he x hx => ?_) fun hm => hm.1)
    rw [propensity_compl hT hx, he x hx]

end Finite

end MathlibExt.Probability.Causality.MissingOutcomes
