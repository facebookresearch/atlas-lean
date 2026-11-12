/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.Orthogonality

/-!
# Tests for finite Neyman orthogonality

Both-wrong non-vacuity fixture, one-nuisance-correct axes, and the null-stratum
boundary.
-/

@[expose] public section

open MeasureTheory Finset
open MathlibExt.Probability.Causality
open MathlibExt.Probability.Causality.MissingOutcomes
open MathlibExt.Probability.Causality.AugmentedIPW.Orthogonality

namespace MathlibExtTest.Probability.Causality.AugmentedIPW.Orthogonality

/-- Both-wrong fixture with nonzero bias: two-point space, Dirac law at
`1`, response on `{1}`, wrong propensity `1 / 2` and wrong regression `0`
give bias `2`, while the Gateaux derivative at truth along any direction is
still `0`. The `2` below is `E[ψ] - E[Y]`, not the score itself. -/
example :
    (∫ ω, aipwScore ({1} : Set (Fin 2)) (fun i : Fin 2 => decide (i = 1))
      (fun _ => (1 / 2 : ℝ)) (fun _ => (0 : ℝ)) (![0, 2]) ω
      ∂(Measure.dirac (1 : Fin 2))) -
    ∫ ω, (![0, 2] : Fin 2 → ℝ) ω ∂(Measure.dirac (1 : Fin 2)) = 2 := by
  have hmem : (1 : Fin 2) ∈ ({1} : Set (Fin 2)) := rfl
  have hY1 : (![0, 2] : Fin 2 → ℝ) 1 = 2 := by simp
  rw [integral_dirac _ _, integral_dirac _ _]
  simp only [aipwScore, Set.indicator_of_mem hmem, hY1]
  norm_num

/-- Axis corollary, propensity-correct line: with `e* = e` the bias function
is identically zero along every regression direction. -/
example {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {μ : Measure Ω} [Fintype 𝒳]
    [IsProbabilityMeasure μ] {R : Set Ω} (hR : MeasurableSet R)
    {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ} (hY : Measurable Y)
    (hYi : Integrable Y μ) (hmar : MissingAtRandom μ R Y X)
    (hpos : ResponsePositivity μ R X) (δm : 𝒳 → ℝ) :
    (fun t : ℝ => (∫ ω, aipwScore R X (fun x => propensity μ R X x)
      (fun x => outcomeRegression μ Y X x + t * δm x) Y ω ∂μ) -
      ∫ ω, Y ω ∂μ) = fun _ => 0 := by
  funext t
  have h := integral_aipwScore_of_propensity hR hX hY hYi hmar hpos
    (m := fun x => outcomeRegression μ Y X x + t * δm x) (fun x _ => rfl)
  simp only [h, sub_self]

set_option linter.unusedVariables false in
/-- Axis corollary, regression-correct line: with `m* = m` the bias function
is identically zero along every propensity direction. -/
example {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {μ : Measure Ω} [Fintype 𝒳]
    [IsProbabilityMeasure μ] {R : Set Ω} (hR : MeasurableSet R)
    {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ} (hY : Measurable Y)
    (hYi : Integrable Y μ) (hmar : MissingAtRandom μ R Y X)
    (hpos : ResponsePositivity μ R X) (δe : 𝒳 → ℝ) :
    (fun t : ℝ => (∫ ω, aipwScore R X
      (fun x => propensity μ R X x + t * δe x)
      (fun x => outcomeRegression μ Y X x) Y ω ∂μ) -
      ∫ ω, Y ω ∂μ) = fun _ => 0 := by
  funext t
  have h := integral_aipwScore_of_regression hR hX hY hYi hmar
    (π := fun x => propensity μ R X x + t * δe x) (fun x _ => rfl)
  simp only [h, sub_self]

set_option linter.unusedVariables false in
/-- Null-stratum boundary: the summand at a null stratum vanishes for every
candidate pair, so it never threatens differentiability. -/
example {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {μ : Measure Ω} [Fintype 𝒳]
    [IsProbabilityMeasure μ] {R : Set Ω} {X : Ω → 𝒳} (hX : Measurable X)
    {Y : Ω → ℝ} (hY : Measurable Y) (x₀ : 𝒳)
    (h0 : μ (X ⁻¹' {x₀}) = 0) (π m : 𝒳 → ℝ) :
    (propensity μ R X x₀ / π x₀ - 1) *
      (∫ ω in X ⁻¹' {x₀}, Y ω ∂μ - m x₀ * μ.real (X ⁻¹' {x₀})) = 0 := by
  have h : (∫ ω in X ⁻¹' {x₀}, Y ω ∂μ - m x₀ * μ.real (X ⁻¹' {x₀})) = 0 := by
    rw [Measure.restrict_eq_zero.2 h0, integral_zero_measure, measureReal_def, h0]
    simp
  rw [h, mul_zero]

end MathlibExtTest.Probability.Causality.AugmentedIPW.Orthogonality
