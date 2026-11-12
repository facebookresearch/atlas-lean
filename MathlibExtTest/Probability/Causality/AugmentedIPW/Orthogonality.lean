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

/-- Positive and degenerate training fold in one: constant estimators over a
one-point (`Unit`, Dirac) training fold collapse the joint law to the
evaluation law and the tower identity to the merged exact identity. -/
example {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {μ : Measure Ω} [Fintype 𝒳]
    [IsProbabilityMeasure μ] {R : Set Ω} (hR : MeasurableSet R)
    {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ} (hY : Measurable Y)
    (hYi : Integrable Y μ) (hmar : MissingAtRandom μ R Y X) (π m : 𝒳 → ℝ) :
    ∫ z : Unit × Ω, aipwScore R X π m Y z.2
      ∂((Measure.dirac ()) |>.prod μ) =
      ∫ ω, aipwScore R X π m Y ω ∂μ := by
  have hgi : Integrable (aipwScore R X π m Y) μ :=
    (integral_aipwScore_eq hR hX hY hYi hmar π m).1
  have hprod : Integrable (fun z : Unit × Ω => aipwScore R X π m Y z.2)
      ((Measure.dirac ()) |>.prod μ) :=
    hgi.comp_snd _
  rw [integral_prod _ hprod, integral_dirac _ ()]

/-- Positivity is necessary for the zero-bias conclusion, not for the exact
identity: with an empty response event the true and candidate propensities are
both zero on the positive-mass stratum, MAR holds vacuously, yet the bias is
`-2` (the exact fiber identity holds and computes this value). So a correct
propensity alone does not imply unbiasedness without `ResponsePositivity`. -/
example :
    (∫ ω, aipwScore (∅ : Set (Fin 2)) (fun i : Fin 2 => decide (i = 1))
      (fun _ : Bool => (0 : ℝ)) (fun _ : Bool => (0 : ℝ)) (![0, 2]) ω
      ∂(Measure.dirac (1 : Fin 2))) -
    ∫ ω, (![0, 2] : Fin 2 → ℝ) ω ∂(Measure.dirac (1 : Fin 2)) = -2 := by
  have hmem : (1 : Fin 2) ∉ (∅ : Set (Fin 2)) := by simp
  have hY1 : (![0, 2] : Fin 2 → ℝ) 1 = 2 := by simp
  rw [integral_dirac _ _, integral_dirac _]
  simp only [aipwScore, Set.indicator_of_notMem hmem, hY1]
  norm_num

/-- Fiber instance: fixed (non-random) nuisances satisfy the fiber identity
directly, pinning the reduction of the fiber target to the merged theorem. -/
example {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {μ : Measure Ω} [Fintype 𝒳]
    [IsProbabilityMeasure μ] {R : Set Ω} (hR : MeasurableSet R)
    {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ} (hY : Measurable Y)
    (hYi : Integrable Y μ) (hmar : MissingAtRandom μ R Y X)
    (π m : 𝒳 → ℝ) (ωₜ : Unit) :
    ∫ ω, aipwScore R X ((fun _ : Unit => π) ωₜ) ((fun _ : Unit => m) ωₜ) Y ω ∂μ =
      ∫ ω, Y ω ∂μ +
      ∑ x, (propensity μ R X x / π x - 1) *
        (∫ ω in X ⁻¹' {x}, Y ω ∂μ - m x * μ.real (X ⁻¹' {x})) := by
  exact (integral_aipwScore_eq hR hX hY hYi hmar π m).2

end MathlibExtTest.Probability.Causality.AugmentedIPW.Orthogonality
