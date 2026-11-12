/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification
public import MathlibExt.Probability.Causality.AugmentedIPW.MissingOutcomes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Finite-covariate Neyman orthogonality of the missing-mean AIPW score

The exact AIPW bias has zero Gateaux derivative at the true nuisances along
any fixed direction.
-/

@[expose] public section

open MeasureTheory Finset
open MathlibExt.Probability.Causality
open MathlibExt.Probability.Causality.MissingOutcomes

namespace MathlibExt.Probability.Causality.AugmentedIPW.Orthogonality

/-- Finite Neyman orthogonality: the AIPW bias has zero Gateaux derivative at
the true nuisances along any fixed direction.

Informal clause map: "finite covariate space" is `[Finite 𝒳]` (with
`[MeasurableSpace 𝒳]` and `[MeasurableSingletonClass 𝒳]`, and `Fintype 𝒳`
supplied locally by `Fintype.ofFinite`); "missing at random"
is `hmar : MissingAtRandom μ R Y X`; "response positivity" is
`hpos : ResponsePositivity μ R X`; "true nuisances as base point" is
`propensity μ R X` and `outcomeRegression μ Y X`; "any fixed direction" is
`δm δe : 𝒳 → ℝ`; "zero first-order Gateaux derivative at `t = 0`" is
`HasDerivAt … 0 0`. -/
theorem aipwScore_bias_gateaux_zero {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]
    {μ : Measure Ω} [Finite 𝒳] [IsProbabilityMeasure μ] {R : Set Ω}
    (hR : MeasurableSet R) {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ}
    (hY : Measurable Y) (hYi : Integrable Y μ)
    (hmar : MissingAtRandom μ R Y X) (hpos : ResponsePositivity μ R X)
    (δm δe : 𝒳 → ℝ) :
    HasDerivAt
      (fun t : ℝ => (∫ ω, aipwScore R X
        (fun x => propensity μ R X x + t * δe x)
        (fun x => outcomeRegression μ Y X x + t * δm x) Y ω ∂μ) -
        ∫ ω, Y ω ∂μ)
      0 0 := by
  have _fin := Fintype.ofFinite 𝒳
  have hrewrite : ∀ t : ℝ, (∫ ω, aipwScore R X
      (fun x => propensity μ R X x + t * δe x)
      (fun x => outcomeRegression μ Y X x + t * δm x) Y ω ∂μ) =
      ∫ ω, Y ω ∂μ + ∑ x, (propensity μ R X x /
        (propensity μ R X x + t * δe x) - 1) *
        (∫ ω in X ⁻¹' {x}, Y ω ∂μ -
          (outcomeRegression μ Y X x + t * δm x) * μ.real (X ⁻¹' {x})) := by
    intro t
    exact (integral_aipwScore_eq hR hX hY hYi hmar
      (fun x => propensity μ R X x + t * δe x)
      (fun x => outcomeRegression μ Y X x + t * δm x)).2
  simp only [hrewrite]
  have hfun : (fun t : ℝ => ∫ ω, Y ω ∂μ + ∑ x, (propensity μ R X x /
      (propensity μ R X x + t * δe x) - 1) *
      (∫ ω in X ⁻¹' {x}, Y ω ∂μ -
        (outcomeRegression μ Y X x + t * δm x) * μ.real (X ⁻¹' {x})) -
      ∫ ω, Y ω ∂μ) =
      (fun t : ℝ => ∑ x, (propensity μ R X x /
        (propensity μ R X x + t * δe x) - 1) *
        (∫ ω in X ⁻¹' {x}, Y ω ∂μ -
          (outcomeRegression μ Y X x + t * δm x) * μ.real (X ⁻¹' {x}))) := by
    funext t
    exact add_sub_cancel_left _ _
  rw [hfun]
  have hterm : ∀ x : 𝒳, HasDerivAt (fun t : ℝ => (propensity μ R X x /
      (propensity μ R X x + t * δe x) - 1) *
      (∫ ω in X ⁻¹' {x}, Y ω ∂μ -
        (outcomeRegression μ Y X x + t * δm x) * μ.real (X ⁻¹' {x}))) 0 0 := by
    intro x
    by_cases h0 : μ (X ⁻¹' {x}) = 0
    · have h2 : ∀ t : ℝ, (∫ ω in X ⁻¹' {x}, Y ω ∂μ -
          (outcomeRegression μ Y X x + t * δm x) * μ.real (X ⁻¹' {x})) = 0 := by
        intro t
        rw [Measure.restrict_eq_zero.2 h0, integral_zero_measure, measureReal_def, h0]
        simp
      have hfz : (fun t : ℝ => (propensity μ R X x /
          (propensity μ R X x + t * δe x) - 1) *
          (∫ ω in X ⁻¹' {x}, Y ω ∂μ -
            (outcomeRegression μ Y X x + t * δm x) * μ.real (X ⁻¹' {x}))) =
          fun _ => 0 :=
        funext fun t => by simp only [h2 t, mul_zero]
      rw [hfz]
      exact hasDerivAt_const 0 0
    · obtain ⟨ε, hε, hle⟩ := hpos
      have hpos' : 0 < propensity μ R X x := hε.trans_le (hle x h0)
      have hene : propensity μ R X x ≠ 0 := ne_of_gt hpos'
      have hpx : μ.real (X ⁻¹' {x}) ≠ 0 := fun h => h0 ((measureReal_eq_zero_iff).1 h)
      have hu0 : (fun t : ℝ => propensity μ R X x /
          (propensity μ R X x + t * δe x) - 1) 0 = 0 := by
        change propensity μ R X x / (propensity μ R X x + 0 * δe x) - 1 = 0
        rw [zero_mul, add_zero, div_self hene, sub_self]
      have hv0 : (fun t : ℝ => ∫ ω in X ⁻¹' {x}, Y ω ∂μ -
          (outcomeRegression μ Y X x + t * δm x) * μ.real (X ⁻¹' {x})) 0 = 0 := by
        change ∫ ω in X ⁻¹' {x}, Y ω ∂μ -
          (outcomeRegression μ Y X x + 0 * δm x) * μ.real (X ⁻¹' {x}) = 0
        rw [zero_mul, add_zero, outcomeRegression, div_mul_cancel₀ _ hpx, sub_self]
      obtain ⟨u', hu⟩ : ∃ u', HasDerivAt (fun t : ℝ => propensity μ R X x /
          (propensity μ R X x + t * δe x) - 1) u' 0 := by
        have hπ : HasDerivAt (fun t : ℝ => propensity μ R X x + t * δe x)
            (0 + 1 * δe x) 0 :=
          (hasDerivAt_const 0 _).add ((hasDerivAt_id 0).mul_const _)
        have hne : propensity μ R X x + 0 * δe x ≠ 0 := by
          rw [zero_mul, add_zero]; exact hene
        exact ⟨_, HasDerivAt.sub_const 1 ((hasDerivAt_const 0 _).div hπ hne)⟩
      obtain ⟨v', hv⟩ : ∃ v', HasDerivAt (fun t : ℝ => ∫ ω in X ⁻¹' {x}, Y ω ∂μ -
          (outcomeRegression μ Y X x + t * δm x) * μ.real (X ⁻¹' {x})) v' 0 := by
        have haff : HasDerivAt (fun t : ℝ => outcomeRegression μ Y X x + t * δm x)
            (0 + 1 * δm x) 0 :=
          (hasDerivAt_const 0 _).add ((hasDerivAt_id 0).mul_const _)
        exact ⟨_, (hasDerivAt_const 0 _).sub (haff.mul_const _)⟩
      have hmul := hu.mul hv
      have hD : u' * (fun t : ℝ => ∫ ω in X ⁻¹' {x}, Y ω ∂μ -
          (outcomeRegression μ Y X x + t * δm x) * μ.real (X ⁻¹' {x})) 0 +
          (fun t : ℝ => propensity μ R X x /
            (propensity μ R X x + t * δe x) - 1) 0 * v' = 0 := by
        rw [hu0, hv0, mul_zero, zero_mul, add_zero]
      rw [hD] at hmul
      exact hmul
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => hterm x)
  simpa using hsum

end MathlibExt.Probability.Causality.AugmentedIPW.Orthogonality
