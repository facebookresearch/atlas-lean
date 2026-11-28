/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Statistics.ManskiTreatmentBounds

open MeasureTheory WantedExt.Probability.Statistics.ManskiTreatmentBoundsWanted

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Y₀ Y₁ : Ω → ℝ)

-- With no treatment, only the control mean enters the bounds.
example :
    lowerBound μ ∅ Y₀ Y₁ = -(∫ ω, Y₀ ω ∂μ) ∧
      upperBound μ ∅ Y₀ Y₁ = 1 - ∫ ω, Y₀ ω ∂μ := by
  simp [lowerBound, upperBound]

-- With everyone treated, only the treatment mean enters the bounds.
example :
    lowerBound μ Set.univ Y₀ Y₁ = (∫ ω, Y₁ ω ∂μ) - 1 ∧
      upperBound μ Set.univ Y₀ Y₁ = ∫ ω, Y₁ ω ∂μ := by
  simp [lowerBound, upperBound]

example (T : Set Ω) (hT : MeasurableSet T) (h₀ : Measurable Y₀) (h₁ : Measurable Y₁)
    (h₀01 : ∀ ω, 0 ≤ Y₀ ω ∧ Y₀ ω ≤ 1) (h₁01 : ∀ ω, 0 ≤ Y₁ ω ∧ Y₁ ω ≤ 1) :
    upperBound μ T Y₀ Y₁ - lowerBound μ T Y₀ Y₁ = 1 :=
  (bounds_sound μ T hT Y₀ Y₁ h₀ h₁ h₀01 h₁01).2.2.1

open scoped ENNReal in
-- Both treatment arms have positive mass, and both endpoint witnesses preserve the observations.
example :
    let ν : Measure Bool :=
      (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false
    (∃ L₀ L₁ : Bool → ℝ, L₀ false = 0 ∧ L₁ true = 0 ∧
      (∫ ω, L₁ ω ∂ν) - ∫ ω, L₀ ω ∂ν = -(1 / 2 : ℝ)) ∧
    (∃ U₀ U₁ : Bool → ℝ, U₀ false = 0 ∧ U₁ true = 0 ∧
      (∫ ω, U₁ ω ∂ν) - ∫ ω, U₀ ω ∂ν = 1 / 2) := by
  intro ν
  let T : Set Bool := {true}
  have : IsProbabilityMeasure ν := ⟨by
    simpa only [ν, add_apply, smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one] using
        ENNReal.add_halves 1⟩
  have hmT : ν.real T = 1 / 2 := by simp [ν, T, measureReal_def]
  have hmTc : ν.real Tᶜ = 1 / 2 := by simp [ν, T, measureReal_def]
  have hf : false ∈ Tᶜ := by simp [T]
  have ht : true ∈ T := by simp [T]
  obtain ⟨⟨L₀, L₁, _, _, _, _, hL₁, hL₀, hL⟩, ⟨U₀, U₁, _, _, _, _, hU₁, hU₀, hU⟩⟩ :=
    bounds_sharp ν T MeasurableSet.of_discrete (fun _ => 0) (fun _ => 0)
      measurable_const measurable_const (by simp) (by simp)
  exact ⟨⟨L₀, L₁, hL₀ false hf, hL₁ true ht, by simpa [lowerBound, hmT] using hL⟩,
    ⟨U₀, U₁, hU₀ false hf, hU₁ true ht, by simpa [upperBound, hmTc] using hU⟩⟩
