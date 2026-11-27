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
