/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ModelInterop

/-!
# Tests for deterministic-kernel risk bridges

Boundary and non-vacuity checks for zero loss, constant estimators, and a Dirac
law with identity estimator.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MathlibExt.Probability.Statistics.EstimationRisk

namespace MathlibExtTest.Probability.Statistics.ModelInterop

/-! ### Boundary and non-vacuity checks -/

/-- Zero loss at the parameter `() : Unit` (a nonempty parameter type): the fixed-law bridge gives
the value `0`. -/
example {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (δ : S → A) (hδ : Measurable δ) (μ : ProbabilityMeasure S) :
    frequentistRiskENN δ (fun _ : Unit ↦ μ) (fun _ _ ↦ 0) () = 0 := by
  rw [← lintegral_deterministic_bind_eq_frequentistRiskENN δ hδ (fun _ : Unit ↦ μ)
    (fun _ _ ↦ 0) () measurable_const]
  simp

/-- Constant estimator: the deterministic output law is the point mass at the constant. -/
example {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (μ : ProbabilityMeasure S) (a : A) :
    (μ : Measure S).bind
        (Kernel.deterministic (fun _ : S ↦ a) (measurable_const : Measurable fun _ : S ↦ a)) =
      Measure.dirac a := by
  rw [Measure.deterministic_comp_eq_map, Measure.map_const, measure_univ, one_smul]

/-- Constant estimator through the fixed-law bridge: the frequentist risk is the loss at the
constant. -/
example {Θ S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (P : Θ → ProbabilityMeasure S)
    (ℓ : Θ → A → NNReal) (θ : Θ) (hℓ : Measurable fun a ↦ ((ℓ θ a : NNReal) : ℝ≥0∞)) (a : A) :
    frequentistRiskENN (fun _ : S ↦ a) P ℓ θ = ℓ θ a := by
  have hconst : Measurable fun _ : S ↦ a := measurable_const
  rw [← lintegral_deterministic_bind_eq_frequentistRiskENN _ hconst P ℓ θ hℓ,
    Measure.deterministic_comp_eq_map, Measure.map_const, measure_univ, one_smul,
    lintegral_dirac' a hℓ]

/-- Dirac law with the identity estimator: through the squared-error bridge, the extended mean
squared error is the extended nonnegative square at the support point `x`. -/
example (x θ : ℝ) :
    meanSquaredErrorENN id (⟨Measure.dirac x, inferInstance⟩ : ProbabilityMeasure ℝ) θ =
      ENNReal.ofReal ((x - θ) ^ 2) := by
  rw [← lintegral_deterministic_bind_ofReal_sq_eq_meanSquaredErrorENN id measurable_id
    ⟨Measure.dirac x, inferInstance⟩ θ, ProbabilityMeasure.coe_mk,
    Measure.deterministic_comp_eq_map, Measure.map_id, lintegral_dirac]
end MathlibExtTest.Probability.Statistics.ModelInterop
