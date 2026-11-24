/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Standardized threshold selection

A standardized threshold is measured from the population mean in units of the
population standard deviation. The selected mean is taken under the conditional
measure of the threshold event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- Population standard deviation, computed from the actual variance. -/
noncomputable def populationSD {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) : ℝ := √Var[f; μ]

/-- The Pearson quotient. It represents correlation on the domain where both variances
are positive. -/
noncomputable def pearsonRatio {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) : ℝ := cov[f, g; μ] / (populationSD μ f * populationSD μ g)

/-- Standardization by the population mean and standard deviation, used for positive variance. -/
noncomputable def standardizedValue {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (ω : Ω) : ℝ := (f ω - μ[f]) / populationSD μ f

/-- The upper event at standardized threshold `z`. -/
noncomputable def standardizedUpperEvent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (z : ℝ) : Set Ω := {ω | μ[f] + z * populationSD μ f ≤ f ω}

/-- The selected-group mean minus the population mean, used for positive-measure events. -/
noncomputable def conditionalMeanShift {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (s : Set Ω) : ℝ := (∫ ω, f ω ∂μ[|s]) - μ[f]

/-- Indicator weighting yields the actual conditional mean shift. -/
theorem conditionalMeanShift_eq_indicator_quotient {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} {f : Ω → ℝ}
    (hs : MeasurableSet s) (_hpos : 0 < μ s) :
    conditionalMeanShift μ f s =
      (∫ ω, s.indicator (fun _ => (1 : ℝ)) ω * f ω ∂μ) /
        (∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μ) - μ[f] := by
  classical
  have hmul : (fun ω => s.indicator (fun _ => (1 : ℝ)) ω * f ω) = s.indicator f := by
    funext ω
    by_cases h : ω ∈ s <;> simp [h]
  rw [conditionalMeanShift, ProbabilityTheory.cond, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul, hmul, integral_indicator hs, integral_indicator hs,
    setIntegral_const, smul_eq_mul, mul_one, div_eq_inv_mul]
  rfl

/-- Positive score rescaling preserves the standardized upper event. -/
theorem standardizedUpperEvent_const_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Ω → ℝ) (z : ℝ) {k : ℝ} (hk : 0 < k) :
    standardizedUpperEvent μ (fun ω => k * f ω) z = standardizedUpperEvent μ f z := by
  have hSD : populationSD μ (fun ω => k * f ω) = k * populationSD μ f := by
    rw [populationSD, variance_const_mul, Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq (le_of_lt hk)]
    rfl
  ext ω
  change (∫ w, k * f w ∂μ) + z * populationSD μ (fun w => k * f w) ≤ k * f ω ↔
    μ[f] + z * populationSD μ f ≤ f ω
  rw [integral_const_mul, hSD]
  rw [show k * μ[f] + z * (k * populationSD μ f) = k * (μ[f] + z * populationSD μ f) by ring]
  exact (mul_le_mul_iff_right₀ hk)

/-- An upper event for a negated score is the reflected lower event for the original score. -/
theorem standardizedUpperEvent_neg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (z : ℝ) :
    standardizedUpperEvent μ (fun ω => -f ω) z =
      {ω | f ω ≤ μ[f] - z * populationSD μ f} := by
  have hSD : populationSD μ (fun ω => -f ω) = populationSD μ f := by
    rw [populationSD, variance_fun_neg]
    rfl
  ext ω
  change (∫ w, -f w ∂μ) + z * populationSD μ (fun w => -f w) ≤ -f ω ↔
    f ω ≤ μ[f] - z * populationSD μ f
  rw [integral_neg, hSD]
  constructor <;> intro h <;> linarith

end ProbabilityTheory
