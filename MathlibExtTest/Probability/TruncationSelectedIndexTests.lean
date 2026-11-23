/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Truncation
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section
open MeasureTheory ProbabilityTheory
open ProbabilityTheory.KolmogorovThreeSeries
open scoped ENNReal

namespace MathlibExtTest.Probability.TruncationSelectedIndexTests

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Lp requires measurability only of the selected coordinate. -/
theorem selected_memLp [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (n : ℕ) (hX : Measurable (X n)) (A : ℝ) (p : ℝ≥0∞) :
    MemLp (truncatedRV X A n) p μ :=
  memLp_truncatedRV n hX A p

/-- Integrability requires no hypotheses about the other coordinates. -/
theorem selected_integrable [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (n : ℕ) (hX : Measurable (X n)) (A : ℝ) :
    Integrable (truncatedRV X A n) μ :=
  integrable_truncatedRV n hX A

/-- The selected-variable premise also suffices for the variance bound. -/
theorem selected_variance [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (n : ℕ) (hX : Measurable (X n)) (A : ℝ) :
    variance (truncatedRV X A n) μ ≤ A^2 :=
  variance_truncatedRV_le n hX A

/-- The selected-variable premise also suffices for the absolute mean bound. -/
theorem selected_mean [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (n : ℕ) (hX : Measurable (X n)) (A : ℝ) :
    |∫ ω, truncatedRV X A n ω ∂μ| ≤ |A| :=
  abs_integral_truncatedRV_le n hX A

section BoolExample

local instance : MeasurableSpace Bool := ⊥

/-- Coordinate zero is constant; coordinate one distinguishes the two Bool points. -/
def partialFamily (n : ℕ) (b : Bool) : ℝ :=
  if n = 0 then 2 else if b then 1 else 0

/-- The selected coordinate is measurable for the trivial sigma algebra. -/
theorem partial_zero_measurable : Measurable (partialFamily 0) := by
  have heq : partialFamily 0 = fun _ => (2 : ℝ) := by
    funext b
    simp [partialFamily]
  rw [heq]
  exact measurable_const

/-- Another coordinate is genuinely nonmeasurable in that same space. -/
theorem partial_one_not_measurable : ¬ Measurable (partialFamily 1) := by
  intro h
  obtain ⟨c, hc⟩ := eq_const_of_measurable_bot h
  have hf := congr_fun hc false
  have ht := congr_fun hc true
  norm_num [partialFamily] at hf ht
  linarith

/-- The moment API applies despite the nonmeasurable unused coordinate. -/
theorem partial_zero_memLp :
    MemLp (truncatedRV partialFamily 2 0) 2 (Measure.dirac (false : Bool)) :=
  memLp_truncatedRV 0 partial_zero_measurable 2 2

/-- Integrability likewise depends only on the selected constant coordinate. -/
theorem partial_zero_integrable :
    Integrable (truncatedRV partialFamily 2 0) (Measure.dirac (false : Bool)) :=
  integrable_truncatedRV 0 partial_zero_measurable 2

/-- The probability-space mean bound applies with only selected measurability. -/
theorem partial_zero_mean_bound :
    |∫ b, truncatedRV partialFamily 2 0 b ∂Measure.dirac (false : Bool)| ≤ 2 := by
  simpa using abs_integral_truncatedRV_le 0 partial_zero_measurable 2

end BoolExample

end MathlibExtTest.Probability.TruncationSelectedIndexTests
