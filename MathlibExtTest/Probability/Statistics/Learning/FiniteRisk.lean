/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Learning.FiniteRisk

@[expose] public section

open MeasureTheory

namespace MathlibExtTest.FiniteRisk
open ProbabilityTheory

-- M = 1 holdout
example {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (g : Z → ℝ) (hg : Measurable g)
    (hbd : ∀ᵐ z ∂μ, g z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => μ).real
        {S : Fin n → Z | ∃ _j : Fin 1,
          ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - ∫ z, g z ∂μ|} ≤
      2 * ((1 : ℕ) : ℝ) * Real.exp (-2 * (n : ℝ) * ε ^ 2) :=
  measure_exists_abs_empirical_sub_integral_ge_le μ hn (fun _ => g) (fun _ => hg)
    (fun _ => hbd) hε

-- duplicate candidates
example {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (g : Z → ℝ) (hg : Measurable g)
    (hbd : ∀ᵐ z ∂μ, g z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => μ).real
        {S : Fin n → Z | ∃ _j : Fin 2,
          ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - ∫ z, g z ∂μ|} ≤
      2 * ((2 : ℕ) : ℝ) * Real.exp (-2 * (n : ℝ) * ε ^ 2) :=
  measure_exists_abs_empirical_sub_integral_ge_le μ hn (fun _ => g) (fun _ => hg)
    (fun _ => hbd) hε

-- 0-1 loss of measurable error sets
example {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {M n : ℕ} (hn : 0 < n) (s : Fin M → Set Z) (hs : ∀ j, MeasurableSet (s j))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => μ).real
        {S : Fin n → Z | ∃ j : Fin M,
          ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, (s j).indicator (1 : Z → ℝ) (S i) -
            ∫ z, (s j).indicator (1 : Z → ℝ) z ∂μ|} ≤
      2 * (M : ℝ) * Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  refine measure_exists_abs_empirical_sub_integral_ge_le μ hn
    (fun j => (s j).indicator (1 : Z → ℝ)) (fun j => measurable_one.indicator (hs j))
    (fun j => Filter.Eventually.of_forall fun z => ?_) hε
  by_cases h : z ∈ s j <;> simp [h]

-- clipped squared loss
example {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {M n : ℕ} (hn : 0 < n) (g : Fin M → Z → ℝ) (hg : ∀ j, Measurable (g j))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => μ).real
        {S : Fin n → Z | ∃ j : Fin M,
          ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, min 1 (g j (S i) ^ 2) -
            ∫ z, min 1 (g j z ^ 2) ∂μ|} ≤
      2 * (M : ℝ) * Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  exact measure_exists_abs_empirical_sub_integral_ge_le μ hn
    (fun j z => min 1 (g j z ^ 2)) (fun j => measurable_const.min ((hg j).pow_const 2))
    (fun _ => Filter.Eventually.of_forall fun _ =>
      ⟨le_min zero_le_one (sq_nonneg _), min_le_left _ _⟩) hε

-- zero loss: the deviation event is empty for ε > 0
example {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {M n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    {S : Fin n → Z | ∃ _j : Fin M,
      ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, (fun _ : Z => (0 : ℝ)) (S i) -
        ∫ z, (fun _ : Z => (0 : ℝ)) z ∂μ|} = ∅ := by
  ext S
  simp [not_le.mpr hε]

-- non-vacuity: M = 2, n = 100, ε = 1/5 gives a bound below 1
example : 2 * ((2 : ℕ) : ℝ) * Real.exp (-2 * ((100 : ℕ) : ℝ) * (1 / 5 : ℝ) ^ 2) < 1 := by
  have h8 : (8 : ℝ) + 1 ≤ Real.exp 8 := Real.add_one_le_exp 8
  rw [show -2 * ((100 : ℕ) : ℝ) * (1 / 5 : ℝ) ^ 2 = -8 by norm_num, Real.exp_neg]
  rw [← div_eq_mul_inv, div_lt_one (Real.exp_pos 8)]
  norm_num
  linarith

-- boundedness premise is essential: a constant loss 2 cannot discharge it
example {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ] :
    ¬ ∀ᵐ z ∂μ, (fun _ : Z => (2 : ℝ)) z ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num
  exact IsProbabilityMeasure.ne_zero μ

end MathlibExtTest.FiniteRisk
