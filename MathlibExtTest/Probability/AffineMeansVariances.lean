/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.AffineMeansVariances
import MathlibExtTest.Probability.Statistics.Measurement.FiniteFixtures
import Mathlib.Tactic.NormNum

/-! # Examples for affine changes of means and variances -/

open MeasureTheory ProbabilityTheory MetaMathlibExt

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

-- Even when a negative slope reverses both differences, their ratio is unchanged.
example :
    ((∫ _ : Ω, (-2 : ℝ) * 1 + 3 ∂μ) - ∫ _ : Ω, (-2 : ℝ) * 2 + 3 ∂μ) /
      ((∫ _ : Ω, (-2 : ℝ) * 4 + 3 ∂μ) - ∫ _ : Ω, (-2 : ℝ) * 1 + 3 ∂μ) = -1 / 3 := by
  have h := div_sub_means_affine (μ := μ) (a := -2) (b := 3)
    (X := fun _ => 1) (Y := fun _ => 2) (U := fun _ => 4) (W := fun _ => 1)
    (integrable_const 1) (integrable_const 2) (integrable_const 4) (integrable_const 1)
    (by norm_num)
  exact h.trans (by norm_num)

-- A zero denominator is allowed in both cancellation laws.
example : (∫ _ : Ω, (-2 : ℝ) * 1 ∂μ) / (∫ _ : Ω, (-2 : ℝ) * 0 ∂μ) = 0 := by
  have h := div_means_const_mul (μ := μ) (X := fun _ => 1) (Y := fun _ => 0)
    (a := -2) (by norm_num)
  exact h.trans (by norm_num)

example :
    ((∫ _ : Ω, (-2 : ℝ) * 1 + 3 ∂μ) - ∫ _ : Ω, (-2 : ℝ) * 2 + 3 ∂μ) /
      ((∫ _ : Ω, (-2 : ℝ) * 4 + 3 ∂μ) - ∫ _ : Ω, (-2 : ℝ) * 4 + 3 ∂μ) = 0 := by
  have h := div_sub_means_affine (μ := μ) (a := -2) (b := 3)
    (X := fun _ => 1) (Y := fun _ => 2) (U := fun _ => 4) (W := fun _ => 4)
    (integrable_const 1) (integrable_const 2) (integrable_const 4) (integrable_const 4)
    (by norm_num)
  exact h.trans (by norm_num)

-- A unit shift of two distinct constants changes the ratio of their means.
example : (∫ _ : Ω, (1 : ℝ) ∂μ) / (∫ _ : Ω, (2 : ℝ) ∂μ) = 1 / 2 ∧
    (∫ _ : Ω, (1 : ℝ) + 1 ∂μ) / (∫ _ : Ω, (2 : ℝ) + 1 ∂μ) = 2 / 3 := by
  norm_num

-- A zero slope still preserves a ratio of one when the new constant is nonzero.
example : (∫ _ : Ω, (0 : ℝ) * 2 + 3 ∂μ) / (∫ _ : Ω, (0 : ℝ) * 2 + 3 ∂μ) = 1 := by
  exact div_means_affine_eq_one (μ := μ) (a := 0) (b := 3) (by norm_num) (by norm_num)

open MathlibExtTest.Probability.Statistics.Measurement.FiniteFixtures in
-- The variance clause of the summary applies to both a negative slope and a constant recoding.
example : variance (fun ω => (-2 : ℝ) * coord 1 0 ω + 3) (μUnif 1) = 4 ∧
    variance (fun ω => (0 : ℝ) * coord 1 0 ω + 3) (μUnif 1) = 0 := by
  have hX : MemLp (coord 1 0) 2 (μUnif 1) := by
    apply MemLp.of_bound (coord_measurable 1 0).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by
      cases h : ω 0 <;> norm_num [coord, h, Real.norm_eq_abs]
  have hneg := (affine_mean_variance_laws (μUnif 1) (-2) 3).2.1 hX
  have hzero := (affine_mean_variance_laws (μUnif 1) 0 3).2.1 hX
  rw [coord_variance] at hneg hzero
  constructor
  · exact hneg.trans (by norm_num)
  · exact hzero.trans (by norm_num)
