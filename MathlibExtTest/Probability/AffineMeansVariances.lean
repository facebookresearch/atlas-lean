/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.AffineMeansVariances
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
    (by norm_num) (by norm_num)
  exact h.trans (by norm_num)

-- A unit shift of two distinct constants changes the ratio of their means.
example : (∫ _ : Ω, (1 : ℝ) ∂μ) / (∫ _ : Ω, (2 : ℝ) ∂μ) = 1 / 2 ∧
    (∫ _ : Ω, (1 : ℝ) + 1 ∂μ) / (∫ _ : Ω, (2 : ℝ) + 1 ∂μ) = 2 / 3 := by
  norm_num

-- A zero slope still preserves a ratio of one when the new constant is nonzero.
example : (∫ _ : Ω, (0 : ℝ) * 2 + 3 ∂μ) / (∫ _ : Ω, (0 : ℝ) * 2 + 3 ∂μ) = 1 := by
  exact div_means_affine_eq_one (μ := μ) (a := 0) (b := 3)
    (integrable_const 2) (integrable_const 2) (by norm_num) (by norm_num) (by norm_num)
