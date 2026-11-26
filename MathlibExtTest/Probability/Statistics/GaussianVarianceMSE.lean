/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.GaussianVarianceMSE
import Mathlib.Tactic.NormNum

/-! # Gaussian variance estimator risks at the smallest sample size and at nonunit variance -/

open MeasureTheory ProbabilityTheory

-- With two standard-normal observations, the two risks are 2 and 3/4.
example :
    let P := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let Q := fun x : Fin 2 → ℝ => ∑ i, (x i - (∑ j, x j) / 2) ^ 2
    (∫ x, Q x / ((2 : ℝ) - 1) ∂P) = 1 ∧
      (∫ x, (Q x / ((2 : ℝ) - 1) - 1) ^ 2 ∂P) = 2 ∧
      (∫ x, (Q x / 2 - 1) ^ 2 ∂P) = 3 / 4 := by
  have h := gaussian_variance_estimators_mse (n := 2) (by decide) 0 (v := 1) (by norm_num)
  refine ⟨h.2.2.1, ?_, ?_⟩
  · have hm := h.2.2.2.2.1
    norm_num at hm ⊢
    exact hm
  · have hm := h.2.2.2.2.2.1
    norm_num at hm ⊢
    exact hm

-- A nonzero sample mean parameter and variance two do not change the risk formulas' form.
example :
    let P := Measure.pi fun _ : Fin 5 => gaussianReal 4 2
    let Q := fun x : Fin 5 → ℝ => ∑ i, (x i - (∑ j, x j) / 5) ^ 2
    (∫ x, Q x / 5 ∂P) - 2 = -(2 : ℝ) / 5 ∧
      (∫ x, (Q x / 5 - 2) ^ 2 ∂P) = 36 / 25 ∧
      (∫ x, (Q x / 5 - 2) ^ 2 ∂P) < ∫ x, (Q x / ((5 : ℝ) - 1) - 2) ^ 2 ∂P := by
  have h := gaussian_variance_estimators_mse (n := 5) (by decide) 4 (v := 2) (by norm_num)
  refine ⟨h.2.2.2.1, ?_, h.2.2.2.2.2.2⟩
  have hm := h.2.2.2.2.2.1
  norm_num at hm ⊢
  exact hm
