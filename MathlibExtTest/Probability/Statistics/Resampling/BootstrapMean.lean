/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.Resampling.BootstrapMean

/-! # Tests for `MathlibExt.Probability.Statistics.Resampling.BootstrapMean` -/

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.BootstrapMean

def testSample : ℕ → ℝ := fun i => if i = 0 then 3 else if i = 1 then 1 else if i = 2 then 4 else if i = 3 then 1 else if i = 4 then 5 else 0

theorem testSample_mean : empiricalMean testSample 5 = 14 / 5 := by
  have h0 : testSample 0 = 3 := rfl
  have h1 : testSample 1 = 1 := rfl
  have h2 : testSample 2 = 4 := rfl
  have h3 : testSample 3 = 1 := rfl
  have h4 : testSample 4 = 5 := rfl
  rw [empiricalMean_eq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4]
  norm_num

theorem testSample_bootstrapMean :
    ∫ y, (5 : ℝ)⁻¹ * ∑ k : Fin 5, y k ∂(Measure.pi fun _ : Fin 5 => empiricalLaw testSample 5) = 14 / 5 := by
  have h5 : (0 : ℕ) < 5 := by norm_num
  have h := integral_bootstrapMean (x := testSample) (n := 5) h5
  have hcast : ((5 : ℕ) : ℝ) = (5 : ℝ) := by norm_num
  rw [hcast] at h
  rw [h]
  exact testSample_mean

end MathlibExtTest.BootstrapMean
