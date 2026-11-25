/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.SheppardArcsine

@[expose] public section

open Real MeasureTheory ProbabilityTheory MathlibExt.Probability.Distributions.SheppardArcsine

namespace MathlibExtTest.Probability.Distributions.SheppardArcsine

/-- Uncorrelated case: the quadrant has probability `1/4`. -/
example : (multivariateGaussian 0
      (Matrix.of fun i j : Fin 2 => if i = j then (1 : ℝ) else 0)).real
    {x | 0 < x 0 ∧ 0 < x 1} = 1 / 4 := by
  have h := sheppard_quadrant_probability_arcsine 0 ⟨by norm_num, by norm_num⟩
  simp only [arcsin_zero, zero_div, add_zero] at h
  exact h

/-- Correlation `1/2`: the quadrant has probability `1/3` (`arcsin (1/2) = π/6`). -/
example : (multivariateGaussian 0
      (Matrix.of fun i j : Fin 2 => if i = j then (1 : ℝ) else 1 / 2)).real
    {x | 0 < x 0 ∧ 0 < x 1} = 1 / 3 := by
  have h := sheppard_quadrant_probability_arcsine (1 / 2) ⟨by norm_num, by norm_num⟩
  simp only at h
  rw [h, show (1 / 2 : ℝ) = sin (π / 6) by rw [sin_pi_div_six],
    arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]
  field_simp
  ring

end MathlibExtTest.Probability.Distributions.SheppardArcsine
