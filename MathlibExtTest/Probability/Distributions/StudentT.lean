/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import MathlibExt.Probability.Distributions.StudentT

/-!
# Tests for Student's `t` law

Total mass `1` at `k = 1` and `k = 5`, the density at `0`, the Cauchy density at `k = 1`, the
degenerate `k = 0` case (zero measure), and the ratio law instantiated on the product space
`N(0, 1) ⊗ χ²₃` (non-vacuity of its hypotheses).
-/

open MeasureTheory ProbabilityTheory Real

namespace MathlibExtTest.Probability.Distributions.StudentT

/-- `t₁` has total mass `1`. -/
example : studentTMeasure 1 Set.univ = 1 := by
  have := isProbabilityMeasure_studentTMeasure (k := 1) one_pos
  exact measure_univ

/-- `t₅` is a probability measure. -/
example : IsProbabilityMeasure (studentTMeasure 5) :=
  isProbabilityMeasure_studentTMeasure (by norm_num)

/-- The density at `t = 0` is the normalizing constant `Γ((k+1)/2) / (√(k π) Γ(k/2))`. -/
example (k : ℕ) :
    Gamma ((k + 1) / 2) / (√(k * π) * Gamma (k / 2)) *
        (1 + (0 : ℝ) ^ 2 / k) ^ (-((k : ℝ) + 1) / 2) =
      Gamma ((k + 1) / 2) / (√(k * π) * Gamma (k / 2)) := by
  simp

/-- At `k = 1` the density is the Cauchy density `1 / (π (1 + t²))`. -/
example (t : ℝ) :
    Gamma (((1 : ℕ) + 1) / 2) / (√((1 : ℕ) * π) * Gamma ((1 : ℕ) / 2)) *
        (1 + t ^ 2 / (1 : ℕ)) ^ (-(((1 : ℕ) : ℝ) + 1) / 2) =
      1 / (π * (1 + t ^ 2)) := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  norm_num [Gamma_one_half_eq, rpow_neg_one]
  rw [← mul_inv, mul_self_sqrt pi_pos.le, mul_comm]

/-- At `k = 0` the normalizing constant vanishes, so `studentTMeasure 0 = 0`. -/
example : studentTMeasure 0 = 0 := by
  simp [studentTMeasure]

/-- The ratio law on the canonical product space: with `Z = fst`, `V = snd` under
`N(0, 1) ⊗ χ²₃`, the hypotheses hold and `Z / √(V / 3) ~ t₃`. -/
example : ((gaussianReal 0 1).prod (chiSquareMeasure 3)).map
      (fun ω : ℝ × ℝ => ω.1 / √(ω.2 / ((3 : ℕ) : ℝ))) = studentTMeasure 3 := by
  have := isProbabilityMeasure_chiSquareMeasure (p := 3) (by norm_num)
  exact map_div_sqrt_chiSquare_eq_studentT (by norm_num)
    ⟨by fun_prop, by simp [Measure.map_fst_prod]⟩ ⟨by fun_prop, by simp [Measure.map_snd_prod]⟩
    (indepFun_prod (X := id) (Y := id) measurable_id measurable_id)

end MathlibExtTest.Probability.Distributions.StudentT
