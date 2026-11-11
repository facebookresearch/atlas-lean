/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import MathlibExt.Probability.Distributions.StudentT

/-!
# Tests for Student's `t` law

Total mass `1` at `k = 1` and `k = 5`, the density at `0`, the Cauchy density at `k = 1`, the
degenerate `k = 0` case (zero measure), and the gamma moment and Laplace transform helpers at
the exponential law.
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

/-- The gamma moment helper at the exponential law: `∫ e^{-y} y dy = 1`. -/
example : ∫⁻ y, gammaPDF 1 1 y * ENNReal.ofReal (y ^ (1 : ℝ)) = 1 := by
  rw [lintegral_gammaPDF_mul_rpow (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Gamma_two]

/-- The Laplace helper at the exponential law: `∫ e^{-y} e^{-y} dy = 1/2`. -/
example : ∫⁻ y, gammaPDF 1 1 y * ENNReal.ofReal (exp (-(1 * y))) = ENNReal.ofReal (1 / 2) := by
  rw [lintegral_gammaPDF_mul_exp (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end MathlibExtTest.Probability.Distributions.StudentT
