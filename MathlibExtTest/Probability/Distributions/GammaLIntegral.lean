/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import MathlibExt.Probability.Distributions.GammaLIntegral

/-!
# Tests for the gamma lower integrals

Each helper at the exponential law (shape `1`): the mean `1` via the real-power moment, the
Laplace transform `1/2` at `c = 1`, and `∫₀^∞ e^{-2x} dx = 1/2`.
-/

open MeasureTheory ProbabilityTheory Real

namespace MathlibExtTest.Probability.Distributions.GammaLIntegral

/-- The moment helper at the exponential law: `∫ e^{-y} y dy = 1`. -/
example : ∫⁻ y, gammaPDF 1 1 y * ENNReal.ofReal (y ^ (1 : ℝ)) = 1 := by
  rw [lintegral_gammaPDF_mul_rpow (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Gamma_two]

/-- The Laplace helper at the exponential law: `∫ e^{-y} e^{-y} dy = 1/2`. -/
example : ∫⁻ y, gammaPDF 1 1 y * ENNReal.ofReal (exp (-(1 * y))) = ENNReal.ofReal (1 / 2) := by
  rw [lintegral_gammaPDF_mul_exp (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The `Ioi` helper at `a = 1`, `r = 2`: `∫₀^∞ e^{-2x} dx = 1/2`. -/
example : ∫⁻ x, ENNReal.ofReal (if 0 < x then x ^ ((1 : ℝ) - 1) * exp (-(2 * x)) else 0) =
    ENNReal.ofReal (1 / 2) := by
  rw [lintegral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (by norm_num)]
  norm_num

end MathlibExtTest.Probability.Distributions.GammaLIntegral
