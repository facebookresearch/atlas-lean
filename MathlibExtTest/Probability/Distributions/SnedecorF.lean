/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import MathlibExt.Probability.Distributions.SnedecorF

/-!
# Tests for Snedecor's `F` law

Total mass `1` at `(1, 1)` and `(2, 3)`, no mass on `(-∞, 0]` (the density vanishes off
`Ioi 0`), the closed form `(1 + x)^{-2}` of the `F(2, 2)` density, and the beta and gamma
integral helpers at their simplest parameters.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace MathlibExtTest.Probability.Distributions.SnedecorF

/-- `F(1, 1)` has total mass `1`. -/
example : snedecorFMeasure 1 1 univ = 1 := by
  have := isProbabilityMeasure_snedecorFMeasure (d₁ := 1) (d₂ := 1) one_pos one_pos
  exact measure_univ

/-- `F(2, 3)` is a probability measure. -/
example : IsProbabilityMeasure (snedecorFMeasure 2 3) :=
  isProbabilityMeasure_snedecorFMeasure (by norm_num) (by norm_num)

/-- The density vanishes off `Ioi 0`, so `(-∞, 0]` is null for every `(d₁, d₂)`. -/
example (d₁ d₂ : ℕ) : snedecorFMeasure d₁ d₂ (Iic 0) = 0 := by
  rw [snedecorFMeasure, withDensity_apply _ measurableSet_Iic]
  rw [setLIntegral_congr_fun measurableSet_Iic (g := fun _ => 0)
    (fun x (hx : x ≤ 0) => by simp [not_lt.mpr hx])]
  simp

/-- At `(d₁, d₂) = (2, 2)` the density formula reduces to `(1 + x)^{-2}`. -/
example (x : ℝ) :
    Gamma (((2 : ℕ) + (2 : ℕ)) / 2) / (Gamma ((2 : ℕ) / 2) * Gamma ((2 : ℕ) / 2)) *
        (((2 : ℕ) : ℝ) / (2 : ℕ)) ^ (((2 : ℕ) : ℝ) / 2) * x ^ (((2 : ℕ) : ℝ) / 2 - 1) *
          (1 + (2 : ℕ) * x / (2 : ℕ)) ^ (-(((2 : ℕ) : ℝ) + (2 : ℕ)) / 2) =
      (1 + x) ^ (-2 : ℝ) := by
  norm_num [Gamma_two]

/-- The beta helper at `a = b = c = 1`: `∫₀^∞ (1 + x)^{-2} dx = 1`. -/
example : ∫⁻ x, ENNReal.ofReal (if 0 < x then x ^ ((1 : ℝ) - 1) * (1 + 1 * x) ^ (-(1 + 1 : ℝ))
    else 0) = 1 := by
  rw [lintegral_rpow_mul_one_add_mul_rpow_neg (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Gamma_two]

/-- The gamma helper at `a = 1`, `r = 2`: `∫₀^∞ e^{-2x} dx = 1/2`. -/
example : ∫⁻ x, ENNReal.ofReal (if 0 < x then x ^ ((1 : ℝ) - 1) * exp (-(2 * x)) else 0) =
    ENNReal.ofReal (1 / 2) := by
  rw [lintegral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (by norm_num)]
  norm_num

end MathlibExtTest.Probability.Distributions.SnedecorF
