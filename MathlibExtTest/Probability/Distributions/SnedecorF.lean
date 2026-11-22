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

Total mass `1` at `(1, 1)` and `(2, 3)`, the zero measure when either degree of freedom is `0`,
no mass on `(-∞, 0]` (the density vanishes off `Ioi 0`), the closed form `(1 + x)^{-2}` of the
`F(2, 2)` density, the beta integral helper at its simplest parameters, and the ratio law: it
applies to the coordinates of a product of two chi-square laws, and a zero degree of freedom
makes the target the zero measure.
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

/-- Zero numerator degrees of freedom: `Γ(0) = 0` in the denominator, so `F(0, d) = 0`. -/
example (d : ℕ) : snedecorFMeasure 0 d = 0 := by
  simp [snedecorFMeasure]

/-- Zero denominator degrees of freedom: `Γ(0) = 0` in the denominator, so `F(d, 0) = 0`. -/
example (d : ℕ) : snedecorFMeasure d 0 = 0 := by
  simp [snedecorFMeasure]

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

/-! ### The ratio law -/

/-- Non-vacuity: the hypotheses are satisfiable. Coordinates of a product of two chi-square laws
are independent with the right marginals, so the theorem applies to them. -/
example : ((chiSquareMeasure 2).prod (chiSquareMeasure 3)).map
    (fun p : ℝ × ℝ => (p.1 / (2 : ℕ)) / (p.2 / (3 : ℕ))) = snedecorFMeasure 2 3 := by
  have := isProbabilityMeasure_chiSquareMeasure (by norm_num : 0 < 2)
  have := isProbabilityMeasure_chiSquareMeasure (by norm_num : 0 < 3)
  exact map_div_chiSquare_eq_snedecorF (by norm_num) (by norm_num)
    ⟨measurable_fst.aemeasurable, by rw [Measure.map_fst_prod]; simp⟩
    ⟨measurable_snd.aemeasurable, by rw [Measure.map_snd_prod]; simp⟩
    (indepFun_prod measurable_id measurable_id)

/-- Boundary: with `d₁ = 0` the target is the zero measure, so `0 < d₁` cannot be dropped. -/
example (d : ℕ) : ¬ IsProbabilityMeasure (snedecorFMeasure 0 d) := by
  intro h
  apply IsProbabilityMeasure.ne_zero (snedecorFMeasure 0 d)
  simp [snedecorFMeasure]

/-- Boundary: with `d₂ = 0` the target is the zero measure, so `0 < d₂` cannot be dropped. -/
example (d : ℕ) : ¬ IsProbabilityMeasure (snedecorFMeasure d 0) := by
  intro h
  apply IsProbabilityMeasure.ne_zero (snedecorFMeasure d 0)
  simp [snedecorFMeasure]

end MathlibExtTest.Probability.Distributions.SnedecorF
