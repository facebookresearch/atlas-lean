/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.WeightedChiSquare

/-! # Tests for `MathlibExt.Analysis.WeightedChiSquare`

Boundary: all weights `0` (the law is `δ₀`, so `φ ≡ 1`, checked both through the moved formula and
through `weightedChiSq_zero`) and `t = 0`. Non-vacuity: for `χ²₁` the formula gives
`‖φ(1)‖ = 5^{-1/4} < 1`, so the law is not a point mass at `0`. -/

open MeasureTheory ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.BurdenSKAT
open MathlibExt.Analysis.WeightedChiSquare Complex

namespace MathlibExtTest.WeightedChiSquare

/-- All weights zero, through the moved formula: `∏ⱼ 1^{-1/2} = 1`. -/
example (t : ℝ) : charFun (weightedChiSq (0 : Fin 3 → ℝ)) t = 1 := by
  rw [charFun_weightedChiSq]
  simp

/-- The same value from the definition side: `weightedChiSq 0 = δ₀`. -/
example (t : ℝ) : charFun (weightedChiSq (0 : Fin 3 → ℝ)) t = 1 := by
  rw [weightedChiSq_zero]
  simp

/-- At `t = 0` every characteristic function is `1`. -/
example (lam : Fin 2 → ℝ) : charFun (weightedChiSq lam) 0 = 1 := by
  rw [charFun_weightedChiSq]
  simp

/-- One term with `c = 0`: `δ₀`, value `1`. -/
example (t : ℝ) : charFun ((gaussianReal 0 1).map fun x => (0 : ℝ) * x ^ 2) t = 1 := by
  rw [charFun_map_mul_sq_gaussianReal]
  simp

/-- `χ²₁` at `t = 1`: `φ(1) = (1 - 2 i)^{-1/2}`. -/
example : charFun (weightedChiSq fun _ : Fin 1 => (1 : ℝ)) 1 = (1 - 2 * I) ^ (-(1 / 2) : ℂ) := by
  rw [charFun_weightedChiSq]
  simp

/-- Non-vacuity: `‖φ_{χ²₁}(1)‖ = ‖1 - 2 i‖^{-1/2} < 1`. -/
example : ‖charFun (weightedChiSq fun _ : Fin 1 => (1 : ℝ)) 1‖ < 1 := by
  rw [charFun_weightedChiSq]
  simp only [Finset.univ_unique, Finset.prod_singleton, mul_one, ofReal_one]
  have he : (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [he, norm_cpow_real]
  have h1 : 1 < ‖(1 : ℂ) - 2 * I‖ := by
    have h := abs_im_le_norm ((1 : ℂ) - 2 * I)
    simp at h
    linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num)

end MathlibExtTest.WeightedChiSquare
