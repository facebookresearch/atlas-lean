/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WeightedSineSum

namespace MetaMathlibExt

-- The weighted sum has one nonzero term, attaining the pointwise bound for the sine.
example : (1 : ℝ) <
    2 / Real.pi * (Real.eulerMascheroniConstant + Real.log 2) + 5 / Real.pi := by
  simpa [Real.sin_pi_div_two] using (sum_abs_sin_mul_div_lt 1 le_rfl (Real.pi / 2)).2

-- The modulus need not be prime, and the single ratio here is exactly one.
example : (1 : ℝ) <
    2 * 4 / Real.pi ^ 2 * (Real.eulerMascheroniConstant + Real.log 2) +
      4 / Real.pi * (1 / 3) + 5 * 4 / Real.pi ^ 2 := by
  have h := sum_abs_sin_div_abs_sin_lt 4 1 1 le_rfl (by decide) le_rfl
  have hs : Real.sin (Real.pi / 4) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
  simpa [hs, show (4 : ℝ) - 1 = 3 by norm_num] using h

-- A zero numerator is allowed; no strict termwise comparison is needed.
example : (0 : ℝ) <
    2 * 2 / Real.pi ^ 2 * (Real.eulerMascheroniConstant + Real.log 2) +
      2 / Real.pi + 5 * 2 / Real.pi ^ 2 := by
  have h := sum_abs_sin_div_abs_sin_lt 2 1 2 le_rfl (by decide) (by decide)
  have he : Real.pi * 2 / 2 = Real.pi := by ring
  simpa [he, show (2 : ℝ) - 1 = 1 by norm_num] using h

end MetaMathlibExt
