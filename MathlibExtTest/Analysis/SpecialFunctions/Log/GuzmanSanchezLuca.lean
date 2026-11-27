/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Log.GuzmanSanchezLuca
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum.RealSqrt

/-! # Tests for the Guzmán Sánchez–Luca bound -/

open MetaMathlibExt Real

-- At L = 1 the logarithmic denominator vanishes.
example : 1 < 2 * (5 : ℝ) * log 5 := by
  simpa using lt_two_rpow_mul_mul_log_rpow (r := 1) (H := 5) (L := 1)
    (by norm_num) (by norm_num) (by norm_num)

-- A nonintegral exponent with a positive logarithm and L greater than H.
example : exp 4 < 2 ^ (3 / 2 : ℝ) * 32 * log 32 ^ (3 / 2 : ℝ) := by
  apply lt_two_rpow_mul_mul_log_rpow (by norm_num)
  · norm_num [rpow_div_two_eq_sqrt, rpow_ofNat]
  · rw [log_exp, rpow_div_two_eq_sqrt 3 (by norm_num)]
    rw [div_lt_iff₀ (by positivity)]
    calc
      exp 4 = exp 1 ^ 4 := by rw [← exp_nat_mul]; norm_num
      _ < 3 ^ 4 := by gcongr; exact exp_one_lt_three
      _ < _ := by norm_num [rpow_ofNat]
