/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Trigonometric.ExpIMulTaylor

set_option autoImplicit false

open Complex

-- The `|x| ≤ 1` and `1 ≤ |x|` regimes, and the textbook form with `α = 1/2`.
example : ‖exp ((1 / 2 : ℝ) * I) - 1 - (1 / 2 : ℝ) * I - ((1 / 2 : ℝ) * I) ^ 2 / 2‖ ≤ |(1 / 2 : ℝ)| ^ 3 :=
  norm_exp_ofReal_mul_I_sub_taylor_two_le_pow_three (by norm_num [abs_of_pos])

example : ‖exp ((3 : ℝ) * I) - 1 - (3 : ℝ) * I - ((3 : ℝ) * I) ^ 2 / 2‖ ≤ 4 * |(3 : ℝ)| ^ 2 :=
  norm_exp_ofReal_mul_I_sub_taylor_two_le_four_mul_sq (by norm_num)

example (x : ℝ) : ‖exp (x * I) - 1 - x * I - (x * I) ^ 2 / 2‖ ≤ 4 * |x| ^ (2 + (1 / 2 : ℝ)) :=
  norm_exp_ofReal_mul_I_sub_taylor_two_le_rpow x (by norm_num) (by norm_num)
