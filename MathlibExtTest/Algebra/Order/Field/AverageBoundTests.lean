/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Order.Field.AverageBound
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt

/-- Two machines, total work `10`, a final job of length `4`: makespan at most `9`. -/
example (M : ℝ) (h : 2 * (M - 4) ≤ 10) : M ≤ 10 / 2 + 4 :=
  le_div_add_of_mul_sub_le 2 M 4 10 (by norm_num) h

/-- The equality case `2 * (9 - 4) = 10` is allowed and gives the tight bound `9 ≤ 9`. -/
example : (9 : ℝ) ≤ 10 / 2 + 4 :=
  le_div_add_of_mul_sub_le 2 9 4 10 (by norm_num) (by norm_num)

/-- Zero work: with `M = p = T = 0` the hypothesis `1 * (0 - 0) ≤ 0` holds with equality. -/
example : (0 : ℝ) ≤ 0 / 1 + 0 :=
  le_div_add_of_mul_sub_le 1 0 0 0 one_pos (by norm_num)

/-- The same numbers give the `2 * B` form at `B = 5`. -/
example (M : ℝ) (h : 2 * (M - 4) ≤ 10) : M ≤ 2 * 5 :=
  le_two_mul_of_mul_sub_le 2 M 4 10 5 (by norm_num) h (by norm_num) (by norm_num)

/-- The lemmas hold in any linearly ordered field, here `ℚ`. -/
example (M : ℚ) (h : 3 * (M - 1) ≤ 6) : M ≤ 2 * 2 :=
  le_two_mul_of_mul_sub_le 3 M 1 6 2 (by norm_num) h (by norm_num) (by norm_num)

end
