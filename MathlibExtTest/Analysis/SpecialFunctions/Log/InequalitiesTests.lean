/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Log.Inequalities

/-!
# Diagnostics for the `log (1 - x)` / `exp (-x)` bounds.
-/

@[expose] public section

#check @Real.log_one_sub_le_neg
#check @Real.neg_add_sq_le_log_one_sub
#check @Real.log_one_sub_bounds
#check @Real.exp_neg_le_one_sub_add_sq

example : -(1 / 4 : ℝ) - (1 / 4) ^ 2 ≤ Real.log (1 - 1 / 4) :=
  Real.neg_add_sq_le_log_one_sub (1 / 4) (by norm_num) (by norm_num)

example : Real.log (1 - (1 / 4 : ℝ)) ≤ -(1 / 4 : ℝ) :=
  Real.log_one_sub_le_neg (1 / 4) (by norm_num)

example : Real.exp (-(1 / 4 : ℝ)) ≤ 1 - 1 / 4 + (1 / 4 : ℝ) ^ 2 :=
  Real.exp_neg_le_one_sub_add_sq (1 / 4) (by norm_num)

#print axioms Real.log_one_sub_le_neg
#print axioms Real.neg_add_sq_le_log_one_sub
#print axioms Real.log_one_sub_bounds
#print axioms Real.exp_neg_le_one_sub_add_sq
