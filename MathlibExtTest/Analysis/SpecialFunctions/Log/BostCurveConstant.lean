/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Log.BostCurveConstant

open Real Javanpeykar

/-! Checks and concrete instances of the comparison of Bost's constants. -/

#check @half_mul_log_two_mul_pi_sq
#check @neg_mul_log_two_mul_pi_le_neg_half_mul_log_two_mul_pi_sq

/-- At genus `g = 1`. -/
example : -1 * Real.log (2 * π) ≤ -(1 / 2) * Real.log (2 * π ^ 2) :=
  neg_mul_log_two_mul_pi_le_neg_half_mul_log_two_mul_pi_sq zero_le_one

/-- At genus `g = 2`: `log(2π²) = 2 log(√2 π)`. -/
example : 2 / 2 * Real.log (2 * π ^ 2) = 2 * Real.log (Real.sqrt 2 * π) :=
  half_mul_log_two_mul_pi_sq 2

#print axioms half_mul_log_two_mul_pi_sq
#print axioms neg_mul_log_two_mul_pi_le_neg_half_mul_log_two_mul_pi_sq
