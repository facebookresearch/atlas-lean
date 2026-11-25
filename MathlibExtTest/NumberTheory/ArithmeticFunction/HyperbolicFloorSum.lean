/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.HyperbolicFloorSum
import Mathlib.Analysis.Asymptotics.Arith

open Asymptotics Filter

namespace MetaMathlibExt

-- At both lower endpoints, the weight difference is the ordinary reciprocal difference.
example : Summable fun n : ℕ => |1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)| := by
  have hf : (fun _ : ℕ => (1 : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    simp only [Real.rpow_zero]
    exact isBigO_refl _ _
  simpa using summable_abs_mul_log_pow_div_sub _ 0 le_rfl zero_lt_one hf 0

-- Alternating signs are allowed even for an unbounded function.
example : Summable fun n : ℕ =>
    |(-1 : ℝ) ^ (n + 1) * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) *
      (Real.log (n + 1) / (n + 1) - Real.log (n + 2) / (n + 2))| := by
  have hf : (fun n : ℕ => (-1 : ℝ) ^ n * (n : ℝ) ^ (1 / 2 : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) := by
    apply IsBigO.of_bound'
    exact Filter.Eventually.of_forall fun n => by simp [norm_mul]
  simpa only [Nat.cast_add_one, pow_one] using
    summable_abs_mul_log_pow_div_sub _ (1 / 2) (by norm_num) (by norm_num) hf 1

end MetaMathlibExt
