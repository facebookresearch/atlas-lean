/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FibonacciPiSquared
import Mathlib.Tactic.Ring

namespace MetaMathlibExt.fibPiSquared_coeff_eq_fib

private noncomputable def coeff : ℕ → ℝ
  | 0 => -(8 * √5) / 250
  | 1 => (25 - 4 * √5) / 250
  | n + 2 => coeff (n + 1) + coeff n

private theorem coeff_step (n : ℕ) (hn : 1 ≤ n) : coeff (n + 1) = coeff n + coeff (n - 1) := by
  cases n with
  | zero => omega
  | succ n => rw [coeff, Nat.succ_sub_one]

example : coeff 1 = (25 - 4 * √5) / 250 := by
  simpa using fibPiSquared_coeff_eq_fib coeff rfl rfl coeff_step 0

example : coeff 4 = (75 - 28 * √5) / 250 := by
  rw [fibPiSquared_coeff_eq_fib coeff rfl rfl coeff_step 3]
  change (25 - 4 * √5) / 250 * 3 - 8 * √5 / 250 * 2 = _
  ring

end MetaMathlibExt.fibPiSquared_coeff_eq_fib
