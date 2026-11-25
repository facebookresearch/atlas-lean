/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Signals.Examples
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open ControlTheory

-- The squaring witnesses numerically: with `x = y = 1`, the two sides
-- of the purported additivity identity are `4` and `2` at `t = 0`.
example : ((fun t => ((1 : ℤ → ℝ) t + (1 : ℤ → ℝ) t) ^ 2) 0)
    ≠ ((fun t => ((1 : ℤ → ℝ) t) ^ 2 + ((1 : ℤ → ℝ) t) ^ 2) 0) := by
  norm_num

-- Multiplication by time at explicit points, both time domains.
example : timeMul (fun _ => 1) 3 = 3 := by simp
example : timeMulInt (fun _ => 1) 3 = 3 := by simp

-- The two compositions on the constant signal `1`: `t` versus `t - 1`,
-- separating at `t = 1` and already different at `t = 0`.
example : (timeMul.comp (shiftₗ ℝ ℝ (1 : ℝ))) 1 1 = 1 := by
  simp [timeMul_apply]
example : ((shiftₗ ℝ ℝ (1 : ℝ)).comp timeMul) 1 1 = 0 := by
  simp [timeMul_apply]
example : (timeMul.comp (shiftₗ ℝ ℝ (1 : ℝ))) 1 0 = 0 := by
  simp [timeMul_apply]
example : ((shiftₗ ℝ ℝ (1 : ℝ)).comp timeMul) 1 0 = -1 := by
  simp [timeMul_apply]

-- The advance reads the impulse at time `1` already at time `0`, both
-- domains; the delay does not.
example : (shiftₗ ℝ ℝ (-1 : ℤ)) (fun n => if n = 1 then (1 : ℝ) else 0) 0
    = 1 := by
  show (fun n => if n = 1 then (1 : ℝ) else 0) (0 - -1) = 1
  norm_num
example : (shiftₗ ℝ ℝ (-1 : ℝ)) (fun t => if t = 1 then (1 : ℝ) else 0) 0
    = 1 := by
  show (fun t => if t = 1 then (1 : ℝ) else 0) (0 - -1) = 1
  norm_num
example : (shiftₗ ℝ ℝ (1 : ℤ)) (fun n => if n = 1 then (1 : ℝ) else 0) 0
    = 0 := by
  show (fun n => if n = 1 then (1 : ℝ) else 0) (0 - 1) = 0
  norm_num

#print axioms timeMul_apply
#print axioms timeMulInt_apply
#print axioms sq_not_additive_int
#print axioms sq_not_additive_real
#print axioms not_isTimeInvariant_timeMul
#print axioms not_isTimeInvariant_timeMulInt
#print axioms not_isCausal_shift_neg_one_int
#print axioms not_isCausal_shift_neg_one_real
