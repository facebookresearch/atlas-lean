/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Signals.DiscreteConv
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

open ControlTheory

/-- A two-tap kernel `1, 2, 0, 0, …` for the examples. -/
def twoTap : ℕ → ℝ := fun n => if n = 0 then 1 else if n = 1 then 2 else 0

/-- The ramp `0, 1, 2, …` for the examples. -/
def rampSeq : ℕ → ℝ := fun n => n

-- Two-tap kernel on the ramp: `n + 2(n - 1)` for `n ≥ 1`, `0` at `0`.
example : causalConv twoTap rampSeq 0 = 0 := by
  norm_num [causalConv_apply, twoTap, rampSeq, Finset.sum_range_succ]
example : causalConv twoTap rampSeq 1 = 1 := by
  norm_num [causalConv_apply, twoTap, rampSeq, Finset.sum_range_succ]
example : causalConv twoTap rampSeq 2 = 4 := by
  norm_num [causalConv_apply, twoTap, rampSeq, Finset.sum_range_succ]
example : causalConv twoTap rampSeq 4 = 10 := by
  norm_num [causalConv_apply, twoTap, rampSeq, Finset.sum_range_succ]

-- Boundary at `n = 0`, for arbitrary sequences.
example (f g : ℕ → ℝ) : causalConv f g 0 = f 0 * g 0 := by
  simp [causalConv_apply]

-- Zero kernel on both sides.
example (g : ℕ → ℝ) : causalConv 0 g 3 = 0 := by simp
example (f : ℕ → ℝ) : causalConv f 0 3 = 0 := by simp

-- The delay kernel `Pi.single 2 1` shifts by two: output at `5` reads
-- the input at `3`.
example (g : ℕ → ℝ) : causalConv (Pi.single 2 1) g 5 = g 3 := by
  norm_num [causalConv_apply, Finset.sum_range_succ, Pi.single_apply]

-- Unit sample on both sides at explicit points.
example (f : ℕ → ℝ) : causalConv (Pi.single 0 1) f 2 = f 2 := by
  rw [single_zero_causalConv]
example (f : ℕ → ℝ) : causalConv f (Pi.single 0 1) 2 = f 2 := by
  rw [causalConv_single_zero]

#print axioms causalConv_apply
#print axioms causalConv_eq_addRingConvolution
#print axioms zero_causalConv
#print axioms causalConv_zero
#print axioms single_zero_causalConv
#print axioms causalConv_single_zero
#print axioms causalConv_comm
#print axioms causalConv_assoc
