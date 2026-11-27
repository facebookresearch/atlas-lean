/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FareyStaircaseFareyStaircaseSubMemIcc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for bounds on the increment of the Farey staircase -/

open MetaMathlibExt

namespace MathlibExtTest.NumberTheory.FareyStaircaseFareyStaircaseSubMemIcc

-- At order two the increment is nonnegative.
example (x : ℝ) : 0 ≤ fareyStaircase 2 x - fareyStaircase 1 x :=
  (fareyStaircase_sub_mem_Icc (by decide : 2 ≤ 2) x).1

-- The Farey staircase grows from order one to order two.
example (x : ℝ) : fareyStaircase 1 x ≤ fareyStaircase 2 x := by
  have h := (fareyStaircase_sub_mem_Icc (by decide : 2 ≤ 2) x).1
  linarith

-- At order two the increment is at most `(log 2) / 2`.
example (x : ℝ) : fareyStaircase 2 x - fareyStaircase 1 x ≤ Real.log 2 / 2 := by
  have h := (fareyStaircase_sub_mem_Icc (by decide : 2 ≤ 2) x).2
  have heq : Real.log 2 / (2 * (2 - 1)) = Real.log 2 / 2 := by
    norm_num
  simpa [heq] using h

end MathlibExtTest.NumberTheory.FareyStaircaseFareyStaircaseSubMemIcc
