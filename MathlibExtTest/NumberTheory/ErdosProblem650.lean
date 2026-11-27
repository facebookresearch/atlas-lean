/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosProblem650
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt

/-! # Tests for Erdős's matching function -/

open MathlibExt.NumberTheory.ErdosProblem650Wanted

example : f 0 = 0 := by simp [conjecture_holds.1]

-- The size of the input set is the active bound for two elements.
example : f 2 = 2 := by
  rw [conjecture_holds.1, min_eq_left]
  apply (Nat.lt_ceil.mpr _).le
  have := Real.one_lt_sqrt_two
  norm_num at *
  linarith

-- Six elements are the first case where a full matching is not guaranteed.
example : f 6 = 5 := by
  have hc : ⌈2 * Real.sqrt 6⌉₊ = 5 := by
    apply (Nat.ceil_eq_iff (by decide)).mpr
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
    constructor <;> norm_num <;> nlinarith [Real.sqrt_nonneg 6]
  rw [conjecture_holds.1]
  norm_num [hc]
