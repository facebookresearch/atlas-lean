/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.DerangementSumRule

/-! # Boundary and parity tests for the derangement sum rule -/

open MetaMathlibExt

example : ⌊((0 + 1 : ℕ).factorial : ℝ) / Real.exp 1⌋ = 0 := by
  rw [← sum_mul_numDerangements_eq_floor 0]
  decide

example : ⌊((1 + 1 : ℕ).factorial : ℝ) / Real.exp 1⌋ = 0 := by
  rw [← sum_mul_numDerangements_eq_floor 1]
  decide

example : ⌊((2 + 1 : ℕ).factorial : ℝ) / Real.exp 1⌋ = 2 := by
  rw [← sum_mul_numDerangements_eq_floor 2]
  decide

example : ⌊((3 + 1 : ℕ).factorial : ℝ) / Real.exp 1⌋ = 8 := by
  rw [← sum_mul_numDerangements_eq_floor 3]
  decide
