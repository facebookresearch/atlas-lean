/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Process.BatchReactor


/-!
# Tests for batch first-order consumption

Interior, boundary and assumption-necessity checks.
-/

namespace Engineering.Process.BatchReactor.Tests

open Engineering.Process.BatchReactor

-- Interior witness: k = c0 = t = 1 leaves a positive amount and the
-- consumption is strictly below the initial concentration.
example : 0 < (2 : ℝ) * Real.exp (-1 : ℝ) ∧ (2 : ℝ) * Real.exp (-1 : ℝ) < 2 := by
  have hexp : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  constructor
  · exact mul_pos (by norm_num) (Real.exp_pos _)
  · have h : (2 : ℝ) * Real.exp (-1 : ℝ) < 2 * 1 :=
      mul_lt_mul_of_pos_left hexp (by norm_num)
    linarith

example : consumed 1 2 1 ∈ Set.Icc (0 : ℝ) 2 ∧ 0 < consumed 1 2 1 := by
  exact ⟨firstOrder_consumed_mem_Icc zero_le_one zero_le_two zero_le_one,
    consumed_pos one_pos two_pos one_pos⟩

-- Boundary cases.
example : consumed 0 2 1 = 0 := by exact consumed_of_k_eq_zero _ _

example : consumed 1 0 1 = 0 := by exact consumed_of_c0_eq_zero _ _

-- Assumption necessity: a negative rate constant produces growth, so the
-- "consumed" quantity is negative and the bound cannot hold.
example : consumed (-1) 2 1 < 0 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have e : (-(-1 : ℝ) * 1) = 1 := by norm_num
  unfold consumed
  rw [e]
  linarith

example : consumed (-1) 2 1 ∉ Set.Icc (0 : ℝ) 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have e : (-(-1 : ℝ) * 1) = 1 := by norm_num
  have hneg : consumed (-1) 2 1 < 0 := by
    unfold consumed
    rw [e]
    linarith
  intro hmem
  rw [Set.mem_Icc] at hmem
  linarith

end Engineering.Process.BatchReactor.Tests
