/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecificLimits.ExpOneTaylorRemainderBound
import Mathlib.Tactic.Linarith

open MathlibExt.Analysis.SpecificLimits.ExpOneTaylorRemainderBoundWanted

-- The first admissible index gives the strict enclosure 2 < e < 3.
example : 2 < Real.exp 1 ∧ Real.exp 1 < 3 := by
  have h := exp_one_sub_sum_inv_factorial_pos_and_lt 1 (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  constructor <;> linarith [h.1, h.2]

-- At the next index, the factorial in the error bound gives a width of 1/4.
example : 5 / 2 < Real.exp 1 ∧ Real.exp 1 < 11 / 4 := by
  have h := exp_one_sub_sum_inv_factorial_pos_and_lt 2 (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  constructor <;> linarith [h.1, h.2]
