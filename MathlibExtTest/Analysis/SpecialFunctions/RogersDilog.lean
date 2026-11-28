/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.SpecialFunctions.RogersDilog

open Filter Real Set
open scoped Topology

-- At the midpoint, the correction to Li₂ is a positive log square divided by two.
example : rogersDilog (1 / 2) - li2PowerSeries (1 / 2) = log (1 / 2) ^ 2 / 2 := by
  rw [rogersDilog_eq_tsum_add_log_mul_log, li2PowerSeries_eq_tsum,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  ring

-- Reflection fixes the midpoint value and hence its sign.
example : 0 < rogersDilog (1 / 2) := by
  have h := rogersDilog_reflection (x := 1 / 2) (by norm_num [mem_Icc])
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  linarith only [h, sq_pos_of_pos pi_pos]

-- Closed-interval continuity reaches the upper endpoint with the Basel value.
example : Tendsto rogersDilog (𝓝[Icc 0 1] 1) (𝓝 (π ^ 2 / 6)) := by
  have h1 : rogersDilog 1 = π ^ 2 / 6 := by
    simpa only [rogersDilog_zero, sub_zero, zero_add] using
      rogersDilog_reflection (x := 0) (by norm_num [mem_Icc])
  rw [← h1]
  exact (continuousOn_rogersDilog 1 (by norm_num [mem_Icc])).tendsto

-- The first fractional argument at 1/2 and 2/3 is exactly 1/4 and stays in the domain.
example : let u : ℝ := (1 / 2) * (1 - 2 / 3) / (1 - (1 / 2) * (2 / 3))
    u = 1 / 4 ∧ u ∈ Ioo 0 1 := by
  dsimp only
  exact ⟨by norm_num, abel_five_term_arg_mem_Ioo (by norm_num [mem_Ioo])
    (by norm_num [mem_Ioo])⟩

-- For unequal arguments 1/2 and 2/3, the product is 1/3 and the two new
-- arguments are 1/4 and 1/2. The repeated midpoint term cancels.
example : rogersDilog (2 / 3) = rogersDilog (1 / 3) + rogersDilog (1 / 4) := by
  have h := rogersDilog_five_term (x := 1 / 2) (y := 2 / 3)
    (by norm_num [mem_Ioo]) (by norm_num [mem_Ioo])
  norm_num at h
  linarith only [h]
