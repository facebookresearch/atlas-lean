/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Real.Pi.Bounds
import MathlibExt.Combinatorics.Enumerative.CeilCotSingleton

open Real

-- At the first admissible index the three ceilings are 0, 1, and 2.
example : {n : ℕ | 1 ≤ n ∧ ⌈cot (π / (2 * n))⌉ = 1} = {2} := by
  apply (MetaMathlibExt.ceil_cot_singleton_iff 1 2 (by decide) (by decide)).2
  norm_num [cot_eq_cos_div_sin, sin_pi_div_two, cos_pi_div_two, sin_pi_div_four,
    cos_pi_div_four, sin_pi_div_six, cos_pi_div_six, Int.ceil_eq_iff]
  constructor <;> nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]

-- The fiber of 4 is not the singleton {5}: the next ceiling is already at most 4.
example : {n : ℕ | 1 ≤ n ∧ ⌈cot (π / (2 * n))⌉ = 4} ≠ {5} := by
  intro h
  have hnext := ((MetaMathlibExt.ceil_cot_singleton_iff 4 5 (by decide) (by decide)).1 h).2.2
  norm_num at hnext
  have ht : 1 / 4 < tan (π / 12) :=
    lt_trans (by linarith [pi_gt_three]) (lt_tan (by positivity) (by linarith [pi_pos]))
  have hc : cot (π / 12) ≤ 4 := by
    rw [← tan_inv_eq_cot, inv_eq_one_div, div_le_iff₀ (by linarith : 0 < tan (π / 12))]
    linarith
  have : ⌈cot (π / 12)⌉ ≤ 4 := Int.ceil_le.mpr (by simpa using hc)
  omega
