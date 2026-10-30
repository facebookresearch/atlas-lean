/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.NearHalfBKKKL
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.FSPerEdge

/-!
# Tests for the near-half KKL inequality

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.NearHalfBKKKL`, at the `AND` function on
`{0, 1}^Bool` under `μ_p` (variance `p²(1-p²)`, maximal influence `p`, total influence `2p`,
`σ_p² = p(1-p)`):

* `nhb_var_le_damped_add` at `AND` for every `p ∈ (0, 1)`;
* the headline `nhb_nearHalf_kkl` at `AND` for every `p ∈ (0, 1)`, and at `p = 1/2`, where the
  correction vanishes and it is the KKL inequality with constant `2`: `2 · 3/16 · log 2 ≤ 1`;
* `nhb_nearHalf_kkl_absorbed` at `AND` and `p = 3/4 ≠ 1/2`: the correction hypothesis
  `2 · 1/4 · 3/16 · log(4/3) ≤ 1` holds, and the conclusion is
  `63/256 · log(4/3) ≤ 3/2`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

/-- `nhb_var_le_damped_add` at `AND`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    p ^ 2 * (1 - p ^ 2)
      ≤ p ^ 2 / 2 + p ^ 2 * (1 - p) ^ 2 + (1 - 4 * p * (1 - p)) * (p * (1 - p)) * (2 * p) := by
  have h := nhb_var_le_damped_add hp0 hp1 andFun
  rwa [var_andInd, dampedVar_andInd hp0 hp1, ptn_sigma_sq hp0 hp1, totalInfl_andInd_p] at h

/-- `nhb_nearHalf_kkl` at `AND`, for every `p ∈ (0, 1)`. -/
lemma nhbt_nearHalf_kkl_andFun {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    2 * (p ^ 2 * (1 - p ^ 2)) * Real.log (1 / p)
      ≤ (1 + 2 * (1 - 4 * p * (1 - p)) * (p * (1 - p)) * Real.log (1 / p)) * (2 * p) := by
  have h := nhb_nearHalf_kkl hp0 hp1 andFun
  rwa [var_andInd, maxInfl_andInd_p, totalInfl_andInd_p, ptn_sigma_sq hp0 hp1] at h

/-- At `p = 1/2` the correction vanishes: `2 · 3/16 · log 2 ≤ 1`. -/
example : 2 * (3 / 16 : ℝ) * Real.log 2 ≤ 1 := by
  have h := nhbt_nearHalf_kkl_andFun (p := 1 / 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

/-- `log (4/3) ≤ 1/3`. -/
lemma nhbt_log_four_thirds_le : Real.log (4 / 3) ≤ 1 / 3 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
  linarith

/-- `nhb_nearHalf_kkl_absorbed` at `AND` and `p = 3/4`, where its correction hypothesis holds. -/
example : (9 / 16 * (7 / 16) : ℝ) * Real.log (4 / 3) ≤ 3 / 2 := by
  have hlog0 : 0 ≤ Real.log (4 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have h := nhb_nearHalf_kkl_absorbed (p := 3 / 4) (by norm_num) (by norm_num) andFun (by
    rw [maxInfl_andInd_p, ptn_sigma_sq (by norm_num) (by norm_num)]
    norm_num
    nlinarith [nhbt_log_four_thirds_le])
  rw [var_andInd, maxInfl_andInd_p, totalInfl_andInd_p] at h
  norm_num at h ⊢
  linarith

end StatMechTest.BooleanFunctions
