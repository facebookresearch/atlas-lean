/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Optimization.QuasiNewton

open MathlibExt.Analysis.Optimization.QuasiNewton

-- In `ℝ` with `B = I`, `s = 1`, `y = 2`: the update satisfies `B⁺ s = y` …
example : bfgsUpdate (ContinuousLinearMap.id ℝ ℝ) 1 2 1 = 2 :=
  bfgsUpdate_apply_self (by norm_num) (by norm_num)

-- … and `B⁺ = 2 I`, which is again positive definite since `⟪y, s⟫ = 2 > 0`.
example (v : ℝ) : bfgsUpdate (ContinuousLinearMap.id ℝ ℝ) 1 2 v = 2 * v := by
  rw [bfgsUpdate_apply]; simp; ring

example : ∀ v : ℝ, v ≠ 0 → 0 < inner ℝ (bfgsUpdate (ContinuousLinearMap.id ℝ ℝ) 1 2 v) v :=
  bfgsUpdate_pos (fun u v => by simp) (fun v hv => by
    simp; exact lt_of_le_of_ne (sq_nonneg v) (Ne.symm (pow_ne_zero 2 hv))) one_ne_zero (by norm_num)

-- Negative curvature `⟪y, s⟫ = -1 < 0` destroys positive definiteness: `B⁺ s = y` and
-- `⟪B⁺ s, s⟫ = -1`.
example : ¬ ∀ v : ℝ, v ≠ 0 →
    0 < inner ℝ (bfgsUpdate (ContinuousLinearMap.id ℝ ℝ) 1 (-1) v) v := fun h => by
  have := inner_pos_of_bfgsUpdate_pos one_ne_zero (by norm_num) (by norm_num) h
  norm_num at this
