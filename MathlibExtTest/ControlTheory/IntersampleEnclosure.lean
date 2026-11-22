/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.IntersampleEnclosure
import Mathlib.Analysis.Normed.Group.Real

open ControlTheory

-- Straight-line motion `γ t = 2t` on `[1, 4]` with
-- `vbar = 2`, sampled value `xhat = 3 / 2`, `ε = 1 / 2`:
-- the enclosure at `t = 4` is `13 / 2 ≤ 1 / 2 + 2 * 3`,
-- with equality, so the bound is tight.
example :
    ‖(2 : ℝ) * 4 - 3 / 2‖ ≤ 1 / 2 + 2 * 3 :=
  intersample_displacement_le (γ := fun t : ℝ => 2 * t) (xhat := 3 / 2)
    (ts := 1) (h := 3) (vbar := 2) (ε := 1 / 2) (by norm_num)
    (by
      intro t ht
      have h1 : (0 : ℝ) ≤ t - 1 := by linarith [ht.1]
      calc ‖(2 : ℝ) * t - 2 * 1‖ = 2 * (t - 1) := by
            rw [show (2 : ℝ) * t - 2 * 1 = 2 * (t - 1) by ring]
            exact Real.norm_of_nonneg (mul_nonneg (by norm_num) h1)
        _ ≤ 2 * (t - 1) := le_rfl)
    (by norm_num)
    4 ⟨by norm_num, by norm_num⟩

example : ‖(2 : ℝ) * 4 - 3 / 2‖ = 13 / 2 := by norm_num

-- At the sample time `t = ts` the enclosure is the start
-- bound itself.
example :
    ‖(2 : ℝ) * 1 - 3 / 2‖ ≤ 1 / 2 + 2 * 3 :=
  intersample_displacement_le (γ := fun t : ℝ => 2 * t) (xhat := 3 / 2)
    (ts := 1) (h := 3) (vbar := 2) (ε := 1 / 2) (by norm_num)
    (by
      intro t ht
      have h1 : (0 : ℝ) ≤ t - 1 := by linarith [ht.1]
      calc ‖(2 : ℝ) * t - 2 * 1‖ = 2 * (t - 1) := by
            rw [show (2 : ℝ) * t - 2 * 1 = 2 * (t - 1) by ring]
            exact Real.norm_of_nonneg (mul_nonneg (by norm_num) h1)
        _ ≤ 2 * (t - 1) := le_rfl)
    (by norm_num)
    1 ⟨le_rfl, by norm_num⟩

-- The motion premise cannot be dropped: a spike to `10` at
-- `t = 2` violates the `vbar = 1` motion bound on `[0, 3]`
-- (and the would-be enclosure `10 ≤ 0 + 1 * 3` is false).
example :
    ¬ ∀ t ∈ Set.Icc (0 : ℝ) 3,
      ‖(fun t : ℝ => if t = 2 then 10 else t) t
        - (fun t : ℝ => if t = 2 then 10 else t) 0‖ ≤ 1 * (t - 0) := by
  intro h
  have h2 := h 2 ⟨by norm_num, by norm_num⟩
  norm_num at h2

#print axioms intersample_displacement_le
