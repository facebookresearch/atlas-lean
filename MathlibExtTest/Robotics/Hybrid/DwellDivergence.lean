/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Robotics.Hybrid.DwellDivergence
import Mathlib.Analysis.SpecificLimits.Basic

open Robotics.Hybrid

-- Constant unit durations: elapsed time after `n` steps
-- is exactly `n`, and the lower bound is tight.
example (n : ℕ) : dwellElapsed (fun _ => 1) n = n := by
  unfold dwellElapsed
  simp

-- No positive dwell bounds the geometric durations
-- `2 ^ (-k)` from below.
example : ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, δ ≤ (2 : ℝ) ^ (-(k : ℤ)) := by
  rintro ⟨δ, hδ, hle⟩
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hδ)).exists
  have h2 : (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2) ^ n := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, one_div]
  linarith [hle n]

-- Elapsed time at step `0` is `0`.
example (d : ℕ → ℝ) : dwellElapsed d 0 = 0 := by
  unfold dwellElapsed
  simp

#print axioms dwellElapsed_ge
#print axioms dwellElapsed_tendsto_atTop
