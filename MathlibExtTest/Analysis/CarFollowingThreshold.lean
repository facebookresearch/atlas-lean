/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CarFollowingThreshold
import Mathlib.Tactic.NormNum

/-!
# Gain-threshold checks

Focused checks for `MathlibExt.Analysis.CarFollowingThreshold`:
the boundary `lambda * T = 1 / 2` satisfies the all-frequency
inequality, while `lambda * T = 0.51` does not.

These are elaboration and non-vacuity checks, not new results.
-/

/-- Boundary case is admitted. -/
example : ∀ omega : ℝ, 0 < omega
    → omega > 2 * (1 / 2 : ℝ) * Real.sin (omega * 1) :=
  (CarFollowingGain.gain_threshold_all_frequencies (lambda := 1 / 2) (T := 1)
    (by norm_num) (by norm_num)).2 (by norm_num)

/-- Just past the boundary is excluded. -/
example : ¬ ∀ omega : ℝ, 0 < omega
    → omega > 2 * (51 / 100 : ℝ) * Real.sin (omega * 1) := by
  rw [CarFollowingGain.gain_threshold_all_frequencies (lambda := 51 / 100) (T := 1)
    (by norm_num) (by norm_num)]
  norm_num


/-- The composed transfer-function gain statement at the boundary. -/
example : ∀ w : ℝ, 0 < w
    → ‖((1 / 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I * w * 1))‖
      < ‖CarFollowingGain.denom (1 / 2) 1 w‖ :=
  (CarFollowingGain.gain_lt_one_all_frequencies (lam := 1 / 2) (T := 1)
    (by norm_num) (by norm_num)).2 (by norm_num)
