/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.KernCondition
import Mathlib.Tactic.NormNum

/-!
# Kern-condition checks

Focused checks for `PhyslibExt.EarthScience.Geotechnical.KernCondition`:
at the exact kern edge (`|M| = N * B / 6`) full contact is admitted
with one zero edge pressure; just beyond the kern it is not.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Exact kern edge is admitted. -/
example : ((0 : ℝ) ≤ (10 : ℝ) / 6 - 6 * 10 / 6 ^ 2
    ∧ (0 : ℝ) ≤ 10 / 6 + 6 * 10 / 6 ^ 2) := by
  have h := (kern_condition_iff (N := 10) (M := 10) (B := 6)
    (by norm_num) (by norm_num)).2 (by norm_num)
  exact h

/-- Just beyond the kern is excluded. -/
example : ¬ ((0 : ℝ) ≤ (10 : ℝ) / 6 - 6 * (61 / 6 : ℝ) / 6 ^ 2
    ∧ (0 : ℝ) ≤ 10 / 6 + 6 * (61 / 6 : ℝ) / 6 ^ 2) := by
  rw [kern_condition_iff (N := 10) (M := (61 / 6 : ℝ)) (B := 6)
    (by norm_num) (by norm_num)]
  norm_num
