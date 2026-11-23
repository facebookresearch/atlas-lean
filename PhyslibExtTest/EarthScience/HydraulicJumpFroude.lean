/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.HydraulicJumpFroude
import Mathlib.Tactic.NormNum

/-!
# Froude-ratio checks

Focused checks for `PhyslibExt.EarthScience.HydraulicJumpFroude`:
the `h1 = 1`, `h2 = 2`, `g = 1` jump has `Fr = 3` and ratio `2`;
the critical case `Fr = 1` forces equal depths.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- The canonical doubling jump: ratio 2, supercritical. -/
example : (2 : ℝ) / 1 = (Real.sqrt (1 + 8 * (3 / (1 * 1 ^ 3))) - 1) / 2
    ∧ ((1 : ℝ) < 2 ↔ (1 : ℝ) < 3 / (1 * 1 ^ 3)) := by
  have hq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hmom : (Real.sqrt 3) ^ 2 / 1 = 1 * 2 * (1 + 2) / 2 := by rw [hq]; norm_num
  have h := conjugate_froude_ratio (q := Real.sqrt 3) (g := 1) (h1 := 1) (h2 := 2)
    (by norm_num) (by norm_num) (by norm_num) hmom
  rwa [hq] at h

/-- Critical case: `Fr = 1` gives ratio 1. -/
example : (1 : ℝ) / 1 = (Real.sqrt (1 + 8 * ((1 : ℝ) ^ 2 / (1 * 1 ^ 3))) - 1) / 2 := by
  have hmom : (1 : ℝ) ^ 2 / 1 = 1 * 1 * (1 + 1) / 2 := by norm_num
  have h := conjugate_froude_ratio (q := 1) (g := 1) (h1 := 1) (h2 := 1)
    (by norm_num) (by norm_num) (by norm_num) hmom
  exact h.1
