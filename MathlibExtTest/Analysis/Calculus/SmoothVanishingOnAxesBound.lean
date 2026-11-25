/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.SmoothVanishingOnAxesBound
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for the product bound for smooth functions vanishing on the axes -/

open MathlibExt.Analysis.Calculus.SmoothVanishingOnAxesBoundWanted

-- For the product function, a point with nonzero coordinates of opposite sign forces `C ≥ 1`.
example : ∃ C : ℝ, 1 ≤ C ∧
    ∀ x y : ℝ, (x, y) ∈ Metric.ball (0 : ℝ × ℝ) 1 → |x * y| ≤ C * |x| * |y| := by
  obtain ⟨C, _, hC⟩ := exists_abs_le_mul_abs_mul_abs_of_contDiff_of_eq_zero_on_axes
    (fun p => p.1 * p.2) contDiff_mul (fun _ _ h => h)
  have hpoint : (-(1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ Metric.ball (0 : ℝ × ℝ) 1 := by
    norm_num [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff]
  have h := hC (-(1 / 2)) (1 / 2) hpoint
  norm_num at h
  exact ⟨C, by linarith, hC⟩
