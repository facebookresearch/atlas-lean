/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedHardyInequality
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Boundary and endpoint tests for the annulus Hardy inequality -/

open MeasureTheory
open MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedHardyInequalityWanted

-- On the unit circle the weight vanishes, and the full open annulus excludes the circle.
example (x : R2) (hx : ‖x‖ = 1) : phi x = 0 ∧ x ∉ Omega1 := by
  simp [phi, Omega1, B, closure_ball _ one_ne_zero, Metric.mem_closedBall, hx]

-- The intermediate circle belongs to the full annulus only and has weight one.
example (x : R2) (hx : ‖x‖ = 2) : x ∈ Omega1 ∧ x ∉ Omega2 ∧ phi x = 1 := by
  norm_num [Omega1, Omega2, B, closure_ball _ (by norm_num : (2 : ℝ) ≠ 0),
    closure_ball _ one_ne_zero, Metric.mem_ball, Metric.mem_closedBall, hx, phi]

-- At p = 1 the constant function has zero gradient and gives a volume comparison.
example : ∃ C : ℝ, 0 < C ∧ volume Omega1 ≤ ENNReal.ofReal C * volume Omega2 := by
  obtain ⟨C, hC, H⟩ := exists_eLpNorm_le_weighted_grad_add_outer_annulus 1 le_rfl
  have hfin : volume Omega2 < ⊤ :=
    (measure_mono (show Omega2 ⊆ B 3 from Set.sdiff_subset)).trans_lt measure_ball_lt_top
  have hnorm (s : Set R2) :
      eLpNorm (fun _ : R2 ↦ (1 : ℝ)) 1 (volume.restrict s) = volume s := by
    simp [eLpNorm_const' _ one_ne_zero ENNReal.one_ne_top]
  have h := H (fun _ ↦ 1) contDiffOn_const (by simp) (by simpa [hnorm] using hfin.ne)
  exact ⟨C, hC, by simpa [hnorm] using h⟩
