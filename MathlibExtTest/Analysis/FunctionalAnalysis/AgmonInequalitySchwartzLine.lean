/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.AgmonInequalitySchwartzLine
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Tests for Agmon's inequality on the line -/

open MeasureTheory
open MathlibExt.Analysis.FunctionalAnalysis.AgmonInequalitySchwartzLineWanted

-- For the zero function, both sides vanish for every constant.
example (C : ℝ) :
    ‖(0 : SchwartzMap ℝ ℝ).toLp ⊤ volume‖ =
      C * Real.sqrt ‖(0 : SchwartzMap ℝ ℝ).toLp 2 volume‖ *
        Real.sqrt ‖(SchwartzMap.derivCLM ℝ ℝ 0).toLp 2 volume‖ := by
  simp [SchwartzMap.norm_toLp, FunLike.coe_zero]

-- A smooth compactly supported bump gives a strictly positive left-hand side.
example : ∃ C > 0, ∃ f : SchwartzMap ℝ ℝ,
    0 < ‖f.toLp ⊤ volume‖ ∧
      ‖f.toLp ⊤ volume‖ ≤ C * Real.sqrt ‖f.toLp 2 volume‖ *
        Real.sqrt ‖(SchwartzMap.derivCLM ℝ ℝ f).toLp 2 volume‖ := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f := bump.hasCompactSupport.toSchwartzMap bump.contDiff
  obtain ⟨C, hC, hbound⟩ := exists_norm_toLp_top_le_mul_sqrt_norm_toLp_two_mul_sqrt_deriv
  refine ⟨C, hC, f, norm_pos_iff.mpr ?_, hbound f⟩
  intro h
  have hzero : (0 : SchwartzMap ℝ ℝ).toLp ⊤ volume = 0 := by
    simp [SchwartzMap.toLp, FunLike.coe_zero]
  have hf : f = 0 := SchwartzMap.injective_toLp ⊤ volume (h.trans hzero.symm)
  have hcenter : f 0 = 1 := bump.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
  simp [hf] at hcenter
