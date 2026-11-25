/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ScottishBook157

/-! # Tests for the approximate derivative monotonicity test -/

open Filter MeasureTheory Set MathlibExt.Analysis.ScottishBook157Wanted
open scoped Topology

-- The identity has empty bad sets at sufficiently small radii, and every positive step
-- has difference quotient 1. This exercises both exact hypotheses of the theorem.
example : Monotone (fun x : ℝ ↦ x) := by
  apply wardApproximatelyContinuousPositiveDerivMonotone
  · intro x ε hε
    apply Metric.tendsto_nhdsWithin_nhds.mpr
    intro ζ hζ
    refine ⟨ε, hε, fun r hr hrε ↦ ?_⟩
    have hr' : r < ε := by simpa [Real.dist_eq, abs_of_pos hr] using hrε
    have hempty : {y : ℝ | ε ≤ |y - x|} ∩ Ioo (x - r) (x + r) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hlt : |y - x| < ε := abs_lt.mpr ⟨by linarith [hy.2.1], by linarith [hy.2.2]⟩
      exact hlt.not_ge hy.1
    change dist ((volume ({y : ℝ | ε ≤ |y - x|} ∩ Ioo (x - r) (x + r))).toReal / (2 * r)) 0 < ζ
    simpa [hempty] using hζ
  · intro x
    refine ⟨1 / 2, by norm_num, 1, zero_lt_one, fun δ hδ ↦ ⟨δ, hδ, le_rfl, ?_⟩⟩
    have hgood :
        {h : ℝ | h ∈ Ioc 0 δ ∧ (1 / 2 : ℝ) < (x + h - x) / h} = Ioc 0 δ := by
      ext h
      refine ⟨fun hh ↦ hh.1, fun hh ↦ ⟨hh, ?_⟩⟩
      rw [show x + h - x = h by ring, div_self hh.1.ne']
      norm_num
    change 1 ≤ (volume {h : ℝ | h ∈ Ioc 0 δ ∧ (1 / 2 : ℝ) < (x + h - x) / h}).toReal / δ
    simp only [hgood, ← Measure.real_def, Real.volume_real_Ioc_of_le hδ.le, sub_zero,
      div_self hδ.ne', le_refl]
