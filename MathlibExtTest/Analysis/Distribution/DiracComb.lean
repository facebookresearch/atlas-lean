/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Distribution.DiracComb
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Testing the Dirac comb on a single lattice point -/

open scoped SchwartzMap
open MathlibExt.Analysis.Distribution.TemperedExamplesWanted

-- A bump of outer radius one isolates the unit mass at any prescribed integer.
example : ∃ T : 𝓢'(ℝ, ℂ), ∀ k : ℤ, ∃ g : 𝓢(ℝ, ℂ),
    g (k : ℝ) = 1 ∧ (∀ n : ℤ, n ≠ k → g (n : ℝ) = 0) ∧ T g = 1 := by
  obtain ⟨T, hT⟩ := diracComb_toTemperedDistribution
  refine ⟨T, fun k ↦ ?_⟩
  let b : ContDiffBump (k : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let g : 𝓢(ℝ, ℂ) := (b.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hcenter : g (k : ℝ) = 1 := by
    change (b (k : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), Complex.ofReal_one]
  have hrest (n : ℤ) (hn : n ≠ k) : g (n : ℝ) = 0 := by
    change (b (n : ℝ) : ℂ) = 0
    apply Complex.ofReal_eq_zero.mpr
    apply b.zero_of_le_dist
    change 1 ≤ dist (n : ℝ) (k : ℝ)
    rw [Real.dist_eq]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hn)
  exact ⟨g, hcenter, hrest, (hT g).trans ((tsum_eq_single k hrest).trans hcenter)⟩
