/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import MathlibExt.Probability.DirichletForm.Brownian

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal ContDiff

namespace MathlibExtTest.Probability.DirichletForm.Brownian

open MathlibExt.Probability.DirichletFormWanted

private noncomputable def bump : ContDiffBump (3 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

-- A nonzero smooth function with compact support away from the origin.
example : bump 3 = 1 ∧
    Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)⁻¹ *
      ∫ x, bump x * (bump x - ∫ y, bump (x + y) ∂gaussianReal 0 t))
      (𝓝[>] 0) (𝓝 (1 / 2 * ∫ x, deriv bump x ^ 2)) := by
  refine ⟨bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le), ?_⟩
  exact tendsto_brownian_approximatingForm (hf := bump.contDiff) (hfc := bump.hasCompactSupport)

-- The zero function has an identically zero limit.
example :
    Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)⁻¹ *
      ∫ x, (0 : ℝ → ℝ) x * ((0 : ℝ → ℝ) x - ∫ y, (0 : ℝ → ℝ) (x + y) ∂gaussianReal 0 t))
      (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_brownian_approximatingForm (f := (0 : ℝ → ℝ))
    (show ContDiff ℝ ∞ (fun _ : ℝ ↦ (0 : ℝ)) from contDiff_const) HasCompactSupport.zero
  have hzero : (1 / 2 : ℝ) * (∫ x, deriv (0 : ℝ → ℝ) x ^ 2) = 0 := by simp
  rwa [hzero] at h

end MathlibExtTest.Probability.DirichletForm.Brownian
