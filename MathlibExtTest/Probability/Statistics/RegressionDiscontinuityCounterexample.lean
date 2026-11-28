/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.RegressionDiscontinuityCounterexample
import Mathlib.Tactic.NormNum

/-! # Regression checks for the sharp RD discontinuity without a treatment effect -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open MathlibExt.Probability.Statistics.RegressionDiscontinuity

-- Neither side of the cutoff is missing from the running-variable distribution.
example :
    let μ := ProbabilityTheory.cond (volume : Measure ℝ) (Icc (-1) 1)
    μ (Ioo 0 (1 / 2)) ≠ 0 ∧ μ (Ioo (-(1 / 2)) 0) ≠ 0 := by
  exact sharpRD_jump_without_effect.2.1 (1 / 2) (by norm_num)

-- The step version jumps even though the treatment effect vanishes in every unit.
example :
    let m : ℝ → ℝ := (Ici (0 : ℝ)).indicator fun _ => 1
    (∀ x, m x - m x = 0) ∧
      Tendsto m (𝓝[>] (0 : ℝ)) (𝓝 1) ∧ Tendsto m (𝓝[<] (0 : ℝ)) (𝓝 0) := by
  exact ⟨sharpRD_jump_without_effect.2.2.1, sharpRD_jump_without_effect.2.2.2.2.2⟩
