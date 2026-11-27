/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.RosenbaumSensitivity
import Mathlib.Tactic.NormNum

open WantedExt.Probability.Statistics.RosenbaumSensitivityWanted

-- With no hidden bias, both bounds coincide at `1 / 2`.
example (u v : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (0 * u) / (Real.exp (0 * u) + Real.exp (0 * v)) = 1 / 2 := by
  have h := treatmentProb_mem (γ := 0) le_rfl hu.1 hu.2 hv.1 hv.2
  apply le_antisymm
  · simpa only [Real.exp_zero, one_add_one_eq_two] using h.2
  · simpa only [Real.exp_zero, one_add_one_eq_two] using h.1

-- At the opposite ends of the covariate interval the upper bound is attained.
example (γ : ℝ) (hγ : 0 ≤ γ) :
    Real.exp (γ * 1) / (Real.exp (γ * 1) + Real.exp (γ * 0)) = Real.exp γ / (1 + Real.exp γ) := by
  apply le_antisymm
  · exact (treatmentProb_mem hγ (by norm_num) le_rfl le_rfl (by norm_num)).2
  · simp [add_comm]
