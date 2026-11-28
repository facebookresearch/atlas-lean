/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.ComputerScience.LinearProbingAnalysis
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the fixed-load-factor limit of successful-search cost

Tables holding five items have mean successful-search cost tending to `1`. Tables holding
`N / 2` items have mean successful-search cost tending to `3 / 2`.
Source: D. E. Knuth, *Notes on "open" addressing*, 22 July 1963,
typeset by H. Prodinger in 1997.
-/

open Filter Topology

namespace CSLibExtTest.ComputerScience.LinearProbingAnalysis

open Cslib.Algorithms.Lean.LinearProbing

/-- Tables holding five items have mean successful-search cost tending to `1`. -/
example : Tendsto (fun N : ℕ => (successfulSearchCost N 5 : ℝ)) atTop (𝓝 1) := by
  have hn : ∀ᶠ N : ℕ in atTop, 1 ≤ 5 ∧ 5 ≤ N := by
    filter_upwards [eventually_ge_atTop 5] with N hN
    exact ⟨by norm_num, hN⟩
  have h := tendsto_successfulSearchCost 0 le_rfl (by norm_num) (fun _ => 5) hn
    (tendsto_const_div_atTop_nhds_zero_nat 5)
  convert h using 1
  norm_num

private theorem tendsto_half_load :
    Tendsto (fun N : ℕ => ((N / 2 : ℕ) : ℝ) / N) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlow : Tendsto (fun N : ℕ => (1 / 2 : ℝ) - 1 / N) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hbound : N ≤ 2 * (N / 2) + 1 := by omega
    have hbound' : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hbound
    apply (le_div_iff₀ hpos).2
    field_simp
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hbound : 2 * (N / 2) ≤ N := by omega
    have hbound' : 2 * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hbound
    apply (div_le_iff₀ hpos).2
    linarith

/-- Half-full tables have mean successful-search cost tending to `3 / 2`. -/
example : Tendsto (fun N : ℕ => (successfulSearchCost N (N / 2) : ℝ)) atTop
    (𝓝 (3 / 2 : ℝ)) := by
  have hn : ∀ᶠ N : ℕ in atTop, 1 ≤ N / 2 ∧ N / 2 ≤ N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    omega
  have h := tendsto_successfulSearchCost (1 / 2) (by norm_num) (by norm_num)
    (fun N => N / 2) hn tendsto_half_load
  convert h using 1
  norm_num

end CSLibExtTest.ComputerScience.LinearProbingAnalysis
