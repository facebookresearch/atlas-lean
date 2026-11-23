/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.SharpnessBelowPc

@[expose] public section

open StatMech StatMech.Percolation
open scoped NNReal

namespace MathlibExtTest.Probability.Percolation.SharpnessBelowPc

/-- Non-vacuity on `ℤ²`: the density `p_c(2)/2` is strictly positive and strictly below `p_c(2)`,
so exponential decay and `θ = 0` hold at a nondegenerate density. -/
example : ∃ p : ℝ≥0, 0 < p ∧ ∃ hp : p ≤ 1, theta 2 p hp = 0 ∧
    ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n) := by
  have hpc : 0 < pc 2 := pc_pos (by norm_num)
  have hpc1 : pc 2 ≤ 1 := by
    apply csSup_le' ; intro q hq ; exact hq.1
  refine ⟨pc 2 / 2, by positivity, ?_⟩
  have hlt : pc 2 / 2 < pc 2 := NNReal.half_lt_self hpc.ne'
  have hp : pc 2 / 2 ≤ 1 := hlt.le.trans hpc1
  exact ⟨hp, theta_eq_zero_of_lt_pc (by norm_num) hp hlt,
    crossProb_exp_decay_of_lt_pc (by norm_num) hp hlt⟩

/-- `φ_p(S)` is monotone across the whole range `0 ≤ 1/3 ≤ 1/2`, for the singleton `S = {0}`. -/
example :
    phi 3 (1 / 3) (by rw [← NNReal.coe_le_coe]; norm_num) {origin 3} ≤
      phi 3 (1 / 2) (by rw [← NNReal.coe_le_coe]; norm_num) {origin 3} :=
  phi_mono _ _ (by rw [← NNReal.coe_le_coe]; norm_num) _

/-- The down-set property is applied at `p = 0`, the degenerate endpoint. -/
example {q : ℝ≥0} (hq : q ∈ tildePcSet 2) : (0 : ℝ≥0) ∈ tildePcSet 2 :=
  mem_tildePcSet_of_le hq (by simp)

end MathlibExtTest.Probability.Percolation.SharpnessBelowPc
