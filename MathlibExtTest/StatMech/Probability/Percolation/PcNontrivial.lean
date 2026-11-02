/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.PcNontrivial

/-!
# Tests for `MathlibExt.Probability.Percolation.PcNontrivial`

Tests `StatMech.Percolation.pc_pos` (`p_c(d) > 0`, Hammersley's path-counting bound) at `d = 1`
and `d = 3` (via `pc_pos_of_two_le`), the explicit lower bound `1/5 ≤ p_c(2)` from
`mem_subcriticalSet_of_lt`, and `theta_le_pow` at `p = 1/8`, `d = 2`, `n = 2`
(`θ_2(1/8) ≤ 1/4`).
-/

@[expose] public section

open StatMech StatMech.Percolation StatMech.Lattice
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.PcNontrivial

-- `p_c(1) > 0` and `p_c(3) > 0`.
example : 0 < pc 1 := pc_pos one_pos

example : 0 < pc 3 := pc_pos_of_two_le (by norm_num)

-- Explicit lower bound: `1/5 ≤ p_c(2)`, since `2d · (1/5) = 4/5 < 1`.
example : (1 / 5 : ℝ≥0) ≤ pc 2 := by
  have hp : (1 / 5 : ℝ≥0) ≤ 1 := by rw [div_le_one (by norm_num)]; norm_num
  exact le_pc_of_mem_subcriticalSet
    (mem_subcriticalSet_of_lt two_pos _ hp (by push_cast; norm_num))

-- The path-counting bound `θ_d(p) ≤ (2dp)^n` at `d = 2`, `p = 1/8`, `n = 2`.
example (hp : (1 / 8 : ℝ≥0) ≤ 1) : theta 2 (1 / 8) hp ≤ 1 / 4 := by
  have h := theta_le_pow two_pos _ hp 2
  have hval : ((((2 * (2 : ℕ) : ℝ≥0) * (1 / 8)) ^ 2 : ℝ≥0) : ℝ) = 1 / 4 := by
    push_cast; norm_num
  push_cast at h hval
  linarith

end MathlibExtTest.StatMech.Probability.Percolation.PcNontrivial
