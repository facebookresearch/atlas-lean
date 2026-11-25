/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.PcNontrivial

@[expose] public section

open StatMech StatMech.Percolation
open scoped NNReal

namespace MathlibExtTest.Probability.Percolation.PcNontrivial

/-- On the square lattice the path-counting bound reads `1/4 ≤ p_c(2) ≤ 1`. -/
example : (1 / 4 : ℝ≥0) ≤ pc 2 ∧ pc 2 ≤ 1 := by
  refine ⟨?_, pc_le_one⟩
  have h := one_div_two_mul_le_pc (d := 2) (by norm_num)
  have h4 : (2 : ℝ≥0) * ((2 : ℕ) : ℝ≥0) = 4 := by norm_num
  rwa [h4] at h

/-- On `ℤ = ℤ^1` the bound is `1/2 ≤ p_c(1)` (in fact `p_c(1) = 1`). -/
example : (1 / 2 : ℝ≥0) ≤ pc 1 := by
  have h := one_div_two_mul_le_pc (d := 1) (by norm_num)
  simpa using h

end MathlibExtTest.Probability.Percolation.PcNontrivial
