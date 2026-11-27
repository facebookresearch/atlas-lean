/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.StochasticCalculusRoute

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Boundary example from the specification: `x = 0`, `y = 1/2` gives
`1/2 ≤ √(1/2)`. -/
example :
    |Real.sqrt ((0 : ℝ) * (1 - 0)) - Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2))| ≤
      Real.sqrt |(0 : ℝ) - 1 / 2| :=
  abs_sqrt_mul_one_sub_sub_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- At the two endpoints both diffusion coefficients vanish. -/
example :
    |Real.sqrt ((0 : ℝ) * (1 - 0)) - Real.sqrt ((1 : ℝ) * (1 - 1))| ≤
      Real.sqrt |(0 : ℝ) - 1| :=
  abs_sqrt_mul_one_sub_sub_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The left side in the first example really is `1/2`. -/
example :
    |Real.sqrt ((0 : ℝ) * (1 - 0)) - Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2))| = 1 / 2 := by
  have hsqrt : Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2)) = 1 / 2 := by
    rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h0 : Real.sqrt ((0 : ℝ) * (1 - 0)) = 0 := by norm_num
  rw [h0, hsqrt]
  norm_num

end MathlibExtTest.Biology.PopulationGenetics.Diffusion
