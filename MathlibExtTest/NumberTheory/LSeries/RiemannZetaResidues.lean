/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.RiemannZetaResidues

/-!
# Tests for the residue computation in the explicit formula

The trivial-zero series `∑_{m ≥ 1} x^{-2m}/(2m) = -½ log (1 - x⁻²)` at `x = 2`, and the uniform
bound on `½ log (1 - y⁻²)`.
-/

@[expose] public section

open Filter Topology

namespace RiemannZetaResiduesTest

/-- At `x = 2`: `∑_{m ≥ 1} 4^{-m}/(2m) → -½ log (3/4)`. -/
example : Tendsto (fun k : ℕ => ∑ m ∈ Finset.Icc 1 k, ((2 : ℝ) : ℂ) ^ (-(2 * (m : ℂ))) /
    (2 * (m : ℂ))) atTop (𝓝 (-((1 / 2 : ℂ) * (Real.log (3 / 4) : ℂ)))) := by
  have h := tendsto_sum_cpow_neg_two_mul_div_two_mul (x := 2) (by norm_num)
  norm_num at h ⊢
  exact h

example : ‖(1 / 2 : ℂ) * (Real.log (1 - (2 : ℝ) ^ (-2 : ℤ)) : ℂ)‖ ≤ 1 / 2 :=
  norm_half_log_one_sub_zpow_neg_two_le (by norm_num)

end RiemannZetaResiduesTest
