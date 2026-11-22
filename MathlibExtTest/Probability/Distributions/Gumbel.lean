/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.Gumbel

/-!
# Tests for the Gumbel distribution function and quantile

Concrete values that pin both formulas, both inverse directions at a fitted location `2` and
scale `3` and at the standard parameters, the inverse identity at a negative scale (it needs only
`β ≠ 0`), strict monotonicity, and the order characterization of the quantile.
-/

open ProbabilityTheory Real

namespace MathlibExtTest.Probability.Distributions.Gumbel

/-- Standard Gumbel (`μ = 0`, `β = 1`): the distribution function at `0` is `exp (-1)`. -/
example : gumbelCDF 0 1 0 = exp (-1) := by simp [gumbelCDF]

/-- Standard Gumbel: the quantile at `q = exp (-1)` is `0`. -/
example : gumbelQuantile 0 1 (exp (-1)) = 0 := by simp [gumbelQuantile]

/-- Standard Gumbel: the median is `-log (log 2)`. -/
example : gumbelQuantile 0 1 (1 / 2) = -log (log 2) := by
  simp [gumbelQuantile, log_inv]

/-- Location `2`, scale `3`: the distribution function at the `0.9`-quantile is `0.9`. -/
example : gumbelCDF 2 3 (gumbelQuantile 2 3 0.9) = 0.9 :=
  gumbelCDF_gumbelQuantile (by norm_num) (by norm_num) (by norm_num)

/-- Location `2`, scale `3`: the quantile at `gumbelCDF 2 3 5` is `5`. -/
example : gumbelQuantile 2 3 (gumbelCDF 2 3 5) = 5 := gumbelQuantile_gumbelCDF (by norm_num) 2 5

/-- Standard Gumbel: the quantile at `gumbelCDF 0 1 0` is `0`. -/
example : gumbelQuantile 0 1 (gumbelCDF 0 1 0) = 0 := gumbelQuantile_gumbelCDF one_ne_zero 0 0

/-- The inverse identity needs only `β ≠ 0`: it also holds at scale `-1`. -/
example : gumbelCDF 0 (-1) (gumbelQuantile 0 (-1) (1 / 2)) = 1 / 2 :=
  gumbelCDF_gumbelQuantile (by norm_num) (by norm_num) (by norm_num)

/-- Strict monotonicity: `F(0) < F(1)` for the standard Gumbel law. -/
example : gumbelCDF 0 1 0 < gumbelCDF 0 1 1 := strictMono_gumbelCDF 0 one_pos one_pos

/-- Order characterization at the `exp (-1)`-quantile of the standard law, which is `0`: a level
`x` has `F(x) ≥ exp (-1)` exactly when `x ≥ 0`. -/
example (x : ℝ) : exp (-1) ≤ gumbelCDF 0 1 x ↔ 0 ≤ x := by
  rw [← gumbelQuantile_le_iff_le_gumbelCDF one_pos (exp_pos _) (exp_lt_one_iff.2 (by norm_num))]
  simp [gumbelQuantile]

end MathlibExtTest.Probability.Distributions.Gumbel
