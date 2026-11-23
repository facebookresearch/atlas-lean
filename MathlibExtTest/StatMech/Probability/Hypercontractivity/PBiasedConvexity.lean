/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.PBiasedConvexity

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.PBiasedConvexity`

* `pcx_OneVarCore` proves `pbt_OneVarCore p q` for `0 < p < 1`, `1 ≤ q ≤ 2`; it is
  instantiated at `p = 1/3`, `q = 3/2` and evaluated at `z = 1`;
* `pcx_two_point_value` (the `p`-biased two-point inequality) at `p = 1/3`, `q = 3/2`, and at
  `p = 1/2`, `q = 2`, `u = 1`, `v = -1`, where it reads `1 ≤ 1`;
* `pcx_g_at_zero`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.PBiasedConvexity

open _root_.StatMech.Probability

-- `pcx_OneVarCore` with all hypotheses instantiated.
example : pbt_OneVarCore (1 / 3) (3 / 2) :=
  pcx_OneVarCore (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Evaluated at `z = 1`: `pbt_g (1/3) (3/2) 1 ≤ 1`.
example : pbt_g (1 / 3) (3 / 2) 1
    ≤ ((1 - 1 / 3) + 1 / 3 * (1 : ℝ) ^ (3 / 2 : ℝ)) ^ (2 / (3 / 2 : ℝ)) :=
  pcx_OneVarCore (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 zero_le_one

-- `pcx_two_point_value` at `p = 1/3`, `q = 3/2`.
example (u v : ℝ) :
    ((1 - 1 / 3) * u + 1 / 3 * v) ^ 2
        + (3 / 2 - 1) * 4 * (1 / 3) ^ 2 * (1 - 1 / 3) ^ 2 * (u - v) ^ 2
      ≤ ((1 - 1 / 3) * |u| ^ (3 / 2 : ℝ) + 1 / 3 * |v| ^ (3 / 2 : ℝ)) ^ (2 / (3 / 2 : ℝ)) :=
  pcx_two_point_value (by norm_num) (by norm_num) (by norm_num) (by norm_num) u v

-- At `p = 1/2`, `q = 2`, `u = 1`, `v = -1`, the left side is `0 + 1 * 4 * 1/16 * 4 = 1` and
-- the right side is `1`.
example : ((1 - 1 / 2 : ℝ) * 1 + 1 / 2 * (-1)) ^ 2
      + (2 - 1) * 4 * (1 / 2) ^ 2 * (1 - 1 / 2) ^ 2 * (1 - (-1)) ^ 2 = 1 ∧
    ((1 - 1 / 2 : ℝ) * |(1 : ℝ)| ^ (2 : ℝ) + 1 / 2 * |(-1 : ℝ)| ^ (2 : ℝ)) ^ (2 / (2 : ℝ)) = 1 := by
  constructor <;> norm_num

-- `pcx_g` vanishes at `0`.
example : pcx_g (1 / 3) (3 / 2) 0 = 0 := pcx_g_at_zero _ _

end MathlibExtTest.StatMech.Probability.Hypercontractivity.PBiasedConvexity
