/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.PBiasedTwoPoint

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.PBiasedTwoPoint`

* `pbt_g` and `pbt_lhs` computed at small inputs;
* `pbt_OneVarCore` proved for `q = 1` (`pbt_OneVarCore_q_one`), at `p = 1/3` and `p = 2/3`;
* `pbt_two_point_value_of_core` instantiated with these cores (`p = 1/3`, `q = 1`), and its
  conclusion evaluated at `u = 3`, `v = 0` to `4 ≤ 4`.

The unconditional version for `1 ≤ q ≤ 2` is tested in
`MathlibExtTest.StatMech.Probability.Hypercontractivity.PBiasedConvexity`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.PBiasedTwoPoint

open _root_.StatMech.Probability

-- `pbt_g` at `p = 1/2`, `q = 2`, `z = 3`: `(1/2 + 3/2)^2 + 4 * (1/16) * 4 = 5`.
example : pbt_g (1 / 2) 2 3 = 5 := by norm_num [pbt_g]

-- `pbt_lhs` at `q = 1` is the square of the `p`-mean.
example (p u v : ℝ) : pbt_lhs p 1 u v = ((1 - p) * u + p * v) ^ 2 := by simp [pbt_lhs]

-- `pbt_OneVarCore` holds for `q = 1`.
example : pbt_OneVarCore (1 / 3) 1 ∧ pbt_OneVarCore (1 - 1 / 3) 1 :=
  ⟨pbt_OneVarCore_q_one _, pbt_OneVarCore_q_one _⟩

-- `pbt_two_point_value_of_core` with every hypothesis instantiated (`p = 1/3`, `q = 1`).
example (u v : ℝ) :
    ((1 - 1 / 3) * u + 1 / 3 * v) ^ 2 + (1 - 1) * 4 * (1 / 3) ^ 2 * (1 - 1 / 3) ^ 2 * (u - v) ^ 2
      ≤ ((1 - 1 / 3) * |u| ^ (1 : ℝ) + 1 / 3 * |v| ^ (1 : ℝ)) ^ (2 / (1 : ℝ)) :=
  pbt_two_point_value_of_core (by norm_num) (by norm_num) le_rfl (by norm_num)
    (pbt_OneVarCore_q_one _) (pbt_OneVarCore_q_one _) u v

-- The same instance at `u = 3`, `v = 0`: both sides equal `4`.
example : ((1 - 1 / 3 : ℝ) * |(3 : ℝ)| ^ (1 : ℝ) + 1 / 3 * |(0 : ℝ)| ^ (1 : ℝ)) ^ (2 / (1 : ℝ))
    = 4 := by
  norm_num

end MathlibExtTest.StatMech.Probability.Hypercontractivity.PBiasedTwoPoint
