/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.PBiasedIntegralHC

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.PBiasedIntegralHC`

* `pih_m` and `pih_V` computed at small inputs, and `pih_g_eq`;
* `pih_KEY` proved for `q = 1` (`pih_KEY_q_one`) and fed to `pih_core_of_KEY` at `p = 1/3`;
* `pih_two_point_value_of_KEY` instantiated at `p = 1/3`, `q = 1`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.PBiasedIntegralHC

open _root_.StatMech.Probability

-- `pih_m` is the `p`-mean of `1` and `z`.
example : pih_m (1 / 4) 5 = 2 := by norm_num [pih_m]

-- `pih_V` at `p = 1/2`, `q = 2`, `z = 3`: `4 * 1 * 1/4 * 1/4 * 4 = 1`.
example : pih_V (1 / 2) 2 3 = 1 := by norm_num [pih_V]

-- `pbt_g = pih_m^2 + pih_V` at a concrete point.
example : pbt_g (1 / 2) 2 3 = pih_m (1 / 2) 3 ^ 2 + pih_V (1 / 2) 2 3 := pih_g_eq _ _ _

-- `pih_core_of_KEY` with every hypothesis instantiated (`p = 1/3`, `q = 1`).
example : pbt_OneVarCore (1 / 3) 1 :=
  pih_core_of_KEY (by norm_num) (by norm_num) le_rfl (by norm_num) (pih_KEY_q_one _)

-- `pih_two_point_value_of_KEY` with every hypothesis instantiated (`p = 1/3`, `q = 1`).
example (u v : ℝ) :
    ((1 - 1 / 3) * u + 1 / 3 * v) ^ 2 + (1 - 1) * 4 * (1 / 3) ^ 2 * (1 - 1 / 3) ^ 2 * (u - v) ^ 2
      ≤ ((1 - 1 / 3) * |u| ^ (1 : ℝ) + 1 / 3 * |v| ^ (1 : ℝ)) ^ (2 / (1 : ℝ)) :=
  pih_two_point_value_of_KEY (by norm_num) (by norm_num) le_rfl (by norm_num)
    (pih_KEY_q_one _) (pih_KEY_q_one _) u v

end MathlibExtTest.StatMech.Probability.Hypercontractivity.PBiasedIntegralHC
