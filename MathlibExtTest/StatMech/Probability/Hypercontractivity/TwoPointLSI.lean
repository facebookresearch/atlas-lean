/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.TwoPointLSI

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.TwoPointLSI`

* `tpl_ent` vanishes on constants and `tpl_mean` evaluates at small inputs.
* The log-Sobolev inequality `tpl_lsi` at `p = 1/2`, `g = (1, 0)`, and its weighted form at
  `p = 1/4`.
-/

@[expose] public section

open StatMech.Probability

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.TwoPointLSI

example : tpl_ent (1 / 2) 1 1 = 0 := by simp [tpl_ent]

example : tpl_mean (1 / 4) 2 6 = 3 := by norm_num [tpl_mean]

example : tpl_ent (1 / 2) (1 ^ 2) (0 ^ 2) ≤ (1 - 0) ^ 2 := tpl_lsi (by norm_num) (by norm_num) 1 0

example (g0 g1 : ℝ) : tpl_ent (1 / 4) (g0 ^ 2) (g1 ^ 2)
    ≤ (1 / (1 / 4 * (1 - 1 / 4))) * (1 / 4 * (1 - 1 / 4) * (g0 - g1) ^ 2) :=
  tpl_lsi_weighted (by norm_num) (by norm_num) g0 g1

example : 0 ≤ tpl_ent (1 / 3) 2 5 := tpl_ent_nonneg (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end MathlibExtTest.StatMech.Probability.Hypercontractivity.TwoPointLSI
