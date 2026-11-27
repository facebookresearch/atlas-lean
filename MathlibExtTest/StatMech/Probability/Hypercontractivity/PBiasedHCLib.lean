/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.PBiasedHCLib

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.PBiasedHCLib`

* The residue predicate `hclib_BracketResidue` holds at `q = 3` and `q = 4`.
* The two-point hypercontractive inequality `hclib_two_point_forward` at `q = 3`, `a = 1`, `b = 1/2`.
* `hclib_forward_core_of_bracket` at `q = 4` with the residue discharged; `hclib_forward_scalar` at
  `ρ = 1` (so `q = 2`).
-/

@[expose] public section

open StatMech.Probability

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.PBiasedHCLib

example : hclib_BracketResidue 3 := hclib_BracketResidue_of_le_four (by norm_num) (by norm_num)

example : ((|(1 : ℝ) + 1 / 2| ^ (3 : ℝ) + |(1 : ℝ) - 1 / 2| ^ (3 : ℝ)) / 2) ^ (2 / (3 : ℝ))
    ≤ 1 ^ 2 + (3 - 1) * (1 / 2) ^ 2 :=
  hclib_two_point_forward (by norm_num) (by norm_num) 1 (1 / 2)

example (t : ℝ) (ht : |t| ≤ 1) :
    ((1 + t) ^ (4 : ℝ) + (1 - t) ^ (4 : ℝ)) / 2 ≤ (1 + (4 - 1) * t ^ 2) ^ ((4 : ℝ) / 2) :=
  hclib_forward_core_of_bracket (by norm_num)
    (hclib_BracketResidue_of_le_four (by norm_num) le_rfl) ht

example (a b : ℝ) :
    ((|a + 1 * b| ^ (1 + 1 / (1 : ℝ) ^ 2) + |a - 1 * b| ^ (1 + 1 / (1 : ℝ) ^ 2)) / 2)
      ^ (2 / (1 + 1 / (1 : ℝ) ^ 2)) ≤ a ^ 2 + b ^ 2 :=
  hclib_forward_scalar one_pos le_rfl (by norm_num) a b

end MathlibExtTest.StatMech.Probability.Hypercontractivity.PBiasedHCLib
