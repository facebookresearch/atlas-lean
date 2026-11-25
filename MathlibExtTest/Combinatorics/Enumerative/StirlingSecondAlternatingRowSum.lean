/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingSecondAlternatingRowSum

open Finset MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

/-- The first row has no columns in the summation interval. -/
example : (∑ j ∈ Icc 2 1,
    (Nat.stirlingSecond 1 j : ℤ) * (j - 2).factorial * (-1) ^ j) = 0 :=
  sum_stirlingSecond_factorial_alternating (by decide : 1 ≤ 1)

/-- Row four includes a negative term and the first factorial weight greater than one. -/
example : (Nat.stirlingSecond 4 2 : ℤ) - Nat.stirlingSecond 4 3 +
    2 * Nat.stirlingSecond 4 4 = 3 := by
  calc
    _ = ∑ j ∈ Icc 2 4,
        (Nat.stirlingSecond 4 j : ℤ) * (j - 2).factorial * (-1) ^ j := by decide
    _ = 3 := sum_stirlingSecond_factorial_alternating (by decide : 1 ≤ 4)
