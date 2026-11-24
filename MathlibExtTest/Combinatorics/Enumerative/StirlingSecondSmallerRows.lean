/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingSecondSmallerRows

open Finset MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

-- On the first subdiagonal only the diagonal term at j = 2 survives.
example {k : ℕ} (hk : 1 ≤ k) :
    (Nat.stirlingSecond (k + 1) k : ℤ) = (k + 1).choose 2 := by
  simpa [Nat.sub_add_cancel hk, Nat.stirlingSecond_self] using
    stirlingSecond_mul_sub_eq_sum_choose_alternating hk (le_refl (k + 1))

-- For n = 5 and k = 2 the three terms include an odd-index subtraction.
example : 3 * (Nat.stirlingSecond 5 2 : ℤ) =
    10 * (Nat.stirlingSecond 4 2 : ℤ) - 10 * (Nat.stirlingSecond 3 2 : ℤ) + 5 := by
  calc
    _ = ∑ j ∈ Icc 2 4,
        (Nat.choose 5 j : ℤ) * Nat.stirlingSecond (5 - j + 1) 2 * (-1) ^ j :=
      stirlingSecond_mul_sub_eq_sum_choose_alternating (by decide : 1 ≤ 2) (by decide : 2 + 1 ≤ 5)
    _ = _ := by decide
