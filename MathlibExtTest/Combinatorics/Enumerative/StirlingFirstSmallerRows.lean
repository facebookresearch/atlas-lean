/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingFirstSmallerRows

open Finset MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

-- On the first subdiagonal the only summand uses the diagonal entry c(k, k).
example {k : ℕ} (hk : 1 ≤ k) :
    (Nat.stirlingFirst (k + 1) k : ℤ) = (k + 1).choose 2 := by
  simpa [Nat.sub_add_cancel hk, Nat.stirlingFirst_self] using
    stirlingFirst_mul_sub_eq_sum_choose_factorial (k := k) (n := k + 1)
      (hk := hk) (hkn := le_rfl)

-- In the first column the upper endpoint is n; the j = 4 and j = 5 terms
-- have factorial weights 2 and 6, respectively.
example : 4 * (Nat.stirlingFirst 5 1 : ℤ) =
    10 * (Nat.stirlingFirst 4 1 : ℤ) + 10 * Nat.stirlingFirst 3 1 +
      10 * Nat.stirlingFirst 2 1 + 6 := by
  calc
    _ = ∑ j ∈ Icc 2 5,
        (Nat.choose 5 j : ℤ) * Nat.stirlingFirst (5 - j + 1) 1 * (j - 2).factorial :=
      stirlingFirst_mul_sub_eq_sum_choose_factorial (k := 1) (n := 5)
        (hk := by decide) (hkn := by decide)
    _ = _ := by decide
