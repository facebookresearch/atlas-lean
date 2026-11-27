/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingFirstShiftedExpansion

open Finset MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

/-- On the diagonal, including row zero, the singleton term has both exponents zero. -/
example (n : ℕ) :
    (Nat.stirlingFirst (n + 1) (n + 1) : ℤ) = Nat.stirlingFirst n n := by
  simpa only [Icc_self, sum_singleton, Nat.choose_self, Nat.cast_one, Nat.sub_self,
    pow_zero, mul_one] using stirlingFirst_succ_eq_sum_choose_pow (le_refl n)

/-- The expansion for two cycles on four elements has two positive terms and one negative term. -/
example : (Nat.stirlingFirst 4 2 : ℤ) = 2 - 18 + 27 := by
  calc
    _ = ∑ k ∈ Icc 1 3, (Nat.stirlingFirst 3 k : ℤ) * k.choose 1 *
          (-1 : ℤ) ^ (3 - k) * (3 : ℤ) ^ (k - 1) :=
      stirlingFirst_succ_eq_sum_choose_pow (by decide : 1 ≤ 3)
    _ = _ := by decide
