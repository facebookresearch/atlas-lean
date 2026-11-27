/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingFirstHigherColumns

open MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

/-- At the nearest higher row the sum has only its diagonal term. -/
example (k : ℕ) (hk : 1 ≤ k) :
    (Nat.stirlingFirst (k + 1) k : ℤ) = (k + 1).choose 2 := by
  simpa [Nat.stirlingFirst_self, show k + 2 - 1 = k + 1 by omega] using
    stirlingFirst_mul_sub_eq_sum_stirlingFirst_choose hk (le_refl (k + 1))

/-- In row five, columns three through five contribute 105, 40, and 5. -/
example : 3 * (Nat.stirlingFirst 5 2 : ℤ) = 105 + 40 + 5 := by
  calc
    _ = ∑ j ∈ Finset.Icc 2 4,
          (Nat.stirlingFirst 5 (2 + j - 1) : ℤ) * (2 + j - 1).choose j :=
      stirlingFirst_mul_sub_eq_sum_stirlingFirst_choose (by decide : 1 ≤ 2) (by decide : 2 + 1 ≤ 5)
    _ = _ := by decide
