/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingSecondHigherColumns

open Finset MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

-- At n = k + 1 the only summand comes from the diagonal.
example (k : ℕ) (hk : 1 ≤ k) :
    (Nat.stirlingSecond (k + 1) k : ℤ) = (k + 1).choose 2 := by
  simpa [Nat.stirlingSecond_self, show k + 2 - 1 = k + 1 by omega] using
    stirlingSecond_mul_sub_eq_sum_factorial_negChoose hk (le_refl (k + 1))

-- In row five the first negative weight and the factor 2! both contribute.
example : 3 * (Nat.stirlingSecond 5 2 : ℤ) = 75 - 40 + 10 := by
  calc
    _ = ∑ j ∈ Icc 2 4, ((j - 2).factorial : ℤ) *
          ((-1 : ℤ) ^ j * ((2 + j - 1).choose j : ℤ)) * Nat.stirlingSecond 5 (2 + j - 1) :=
      stirlingSecond_mul_sub_eq_sum_factorial_negChoose (by decide : 1 ≤ 2) (by decide : 2 + 1 ≤ 5)
    _ = _ := by decide
