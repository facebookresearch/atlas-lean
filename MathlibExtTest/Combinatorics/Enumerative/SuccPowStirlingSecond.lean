/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SuccPowStirlingSecond

open Finset MetaMathlibExt

-- At exponent zero only the partition into one block contributes.
example (k : ℕ) :
    ∑ j ∈ range (k + 1), k.choose j * j.factorial * Nat.stirlingSecond 1 (j + 1) = 1 := by
  simpa using (succ_pow_eq_sum_stirlingSecond k 0).symm

-- An upper bound of zero leaves exactly the one-block term.
example (ℓ : ℕ) : Nat.stirlingSecond (ℓ + 1) 1 = 1 := by
  simpa using (succ_pow_eq_sum_stirlingSecond 0 ℓ).symm

-- At base three, the top term has coefficient 2! even when the exponent exceeds two.
example (ℓ : ℕ) :
    3 ^ ℓ = 1 + 2 * Nat.stirlingSecond (ℓ + 1) 2 + 2 * Nat.stirlingSecond (ℓ + 1) 3 := by
  simpa [sum_range_succ, Nat.stirlingSecond_one_right, Nat.factorial] using
    succ_pow_eq_sum_stirlingSecond 2 ℓ
