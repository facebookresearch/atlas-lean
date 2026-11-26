/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensions

namespace MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

-- The odd numbers satisfy the recurrence with coefficients 2 and -1, giving weight -1.
example (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - i) * (2 * (i : ℚ) + 1) = n + 1 := by
  have h := second_order_recurrence_initial_one_sury_sum (fun i => 2 * (i : ℚ) + 1) 2 (-1)
    (by norm_num) (by norm_num) (fun i => by push_cast; ring) (by norm_num) n
  norm_num [Nat.cast_add] at h
  linear_combination h / 4

-- A negative offset includes signed Fibonacci terms and gives a nontrivial weight of 2.
example (n : ℕ) :
    -fibAtInt ((n : ℤ) + 1) =
      ∑ i ∈ Finset.range (n + 1), (2 : ℚ) ^ (n - i) * fibAtInt ((i : ℤ) - 2) := by
  have hrec (m : ℤ) : fibAtInt (m + 2) = 1 * fibAtInt (m + 1) + 1 * fibAtInt m := by
    simpa only [fibAtInt, Int.cast_add, one_mul, add_comm] using
      congrArg (fun x : ℤ => (x : ℚ)) (Int.fib_add_two m)
  have h0 : fibAtInt 0 = 0 := by decide
  have h1 : fibAtInt 1 = 1 := by decide
  have hk : fibAtInt (-2) = -1 := by decide
  have hprev : fibAtInt (-3) = 2 := by decide
  have h := second_order_recurrence_offset_sury_sum fibAtInt 1 1 (by decide) hrec (-2)
    (by decide) (by decide) n
  norm_num only [h0, h1, hk, hprev, zero_mul, zero_add, one_mul, zero_sub, one_pow,
    neg_div_neg_eq, neg_mul, mul_one, div_one, sub_eq_add_neg] at h ⊢
  exact h

-- A constant sequence has zero initial determinant, even though its offset terms are nonzero.
example (k : ℤ) (n : ℕ) :
    (1 : ℚ) * 1 - 1 * 1 = ((1 * 1 - 1 ^ 2) / 1) *
      ∑ _i ∈ Finset.range (n + 1), (-(1 : ℚ) * 1 / 1) ^ (n - _i) * 1 :=
  second_order_recurrence_offset_sury_sum (fun _ => 1) 0 1 (by decide)
    (fun _ => by simp) k (by decide) (by decide) n

-- Signed Fibonacci and Lucas numbers have opposite signs at the same negative index.
example : fibAtInt (-4) = -3 ∧ lucasAtInt (-4) = 7 := by decide +kernel
example : fibAtInt (-3) = 2 ∧ lucasAtInt (-3) = -4 := by decide +kernel
example : fibAtInt 0 = 0 ∧ lucasAtInt 0 = 2 := by decide +kernel

-- At the smallest step the weight is 1/2 and consecutive summands alternate in sign.
example (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n + i) * (1 / 2 : ℚ) ^ i * lucasAtInt i =
      2 * (1 / 2 : ℚ) ^ (n + 1) * fibAtInt n + 2 * (-1 : ℚ) ^ n := by
  simpa only [Nat.cast_one, one_mul, show lucasAtInt 1 = 1 by decide,
    show fibAtInt 1 = 1 by decide, div_one] using (lucas_step_sury_sum 1 n (by decide)).symm

-- At step four every sign is positive, and the Fibonacci denominator is 3.
example (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (7 / 2 : ℚ) ^ i * lucasAtInt (4 * (i : ℤ)) =
      2 * (7 / 2 : ℚ) ^ (n + 1) * (fibAtInt (4 * (n : ℤ)) / 3) + 2 := by
  simpa only [Nat.cast_ofNat, show lucasAtInt 4 = 7 by decide, show fibAtInt 4 = 3 by decide,
    pow_mul, show (-1 : ℚ) ^ 4 = 1 by decide, one_pow, one_mul, mul_one] using
    (lucas_step_sury_sum 4 n (by decide)).symm

end MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted
