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
