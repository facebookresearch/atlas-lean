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

end MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted
