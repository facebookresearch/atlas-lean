/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlzerRichardsHypergeometricSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- For odd m = 5 all three terms contribute, including the term at the cutoff.
example :
    ∑ k ∈ range 3, ((5 - k).choose k : ℂ) * Ring.choose (5 : ℂ) (5 - k) /
      (2 ^ (2 * k) * Ring.choose ((k : ℂ) + 1) k) = 33 / 8 := by
  have h := sum_choose_mul_choose_div_choose_eq_hypergeometric3F2
    (m := 5) (by decide) (p := 1) (x := 0)
    (by intro j hj h; interval_cases j <;> norm_num)
    (by intro j hj h; interval_cases j <;> norm_num)
  norm_num [sum_range_succ, ascPochhammer_succ_eval, Nat.factorial] at h ⊢
  exact h

-- For m = 4, x = -3 is admissible and makes the prefactor vanish.
example :
    ∑ k ∈ range 3, ((4 - k).choose k : ℂ) * Ring.choose (1 : ℂ) (4 - k) /
      (2 ^ (2 * k) * Ring.choose (k : ℂ) k) = 0 := by
  have h := sum_choose_mul_choose_div_choose_eq_hypergeometric3F2
    (m := 4) (by decide) (p := 0) (x := -3)
    (by intro j hj h; interval_cases j <;> norm_num)
    (by intro j hj h; interval_cases j <;> norm_num)
  norm_num [ascPochhammer_succ_eval] at h
  exact h

-- At the even cutoff ν = m / 2, only k = ν survives and the ₂F₁ sum has one term.
example :
    ∑ k ∈ range 2, ((2 - k).choose k : ℂ) * ((2 - 1).choose (2 - k) : ℂ) /
      (2 ^ (2 * k) * Ring.choose ((k : ℂ) + 1) k) = 1 / 8 := by
  have h := sum_choose_mul_choose_div_choose_eq_hypergeometric2F1
    (m := 2) (ν := 1) (by decide) (by decide) (p := 1)
    (by intro j hj hmax; interval_cases j; norm_num)
  convert h using 1
  norm_num [sum_range_succ, ascPochhammer_succ_eval, Nat.factorial]

-- For odd m = 7 and ν = 2, both surviving terms contribute at the admissible p = -4.
example :
    ∑ k ∈ range 4, ((7 - k).choose k : ℂ) * ((7 - 2).choose (7 - k) : ℂ) /
      (2 ^ (2 * k) * Ring.choose ((k : ℂ) - 4) k) = -5 / 48 := by
  have h := sum_choose_mul_choose_div_choose_eq_hypergeometric2F1
    (m := 7) (ν := 2) (by decide) (by decide) (p := -4)
    (by intro j hj hmax; interval_cases j <;> norm_num)
  norm_num [sub_eq_add_neg, sum_range_succ, ascPochhammer_succ_eval, Nat.factorial] at h ⊢
  exact h
