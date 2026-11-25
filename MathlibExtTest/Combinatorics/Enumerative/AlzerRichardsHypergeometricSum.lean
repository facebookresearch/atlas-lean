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
