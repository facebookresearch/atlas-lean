/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeProduct

open MetaMathlibExt

-- The bound is attained when the crossing prime is already in the singleton set.
example : 3 ≤ 3 := by
  simpa only [Finset.prod_singleton] using
    le_two_mul_prod_sub_one_sub_one_of_two_lt {3} (by decide) (by norm_num) 3
      (by decide) (by decide) (by norm_num)

-- For the set {3, 5}, the starting product is 15/8 and the bound is 15.
example (q : ℕ) (hq : q.Prime) (hodd : Odd q)
    (h : 2 < (15 / 8 : ℚ) * ((q : ℚ) / ((q : ℚ) - 1))) : q ≤ 15 := by
  have hprod : (∏ p ∈ ({3, 5} : Finset ℕ), (p : ℚ) / ((p : ℚ) - 1)) = 15 / 8 := by
    norm_num [Finset.prod_insert]
  have hbound := le_two_mul_prod_sub_one_sub_one_of_two_lt {3, 5} (by decide)
    (by rw [hprod]; norm_num) q hq hodd (by rwa [hprod])
  norm_num [Finset.prod_insert] at hbound
  exact hbound
