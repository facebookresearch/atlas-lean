/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GFPLucasSumChoose
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

open Polynomial Finset

private theorem lucas_parameters : (6 : ℤ[X]) = C (2 : ℤ) * C (3 : ℤ) := by
  norm_num [← C_mul]

-- At n = 1, only the i = 0 term occurs.
example : C (2 : ℤ) * generalizedFibonacciPolynomial (C 1) (C 3) 6 1 1 = 6 := by
  rw [gfp_lucas_eq_sum_choose (α := 2) (p₀ := 1) (hα := by decide) lucas_parameters 1
    (hn := by decide)]
  norm_num [sum_range_succ, Nat.choose]

-- At n = 2, the even endpoint contributes 2 with no factor of d.
example : C (2 : ℤ) * generalizedFibonacciPolynomial (C 1) (C 3) 6 1 2 = 38 := by
  rw [gfp_lucas_eq_sum_choose (α := 2) (p₀ := 1) (hα := by decide) lucas_parameters 1
    (hn := by decide)]
  norm_num [sum_range_succ, Nat.choose]

-- At n = 3, the final term has exponent one and coefficient three.
example : C (2 : ℤ) * generalizedFibonacciPolynomial (C 1) (C 3) 6 1 3 = 234 := by
  rw [gfp_lucas_eq_sum_choose (α := 2) (p₀ := 1) (hα := by decide) lucas_parameters 1
    (hn := by decide)]
  norm_num [sum_range_succ, Nat.choose]

end MetaMathlibExt
