/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ArithmeticProgressionPolynomial
import Mathlib.Tactic.NormNum

/-!
# Boundary cases for the arithmetic-progression polynomial identity
-/

open MetaMathlibExt Polynomial

-- At m = 0 both linear terms on the right contribute at the same exponent.
example : (2 : ℤ[X]) * (X - 1) ^ 2 = 2 * X ^ 2 - 2 * X - 2 * X + 2 := by
  simpa [map_ofNat] using arithProgPoly_mul_sub_one_sq 0 2 0

-- With a = 1 < d = 3, the coefficient -(a - d) is positive and the X² term cancels.
example : (X ^ 2 + 4 * X + 7 : ℤ[X]) * (X - 1) ^ 2 =
    X ^ 4 + 2 * X ^ 3 - 10 * X + 7 := by
  have h := arithProgPoly_mul_sub_one_sq 2 1 3
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_mul, mul_one,
    pow_zero, pow_one, map_one, map_ofNat, map_neg, neg_mul, sub_neg_eq_add] at h
  exact h
