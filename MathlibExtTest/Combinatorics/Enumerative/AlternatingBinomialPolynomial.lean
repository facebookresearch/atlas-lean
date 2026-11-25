/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPolynomial
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- Degree zero gives the constant polynomial, including at `x = 1`.
example (x : ℂ) :
    ∑ k ∈ range (0 + 1),
      (-1) ^ (0 - k) * (Nat.choose 0 k : ℂ) * 2 ^ k / (k + 1) * (1 - x) ^ (0 - k) = 1 := by
  rw [sum_choose_two_pow_div_succ_one_sub_pow]
  simp

-- In odd degree, the last term has exponent one.
example (x : ℂ) :
    ∑ k ∈ range (3 + 1),
      (-1) ^ (3 - k) * (Nat.choose 3 k : ℂ) * 2 ^ k / (k + 1) * (1 - x) ^ (3 - k) =
      x ^ 3 + x := by
  rw [sum_choose_two_pow_div_succ_one_sub_pow]
  norm_num [sum_range_succ, Nat.choose]

-- In even degree, the constant term survives; `I` also makes the quadratic term negative.
example :
    ∑ k ∈ range (4 + 1),
      (-1) ^ (4 - k) * (Nat.choose 4 k : ℂ) * 2 ^ k / (k + 1) * (1 - Complex.I) ^ (4 - k) =
      -4 / 5 := by
  rw [sum_choose_two_pow_div_succ_one_sub_pow]
  norm_num [sum_range_succ, Nat.choose, pow_succ, Complex.I_mul_I]
