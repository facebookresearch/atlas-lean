/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.BinomialPolynomialRescale

open Finset MetaMathlibExt

-- The degree-zero polynomial is constant at every complex argument.
example (x : ℂ) :
    ∑ k ∈ range (0 + 1),
        (Nat.choose 0 k : ℂ) * 2 ^ k / (k + 1) * (1 - x) ^ k * x ^ (0 - k) = 1 := by
  rw [sum_choose_two_pow_div_succ_one_sub_pow_mul_pow]
  simp

-- The endpoint `x = 1` is not covered by the inverse substitution.
example :
    ∑ k ∈ range (4 + 1),
        (Nat.choose 4 k : ℂ) * 2 ^ k / (k + 1) * (1 - 1) ^ k * (1 : ℂ) ^ (4 - k) = 1 := by
  rw [sum_choose_two_pow_div_succ_one_sub_pow_mul_pow]
  norm_num [sum_range_succ, Nat.choose]

-- For `x = 1/2` the even terms in degree two give `1 + (1/2)² / 3`.
example :
    ∑ k ∈ range (2 + 1),
        (Nat.choose 2 k : ℂ) * 2 ^ k / (k + 1) * (1 - 1 / 2) ^ k * (1 / 2 : ℂ) ^ (2 - k) =
      13 / 12 := by
  rw [sum_choose_two_pow_div_succ_one_sub_pow_mul_pow]
  norm_num [sum_range_succ, Nat.choose]
