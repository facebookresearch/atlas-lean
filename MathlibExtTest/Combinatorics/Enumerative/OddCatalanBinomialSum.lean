/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.OddCatalanBinomialSum

open Finset MetaMathlibExt

-- At degree zero the interval is empty.
example :
    ∑ k ∈ Icc 1 ((0 + 1) / 2), (Nat.choose 0 (2 * k - 1) : ℚ) * 2 ^ 0 / 2 ^ (2 * k) *
      catalan k = 0 := by
  rw [sum_choose_odd_two_pow_mul_catalan]
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

-- In even degree four, both even Touchard rows have the same cutoff.
example :
    ∑ k ∈ Icc 1 ((4 + 1) / 2), (Nat.choose 4 (2 * k - 1) : ℚ) * 2 ^ 4 / 2 ^ (2 * k) *
      catalan k = 24 := by
  rw [sum_choose_odd_two_pow_mul_catalan]
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

-- In odd degree three, the new endpoint `k = 2` contributes `C₂ / 2 = 1`.
example :
    ∑ k ∈ Icc 1 ((3 + 1) / 2), (Nat.choose 3 (2 * k - 1) : ℚ) * 2 ^ 3 / 2 ^ (2 * k) *
      catalan k = 7 := by
  rw [sum_choose_odd_two_pow_mul_catalan]
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
