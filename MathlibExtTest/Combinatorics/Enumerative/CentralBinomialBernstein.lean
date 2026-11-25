/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CentralBinomialBernstein
import Mathlib.Tactic.NormNum

open Finset

namespace MetaMathlibExt

-- At degree zero the Bernstein sum is one even at the endpoint x = 0.
example :
    ∑ k ∈ range (0 + 1),
        (Nat.choose 0 k : ℂ) / 2 ^ k * ((2 * k).choose k : ℂ) *
          (1 - 0) ^ k * (0 : ℂ) ^ (0 - k) = 1 := by
  rw [sum_choose_centralBinom_one_sub_pow_mul_pow]
  simp

-- At odd degree three the expansion stops at the quadratic term.
example (x : ℂ) :
    ∑ k ∈ range (3 + 1),
        (Nat.choose 3 k : ℂ) / 2 ^ k * ((2 * k).choose k : ℂ) * (1 - x) ^ k * x ^ (3 - k) =
      1 + 3 / 2 * (1 - x) ^ 2 := by
  rw [sum_choose_centralBinom_one_sub_pow_mul_pow]
  norm_num [sum_range_succ, Nat.choose]

end MetaMathlibExt
