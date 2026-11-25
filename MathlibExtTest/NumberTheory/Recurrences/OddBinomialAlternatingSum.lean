/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.OddBinomialAlternatingSum

open Finset MetaMathlibExt

-- An odd row with three terms, including the exponent-zero term at the inclusive upper endpoint.
example :
    (∑ i ∈ Icc (1 : ℕ) ((7 - 1) / 2),
      (-1 : ℤ) ^ (i - 1) * 2 ^ (7 - 2 * i - 1) * ((7 - i - 1).choose i : ℤ) * (i.choose 1 : ℤ)) =
      35 := by
  rw [← choose_two_mul_add_one_eq_alternating_sum (n := 7) (k := 1) (by decide)]
  decide

-- In an even row, `k = 1` is the last admissible index and the final term has exponent one.
example :
    (∑ i ∈ Icc (1 : ℕ) ((6 - 1) / 2),
      (-1 : ℤ) ^ (i - 1) * 2 ^ (6 - 2 * i - 1) * ((6 - i - 1).choose i : ℤ) * (i.choose 1 : ℤ)) =
      20 := by
  rw [← choose_two_mul_add_one_eq_alternating_sum (n := 6) (k := 1) (by decide)]
  decide
