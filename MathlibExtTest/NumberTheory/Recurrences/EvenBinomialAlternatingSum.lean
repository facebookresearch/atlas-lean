/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.EvenBinomialAlternatingSum
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- The original API takes a strict bound, with `n`, `k`, and `hk` in that order.
example : ∀ {n k : ℕ}, k < n / 2 →
    (n.choose (2 * k) : ℚ) = n * ∑ i ∈ Icc k (n / 2),
      (-1) ^ (i - k) / ((n : ℚ) - i) * (2 : ℚ) ^ ((n : ℤ) - 2 * i - 1) *
        ((n - i).choose i : ℚ) * (i.choose k : ℚ) := by
  intro n k hk
  exact choose_two_mul_eq_alternating_sum (n := n) (k := k) (hk := hk)

-- The last admissible `k` for this even row. Its final summand uses `2 ^ (-1 : ℤ)`.
example :
    (6 : ℚ) * ∑ i ∈ Icc (2 : ℕ) (6 / 2),
      (-1) ^ (i - 2) / ((6 : ℚ) - i) * (2 : ℚ) ^ ((6 : ℤ) - 2 * i - 1) *
        ((6 - i).choose i : ℚ) * (i.choose 2 : ℚ) = 15 := by
  rw [show Icc (2 : ℕ) (6 / 2) = {2, 3} by decide]
  norm_num [sum_insert, Nat.choose]

-- In an odd row the final exponent is zero. Include the constant coefficient (`k = 0`).
example :
    (7 : ℚ) * ∑ i ∈ Icc (0 : ℕ) (7 / 2),
      (-1) ^ (i - 0) / ((7 : ℚ) - i) * (2 : ℚ) ^ ((7 : ℤ) - 2 * i - 1) *
        ((7 - i).choose i : ℚ) * (i.choose 0 : ℚ) = 1 := by
  rw [show Icc (0 : ℕ) (7 / 2) = {0, 1, 2, 3} by decide]
  norm_num [sum_insert, Nat.choose]
