/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Digits.Defs

/-!
# A classification of the decimal Kaprekar numbers (statement)

Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly 62
(2024), Article iwasaki06162024-ASrev2.

`D_n` is the set of `n`-digit strings of decimal digits (leading zeros allowed), i.e. the
numbers `α < 10^n` written with exactly `n` digits. The Kaprekar transformation sends
`α ∈ D_n` to `α_M - α_L`, where `α_M` and `α_L` arrange the `n` digits of `α` in descending and
ascending order; it depends only on the multiset of digits, and a nonzero `α` with
`f(α) = α` is a Kaprekar number. The value depends on `n`: `495` is a Kaprekar number in `D_3`,
but in `D_4` it is the string `0495` and is sent to `9540 - 0459 = 9081`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- `α_M - α_L` for a list of decimal digits: the number whose digits are those of `l` in
descending order minus the number with the same digits in ascending order (`Nat.ofDigits` is
little-endian, so an ascending list gives the descending numeral).

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Definition 1.1. -/
public def kaprekarDiff (l : List ℕ) : ℕ :=
  Nat.ofDigits 10 (List.insertionSort (· ≤ ·) l) - Nat.ofDigits 10 (List.insertionSort (· ≥ ·) l)

/-- The Kaprekar transformation on `D_n`: `α < 10^n` is read as the `n`-digit string of its
decimal digits padded with leading zeros, and sent to `α_M - α_L`.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Definition 1.1. -/
public def kaprekarMap (n α : ℕ) : ℕ :=
  kaprekarDiff (Nat.digits 10 α ++ List.replicate (n - (Nat.digits 10 α).length) 0)

/-- Characteristic value: `f(6174) = 7641 - 1467 = 6174` in `D_4`.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Section 1. -/
public theorem kaprekarMap_four_6174 : kaprekarMap 4 6174 = 6174 := by
  norm_num [kaprekarMap, kaprekarDiff, List.insertionSort_cons, List.orderedInsert_cons,
    Nat.ofDigits_cons]

/-- Characteristic value: `495` is fixed in `D_3`.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Section 1. -/
public theorem kaprekarMap_three_495 : kaprekarMap 3 495 = 495 := by
  norm_num [kaprekarMap, kaprekarDiff, List.insertionSort_cons, List.orderedInsert_cons,
    Nat.ofDigits_cons]

/-- Characteristic value: in `D_4`, `495` is the string `0495` and `f(0495) = 9540 - 0459`.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Definition 1.1. -/
public theorem kaprekarMap_four_495 : kaprekarMap 4 495 = 9081 := by
  norm_num [kaprekarMap, kaprekarDiff, List.insertionSort_cons, List.orderedInsert_cons,
    Nat.ofDigits_cons]

/-- Theorem 3.1: for `n ≥ 3`, a nonzero `α ∈ D_n` is a Kaprekar number if and only if it lies in
one of the sets `T_1, …, T_5` of Definition 2.1, i.e. it equals `f(s)` for a digit string `s` of
length `n` of one of the forms (`x ≥ 1`, `y ≥ 0`, blocks repeated as indicated)
`(495)^{x_1}`; `6174 (36)^{y_2}`; `(123456789)^{x_3} (36)^{y_3}`;
`(123456789)^{x_{4,1}} (36)^{x_{4,2}} (495)^{2x_{4,2}} (27)^{3x_{4,2}}`;
`(124578)^{x_{5,1}} (09)^{x_{5,2}} (123456789)^{y_{5,1}} (36)^{y_{5,2}}`.
Membership of `α ∈ D_n` in `T_i` is read in `D`, where strings of different lengths are
different elements, so the witness string has length `n` (as numbers, `495 ∈ T_1` is below
`10^4` but is not a Kaprekar number of `D_4`). The record's "digit `α`" is the number `α`.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Theorem 3.1. -/
public theorem_wanted kaprekarMap_fixed_iff {n α : ℕ} (hn : 3 ≤ n) (hα : α < 10 ^ n)
    (hα0 : α ≠ 0) :
    kaprekarMap n α = α ↔
      ∃ s : List ℕ, s.length = n ∧ kaprekarDiff s = α ∧
        ((∃ x, 1 ≤ x ∧ s = (List.replicate x [4, 9, 5]).flatten) ∨
          (∃ y, s = [6, 1, 7, 4] ++ (List.replicate y [3, 6]).flatten) ∨
          (∃ x y, 1 ≤ x ∧ s = (List.replicate x [1, 2, 3, 4, 5, 6, 7, 8, 9]).flatten ++
            (List.replicate y [3, 6]).flatten) ∨
          (∃ x₁ x₂, 1 ≤ x₁ ∧ 1 ≤ x₂ ∧
            s = (List.replicate x₁ [1, 2, 3, 4, 5, 6, 7, 8, 9]).flatten ++
              (List.replicate x₂ [3, 6]).flatten ++ (List.replicate (2 * x₂) [4, 9, 5]).flatten ++
              (List.replicate (3 * x₂) [2, 7]).flatten) ∨
          (∃ x₁ x₂ y₁ y₂, 1 ≤ x₁ ∧ 1 ≤ x₂ ∧
            s = (List.replicate x₁ [1, 2, 4, 5, 7, 8]).flatten ++
              (List.replicate x₂ [0, 9]).flatten ++
              (List.replicate y₁ [1, 2, 3, 4, 5, 6, 7, 8, 9]).flatten ++
              (List.replicate y₂ [3, 6]).flatten))

end

end MetaMathlibExt
