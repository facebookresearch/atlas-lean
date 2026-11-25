/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.TriangularRepdigits

open MathlibExt.NumberTheory.Digits.TriangularRepdigitsWanted

-- The largest listed repdigit has a positive triangular index.
example : ∃ n : ℕ, 1 ≤ n ∧ 2 * 666 = n * (n + 1) := by
  have hm : 666 ∈ ({1, 3, 6, 55, 66, 666} : Set ℕ) := by decide
  rw [← triangular_numbers_single_repeated_digit] at hm
  exact hm.1

-- Appending a fourth six gives a repdigit with no such index.
example (n : ℕ) (hn : 1 ≤ n) : 2 * 6666 ≠ n * (n + 1) := by
  intro he
  have hm : 6666 ∈ ({1, 3, 6, 55, 66, 666} : Set ℕ) := by
    rw [← triangular_numbers_single_repeated_digit]
    exact ⟨⟨n, hn, he⟩, 6, by decide +kernel⟩
  exact (by decide : 6666 ∉ ({1, 3, 6, 55, 66, 666} : Set ℕ)) hm
