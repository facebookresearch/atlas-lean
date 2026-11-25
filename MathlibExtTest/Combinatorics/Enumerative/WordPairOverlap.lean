/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Ring.Rat
import MathlibExt.Combinatorics.Enumerative.WordPairOverlap

/-! # Tests for the overlap statistic on pairs of words -/

open Finset MetaMathlibExt

-- Over one letter every position of the second word is an overlap, for every length and every `q`.
example (n : ℕ) (hn : 1 ≤ n) (q : ℚ) :
    ∑ p : (Fin n → Fin 1) × (Fin n → Fin 1),
      q ^ (univ.filter fun i => p.2 i ∈ univ.image p.1).card = q ^ n := by
  rw [wordPairs_sameLength_overlap_sum 1 n hn q]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [Nat.stirlingSecond_one_right]

-- At `q = 0` only the pairs with no common letter count: over two letters with length two, these
-- are the two pairs of distinct constant words. Direct enumeration agrees with the formula.
example :
    ∑ j ∈ Icc 1 2, (Nat.choose 2 j : ℚ) * j.factorial * Nat.stirlingSecond 2 j *
      (0 * j + (2 - j : ℕ)) ^ 2 = 2 := by
  rw [← wordPairs_sameLength_overlap_sum 2 2 (by decide) 0]
  have h : ∑ p : (Fin 2 → Fin 2) × (Fin 2 → Fin 2),
      0 ^ (univ.filter fun i => p.2 i ∈ univ.image p.1).card = 2 := by
    decide
  exact_mod_cast h

-- Two letters, length two, `q = 3`: each of the two constant first words contributes
-- `(3 + 1) ^ 2`, and each of the two other first words `4 * 3 ^ 2`. Direct enumeration agrees with
-- the formula.
example :
    ∑ j ∈ Icc 1 2, (Nat.choose 2 j : ℚ) * j.factorial * Nat.stirlingSecond 2 j *
      (3 * j + (2 - j : ℕ)) ^ 2 = 104 := by
  rw [← wordPairs_sameLength_overlap_sum 2 2 (by decide) 3]
  have h : ∑ p : (Fin 2 → Fin 2) × (Fin 2 → Fin 2),
      3 ^ (univ.filter fun i => p.2 i ∈ univ.image p.1).card = 104 := by
    decide
  exact_mod_cast h

-- Two letters, length three, `q = 2`: the two constant first words contribute `(2 + 1) ^ 3` each,
-- and the `2! S(3, 2) = 6` others `(2 * 2) ^ 3` each. Direct enumeration agrees with the formula.
example :
    ∑ j ∈ Icc 1 2, (Nat.choose 2 j : ℚ) * j.factorial * Nat.stirlingSecond 3 j *
      (2 * j + (2 - j : ℕ)) ^ 3 = 438 := by
  rw [← wordPairs_sameLength_overlap_sum 2 3 (by decide) 2]
  have h : ∑ p : (Fin 3 → Fin 2) × (Fin 3 → Fin 2),
      2 ^ (univ.filter fun i => p.2 i ∈ univ.image p.1).card = 438 := by
    decide
  exact_mod_cast h

/-! ### Words of two arbitrary lengths -/

open PowerSeries

-- Over one letter every position of the second word is an overlap, and the formula keeps the
-- single term `j = 1`: the coefficient of `x ^ r` in `q x (1 - q x)⁻¹`, for all lengths and `q`.
example (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (q : ℚ) :
    ∑ p : (Fin n → Fin 1) × (Fin r → Fin 1),
      q ^ (univ.filter fun i => p.2 i ∈ univ.image p.1).card =
      coeff r (C q * X * (1 - C q * X)⁻¹) := by
  rw [wordPairs_overlap_sum_eq_coeff 1 n r hn hr q]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [Nat.stirlingSecond_one_right]

-- At equal lengths the coefficient form agrees with the closed form `(q j + k - j) ^ n`.
example (k n : ℕ) (hn : 1 ≤ n) (q : ℚ) :
    ∑ j ∈ Icc 1 k, (k.choose j : ℚ) *
        coeff n (C (q * j + (k - j : ℕ)) * X * (1 - C (q * j + (k - j : ℕ)) * X)⁻¹) *
        (j.factorial * Nat.stirlingSecond n j) =
      ∑ j ∈ Icc 1 k,
        (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j * (q * j + (k - j : ℕ)) ^ n := by
  rw [← wordPairs_overlap_sum_eq_coeff k n n hn hn q, wordPairs_sameLength_overlap_sum k n hn q]

/-- Second words of length one: the coefficient of `x` in `c x (1 - c x)⁻¹` is `c`, so a first
word using `j` letters contributes `q j + k - j`. -/
private theorem sum_overlap_secondLength_one (k n : ℕ) (hn : 1 ≤ n) (q : ℚ) :
    ∑ p : (Fin n → Fin k) × (Fin 1 → Fin k),
        q ^ (univ.filter fun i => p.2 i ∈ univ.image p.1).card =
      ∑ j ∈ Icc 1 k, (k.choose j : ℚ) * (q * j + (k - j : ℕ)) *
        (j.factorial * Nat.stirlingSecond n j) := by
  have h (c : ℚ) : coeff 1 (C c * X * (1 - C c * X)⁻¹) = c := by
    rw [mul_assoc, coeff_C_mul, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_inv]
    simp
  simp only [wordPairs_overlap_sum_eq_coeff k n 1 hn le_rfl q, h]

-- Two letters, first words of length two, second words of length one, `q = 3`: each of the two
-- constant first words contributes `3 + 1` and each of the two others `3 + 3`. Direct enumeration
-- agrees with the formula.
example :
    ∑ j ∈ Icc 1 2, (Nat.choose 2 j : ℚ) * (3 * j + (2 - j : ℕ)) *
      (j.factorial * Nat.stirlingSecond 2 j) = 20 := by
  rw [← sum_overlap_secondLength_one 2 2 (by decide) 3]
  have h : ∑ p : (Fin 2 → Fin 2) × (Fin 1 → Fin 2),
      3 ^ (univ.filter fun i => p.2 i ∈ univ.image p.1).card = 20 := by
    decide
  exact_mod_cast h
