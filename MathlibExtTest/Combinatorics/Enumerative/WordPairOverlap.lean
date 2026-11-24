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
