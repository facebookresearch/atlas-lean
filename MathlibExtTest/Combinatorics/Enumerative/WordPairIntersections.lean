/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.WordPairIntersections

/-! # Tests for non-intersecting word pairs -/

open Finset PowerSeries MetaMathlibExt

-- A one-letter alphabet forces an intersection for any two positive lengths.
example (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ((univ : Finset ((Fin n → Fin 1) × (Fin r → Fin 1))).filter fun p =>
      Disjoint (univ.image p.1) (univ.image p.2)).card = 0 := by
  have h := (nonIntersectingWordPairs_card_eq_coeff 1 n r hn hr).2
  rw [show Icc 1 (1 - 1 : ℕ) = ∅ by decide, sum_empty] at h
  exact_mod_cast h

-- For lengths two and one on three letters, the first word can use either one or two letters.
-- Direct enumeration checks the product of generating-function coefficients.
example :
    (∑ j ∈ Icc 1 (3 - 1), (Nat.choose 3 j : ℚ) *
      coeff 2 ((j.factorial : ℚ⟦X⟧) * X ^ j * (∏ i ∈ Icc 1 j, (1 - (i : ℚ⟦X⟧) * X))⁻¹) *
      coeff 1 (((3 - j : ℕ) : ℚ⟦X⟧) * X * (1 - ((3 - j : ℕ) : ℚ⟦X⟧) * X)⁻¹)) = 12 := by
  rw [← (nonIntersectingWordPairs_card_eq_coeff 3 2 1 (by decide) (by decide)).1]
  exact_mod_cast (show ((univ : Finset ((Fin 2 → Fin 3) × (Fin 1 → Fin 3))).filter fun p =>
    Disjoint (univ.image p.1) (univ.image p.2)).card = 12 by decide)

-- An empty alphabet admits no pair of words of positive length.
example (n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset ((Fin n → Fin 0) × (Fin n → Fin 0))).filter fun p =>
      Disjoint (univ.image p.1) (univ.image p.2)).card = 0 := by
  rw [nonIntersectingWordPairs_sameLength_card 0 n hn]
  rfl

-- At length two over three letters, the first word can use one or two letters.
-- Direct enumeration counts twelve disjoint pairs in the first case and six in the second.
example :
    ∑ j ∈ Icc 1 (3 - 1), (Nat.choose 3 j) * j.factorial * Nat.stirlingSecond 2 j *
      (3 - j) ^ 2 = 18 := by
  rw [← nonIntersectingWordPairs_sameLength_card 3 2 (by decide)]
  decide

-- The series excludes the unique pair of empty words.
example (k : ℕ) :
    coeff 0 (PowerSeries.mk fun n => ∑ j ∈ Icc 1 (k - 1),
      (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j * ((k - j : ℕ) : ℚ) ^ n) = 0 := by
  rw [← nonIntersectingWordPairs_sameLength_generatingFunction, coeff_mk, ite_eq_left rfl]

-- Over three letters, there are six ordered pairs of distinct single letters.
example :
    coeff 1 (PowerSeries.mk fun n => ∑ j ∈ Icc 1 (3 - 1),
      (Nat.choose 3 j : ℚ) * j.factorial * Nat.stirlingSecond n j * ((3 - j : ℕ) : ℚ) ^ n) = 6 := by
  rw [← nonIntersectingWordPairs_sameLength_generatingFunction, coeff_mk, ite_eq_right (by decide)]
  exact_mod_cast (show ((univ : Finset ((Fin 1 → Fin 3) × (Fin 1 → Fin 3))).filter fun p =>
    Disjoint (univ.image p.1) (univ.image p.2)).card = 6 by decide)
