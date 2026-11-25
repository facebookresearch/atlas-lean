/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.WeaklyDecreasingWordPairs

/-! # Tests for intersections in pairs of weakly decreasing words -/

open Finset MetaMathlibExt

-- A one-letter alphabet forces a common letter, and the sum over `Icc 1 0` is empty.
example (n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset ((Fin n → Fin 1) × (Fin n → Fin 1))).filter fun p => Antitone p.1 ∧
      Antitone p.2 ∧ Disjoint (univ.image p.1) (univ.image p.2)).card = 0 := by
  rw [weaklyDecreasingNonIntersectingPairs_sameLength_card 1 n hn]
  simp

-- Over two letters, for every length, the only pairs are the two pairs of distinct constant words.
example (n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset ((Fin n → Fin 2) × (Fin n → Fin 2))).filter fun p => Antitone p.1 ∧
      Antitone p.2 ∧ Disjoint (univ.image p.1) (univ.image p.2)).card = 2 := by
  rw [weaklyDecreasingNonIntersectingPairs_sameLength_card 2 n hn]
  simp

-- On three letters with length two, the first word uses one letter (nine pairs) or two letters
-- (three pairs). Direct enumeration agrees with the formula.
example :
    ∑ j ∈ Icc 1 (3 - 1), Nat.choose 3 j * (2 - 1).choose (j - 1) * (2 + 3 - j - 1).choose 2 =
      12 := by
  rw [← weaklyDecreasingNonIntersectingPairs_sameLength_card 3 2 (by decide)]
  decide

-- For four letters and length three the formula gives `40 + 48 + 4`.
example :
    ((univ : Finset ((Fin 3 → Fin 4) × (Fin 3 → Fin 4))).filter fun p => Antitone p.1 ∧
      Antitone p.2 ∧ Disjoint (univ.image p.1) (univ.image p.2)).card = 92 := by
  rw [weaklyDecreasingNonIntersectingPairs_sameLength_card 4 3 (by decide)]
  decide

open PowerSeries

-- With one letter, the full-support term is the only term. Both positions contribute to the weight.
example (q : ℚ) :
    coeff 1 (X * (1 - X)⁻¹ : ℚ⟦X⟧) * coeff 2 (-1 + (1 - C q * X)⁻¹) = q ^ 2 := by
  have h := (weaklyDecreasingPairs_overlap_sum_eq_coeff 1 1 2 (by decide) (by decide) q).2
  have hmem (u : Fin 1 → Fin 1) (a : Fin 1) : a ∈ univ.image u :=
    mem_image.2 ⟨0, mem_univ _, Subsingleton.elim _ _⟩
  simp only [hmem, filter_true, card_univ, Fintype.card_fin] at h
  simpa [Antitone] using h.symm

-- At lengths two over two letters, two pairs have overlap zero, two have one, and five have two.
example :
    ∑ j ∈ Icc 1 2, (Nat.choose 2 j : ℚ) * coeff 2 (X ^ j * ((1 - X) ^ j)⁻¹ : ℚ⟦X⟧) *
      coeff 2 ((((1 - X) ^ (2 - j))⁻¹ - 1 + ((1 - X) ^ (2 - j))⁻¹ *
        PowerSeries.mk fun m => if m = 0 then 0 else ((m + j - 1).choose m : ℚ) * 2 ^ m) :
          ℚ⟦X⟧) = 26 := by
  rw [← (weaklyDecreasingPairs_overlap_sum_eq_coeff 2 2 2 (by decide) (by decide) 2).1]
  have h : ∑ p ∈ ((univ : Finset ((Fin 2 → Fin 2) × (Fin 2 → Fin 2))).filter fun p =>
      Antitone p.1 ∧ Antitone p.2), (2 : ℕ) ^ (univ.filter fun i => p.2 i ∈ univ.image p.1).card =
        26 := by decide
  exact_mod_cast h
