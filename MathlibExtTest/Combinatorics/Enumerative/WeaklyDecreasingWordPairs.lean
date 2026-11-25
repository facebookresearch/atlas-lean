/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.WeaklyDecreasingWordPairs

/-! # Tests for non-intersecting pairs of weakly decreasing words -/

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
