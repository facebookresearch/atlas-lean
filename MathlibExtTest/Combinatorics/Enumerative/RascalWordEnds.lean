/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RascalWordEnds

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

-- With two ones and two zeros free, one of the six middle words has two ascents.
example : (Nat.card { w : RascalWord 1 3 6 //
    (∀ x ∈ w.1.take 1, x = 1) ∧ (∀ x ∈ w.1.drop 5, x = 0) } : ℤ) = 5 := by
  exact card_prefixOnes_suffixZeros 6 3 1 1 (by decide) (by decide)

-- Fixing all the ones forces the decreasing word for every admissible suffix length.
example (n k u : ℕ) (hu : k + u ≤ n) :
    Nat.card { w : RascalWord 1 k n //
      (∀ x ∈ w.1.take k, x = 1) ∧ (∀ x ∈ w.1.drop (n - u), x = 0) } = 1 := by
  simpa [rascalZ] using card_prefixOnes_suffixZeros n k k u le_rfl hu

-- Fixing all the zeros also leaves one word, including when its length is zero.
example (k z : ℕ) : Nat.card { w : RascalWord 1 k (k + z) //
    ∀ x ∈ w.1.drop k, x = 0 } = 1 := by
  simpa [rascalZ] using card_prefixOnes_suffixZeros (k + z) k 0 z (by omega) le_rfl

-- The empty word and the all-zero and all-one words each contribute once.
example : rascalGenZ 1 0 0 = 1 := by
  rw [← rascalZ_eq_rascalGenZ_one]
  decide

example : rascalGenZ 1 4 0 = 1 := by
  rw [← rascalZ_eq_rascalGenZ_one]
  decide

example : rascalGenZ 1 4 4 = 1 := by
  rw [← rascalZ_eq_rascalGenZ_one]
  decide

-- Of the six words with two ones and two zeros, only 0101 has two ascents.
example : rascalGenZ 1 4 2 = 5 := by
  rw [← rascalZ_eq_rascalGenZ_one]
  decide

-- A negative length, a negative weight, and a weight above the length are out of range.
example : rascalGenZ 1 (-1) 0 = 0 := by
  rw [← rascalZ_eq_rascalGenZ_one]
  decide

example : rascalGenZ 1 4 (-1) = 0 := by
  rw [← rascalZ_eq_rascalGenZ_one]
  decide

example : rascalGenZ 1 4 5 = 0 := by
  rw [← rascalZ_eq_rascalGenZ_one]
  decide

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
