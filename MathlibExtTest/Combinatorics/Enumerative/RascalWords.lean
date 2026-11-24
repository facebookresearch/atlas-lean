/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RascalWords

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

-- The empty word contributes once at every ascent bound.
example (j : ℕ) : rascalGen j 0 0 = 1 := by
  calc
    _ = ({[]} : Finset (List ℕ)).card := by
      apply Nat.subtype_card
      intro w
      cases w <;> simp [wordAscents]
    _ = 1 := Finset.card_singleton _

-- At the first positive bound, a word and its odd-position flip straddle the cutoff.
example : RascalWord 1 3 7 := ⟨[0, 0, 1, 1, 1, 0, 0], by decide⟩

example : wordAscents [1, 0, 0, 1, 0, 0, 1] = 2 := rfl

-- With no ascents allowed, the first row covered by the theorem counts four words.
example : ∑ k ∈ Finset.range 4, (rascalGen 0 k 3 : ℤ) = 4 := by
  simpa using sum_rascalGen_four_mul_add_three 0

-- The empty row contributes once even when the binomial cutoff extends past the row.
example (j : ℕ) : ∑ k ∈ Finset.range 1, (rascalGen j k 0 : ℤ) = 1 := by
  rw [show 1 = 0 + 1 by rfl, sum_rascalGen_row]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)]
  · simp

-- With no ascents, each number of ones determines a unique word.
example (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (rascalGen 0 k n : ℤ) = n + 1 := by
  simpa [Finset.sum_range_succ, add_comm] using sum_rascalGen_row 0 n

-- At the first nontrivial cutoff, only the word 0101 is excluded.
example : ∑ k ∈ Finset.range 5, (rascalGen 1 k 4 : ℤ) = 15 := by
  rw [sum_rascalGen_row 1 4]
  decide

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
