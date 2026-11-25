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

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
