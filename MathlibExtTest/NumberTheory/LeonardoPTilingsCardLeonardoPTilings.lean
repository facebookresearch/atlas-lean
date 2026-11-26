/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LeonardoPTilingsCardLeonardoPTilings

namespace MathlibExtTest.NumberTheory.LeonardoPTilingsCardLeonardoPTilings

open MetaMathlibExt
open MathlibExt.NumberTheory.LeonardoPWanted

-- The `1`-tilings of a `2`-board are the two pure tilings and the lone `1`-tile.
example : (Nat.card (leonardoPTilings 1 2) : ℤ) = 3 := by
  rw [card_leonardoPTilings 1 2 (by omega)]
  rfl

-- The `2`-tilings of a `3`-board: `𝓛_{2,3} = 𝓛_{2,2} + 𝓛_{2,0} + 2 = 4`.
example : (Nat.card (leonardoPTilings 2 3) : ℤ) = 4 := by
  rw [card_leonardoPTilings 2 3 (by omega)]
  rfl

-- A short board has only the all-squares tiling.
example (n : ℕ) (hn : n ≤ 2) : (Nat.card (leonardoPTilings 2 n) : ℤ) = 1 := by
  rw [card_leonardoPTilings 2 n (by omega)]
  exact leonardoPK_of_le 2 2 n hn

-- The tiling model on the paper's `p = 3`, `n = 5` example, checked without the theorem.
-- A colored tile of length four followed by a square is a tiling.
example : (some (0, 4), [false]) ∈ leonardoPTilings 3 5 := by
  simp [leonardoPTilings]

-- A colored tile shorter than `p + 1` is not.
example : (some (0, 3), [false, false]) ∉ leonardoPTilings 3 5 := by
  simp [leonardoPTilings]

-- The nine tilings: three uncolored tilings, three colors of a length-four tile followed by a
-- square, and three colors of a lone length-five tile.
example : leonardoPTilings 3 5 =
    {(none, [false, false, false, false, false]), (none, [true, false]), (none, [false, true]),
      (some (0, 4), [false]), (some (1, 4), [false]), (some (2, 4), [false]),
      (some (0, 5), []), (some (1, 5), []), (some (2, 5), [])} := by
  ext ⟨o, bs⟩
  simp only [leonardoPTilings, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨ho, hs⟩
    rcases o with _ | ⟨c, l⟩
    · rcases bs with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, bs⟩⟩⟩⟩⟩⟩ <;>
        (try cases b1) <;> (try cases b2) <;> (try cases b3) <;> (try cases b4) <;>
        (try cases b5) <;> (try cases b6) <;> simp at hs ⊢ <;> omega
    · have h4 : 4 ≤ l := ho c l rfl
      rcases bs with _ | ⟨b1, _ | ⟨b2, bs⟩⟩ <;> (try cases b1) <;> (try cases b2) <;>
        simp at hs ⊢ <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

-- The count of the example agrees: `𝓛_{3,5} = 9`.
example : (Nat.card (leonardoPTilings 3 5) : ℤ) = 9 := by
  rw [card_leonardoPTilings 3 5 (by omega)]
  rfl

end MathlibExtTest.NumberTheory.LeonardoPTilingsCardLeonardoPTilings
