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

end MathlibExtTest.NumberTheory.LeonardoPTilingsCardLeonardoPTilings
