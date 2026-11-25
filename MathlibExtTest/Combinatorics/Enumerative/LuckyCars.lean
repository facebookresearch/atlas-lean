/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.LuckyCars

open MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

-- The search starts at the preference, even when a lower spot is free.
example : parkSpots (n := 3) ![1, 1, 0] = ![1, 2, 0] := by decide
example : luckyCount (n := 3) ![1, 1, 0] = 2 := by decide

-- When all spots at or above the preference are occupied, it is returned as the fallback.
example : nextFreeSpot ({1, 2} : Finset (Fin 3)) 1 = 1 := by decide

-- Without right steps there is exactly one path.
example : (Nat.card (BallotPath 0 4) : ℚ) = 1 := by
  rw [card_ballotPath 0 4 (by decide)]
  norm_num

-- On the diagonal this is the Catalan count C₃ = 5.
example : (Nat.card (BallotPath 3 3) : ℚ) = 5 := by
  rw [card_ballotPath 3 3 (by decide)]
  norm_num [Nat.choose]

example : (Nat.card (BallotPath 2 4) : ℚ) = 9 := by
  rw [card_ballotPath 2 4 (by decide)]
  norm_num [Nat.choose]
