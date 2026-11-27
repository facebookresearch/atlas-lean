/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PrincessAndRosesSimplification

open MetaMathlibExt MetaMathlibExt.SpragueGrundy

-- An arbitrary shift of the empty board leaves a terminal simplified position.
example (n : ℕ) : Equiv (princessRoses ![0, 0, 0, 0]) (simplifiedPrincessRoses (n, n, n, 0)) := by
  simpa only [Nat.zero_add] using
    princessRoses_equiv_simplifiedPrincessRoses 0 0 0 0 n le_rfl le_rfl le_rfl

-- Ties at the bottom do not prevent shifting the three largest piles.
example : Equiv (princessRoses ![2, 1, 1, 1]) (simplifiedPrincessRoses (4, 3, 3, 1)) :=
  princessRoses_equiv_simplifiedPrincessRoses 2 1 1 1 2 (by decide) le_rfl le_rfl

-- Even with four distinct piles, the ordinary game has moves the simplified game forbids.
example : ![4, 3, 1, 1] ∈ (princessRoses ![4, 3, 2, 1]).moves ![4, 3, 2, 1] := by
  change ![4, 3, 1, 1] ∈ slowANimMoves {1, 2} ![4, 3, 2, 1]
  decide

example : (4, 3, 1, 1) ∉ simplifiedPrincessRosesMoves (4, 3, 2, 1) := by
  decide

example : Equiv (princessRoses ![4, 3, 2, 1]) (simplifiedPrincessRoses (5, 4, 3, 1)) :=
  princessRoses_equiv_simplifiedPrincessRoses 4 3 2 1 1 (by decide) (by decide) (by decide)
