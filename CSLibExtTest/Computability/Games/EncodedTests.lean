/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for encoded finite parity games
-/
module

public import CSLibExt.Computability.Games.Encoded
import Mathlib.Tactic.FinCases

/-!
# Tests for encoded finite parity games

A two-position encoded game on `Fin 2`: position `0` (even) moves to `1`,
position `1` (odd) loops, priorities `0` and `1`. The maximal priority on
the whole arena is `1`, and the attractor of `{1}` for even is the whole
arena (even moves `0 → 1`, and `1` is already in the target).
-/

@[expose] public section

namespace Cslib.Games.EncodedParityGame.Tests

/-- Position `0` (even) moves to `1`, position `1` (odd) loops, priorities `0`, `1`. -/
def twoGame : EncodedParityGame 2 where
  owner v := decide (v = 1)
  move v w := decide (v = 0 ∧ w = 1 ∨ v = 1 ∧ w = 1)
  priority v := v.val

/-- Every position has a move. -/
theorem twoGame_serial : ∀ v, ∃ w, twoGame.move v w = true := by
  intro v
  fin_cases v <;> decide

/-- The maximal priority on the whole arena is `1`. -/
example : twoGame.maxPriorityIn Finset.univ = 1 := by decide

/-- The maximal-priority positions are `{1}`. -/
example : twoGame.maxPositionsIn Finset.univ = {1} := by decide

/-- The attractor of `{1}` for even is the whole arena. -/
example : twoGame.attractorIn false {1} Finset.univ = Finset.univ := by decide

/-- The `ParityGame` of the encoded game assigns the right owners. -/
example : (twoGame.toParityGame twoGame_serial).owner 0 = Player.even := rfl

/-- Priority compression of `twoGame`: priorities `0, 1` map to `0, 3`
(rank `1` with odd parity). -/
example : twoGame.priorityCompress.priority 0 = 0 := by decide

/-- Priority compression of `twoGame`: priorities `0, 1` map to `0, 3`
(rank `1` with odd parity). -/
example : twoGame.priorityCompress.priority 1 = 3 := by decide

/-- A three-position game with sparse priorities `0, 5, 100` (all positions
move to `0`). -/
def sparseGame : EncodedParityGame 3 where
  owner _ := false
  move _ _ := true
  priority v := if v = 1 then 5 else if v = 2 then 100 else 0

/-- Priority compression turns the sparse priorities `0, 5, 100` into
`0, 3, 4`: ranks `0, 1, 2` with parities `0, 1, 0`. -/
example : sparseGame.priorityCompress.priority 1 = 3 := by decide

/-- Priority compression turns the sparse priorities `0, 5, 100` into
`0, 3, 4`: ranks `0, 1, 2` with parities `0, 1, 0`. -/
example : sparseGame.priorityCompress.priority 2 = 4 := by decide

/-- Every compressed priority of the sparse game is below `2 * 3`. -/
example : ∀ v, sparseGame.priorityCompress.priority v < 2 * 3 :=
  fun _v => sparseGame.priorityCompressed_lt

end Cslib.Games.EncodedParityGame.Tests
