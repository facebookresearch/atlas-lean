/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SmithRemoteness

namespace MetaMathlibExt.SpragueGrundy

/-- Options of the test game: a chain `3 → 2 → 1 → 0`, plus position `4` with options `0, 2`
(both of even remoteness) and position `5` with options `1, 3` (both of odd remoteness). -/
def branchMoves : ℕ → Finset ℕ
  | 1 => {0}
  | 2 => {1}
  | 3 => {2}
  | 4 => {0, 2}
  | 5 => {1, 3}
  | _ => ∅

/-- The test game, ranked by the position itself. -/
abbrev branchGame : ImpartialGame where
  Pos := ℕ
  eqDec := inferInstance
  moves := branchMoves
  rank n := n
  rank_lt p q h := by
    rcases p with _ | _ | _ | _ | _ | _ | p <;> simp [branchMoves] at h <;> omega
  start := 0

private theorem r0 : smithRemoteness branchGame (0 : ℕ) = 0 :=
  smithRemoteness_of_moves_eq_empty _ _ rfl

private theorem r1 : smithRemoteness branchGame (1 : ℕ) = 1 := by
  rw [smithRemoteness_eq branchGame (1 : ℕ), show branchGame.moves (1 : ℕ) = {0} from rfl,
    Finset.image_singleton, r0]
  decide

private theorem r2 : smithRemoteness branchGame (2 : ℕ) = 2 := by
  rw [smithRemoteness_eq branchGame (2 : ℕ), show branchGame.moves (2 : ℕ) = {1} from rfl,
    Finset.image_singleton, r1]
  decide

private theorem r3 : smithRemoteness branchGame (3 : ℕ) = 3 := by
  rw [smithRemoteness_eq branchGame (3 : ℕ), show branchGame.moves (3 : ℕ) = {2} from rfl,
    Finset.image_singleton, r2]
  decide

/-- Terminal positions have remoteness `0`. -/
example : smithRemoteness branchGame (0 : ℕ) = 0 := r0

/-- A chain alternates the two rules: `R(1) = 1 + 0`, `R(2) = 1 + 1`, `R(3) = 1 + 2`. -/
example : smithRemoteness branchGame (3 : ℕ) = 3 := r3

/-- Several even options: the winner hurries to the least, `R(4) = 1 + min {0, 2} = 1`. -/
example : smithRemoteness branchGame (4 : ℕ) = 1 := by
  rw [smithRemoteness_eq branchGame (4 : ℕ), show branchGame.moves (4 : ℕ) = {0, 2} from rfl,
    Finset.image_insert, Finset.image_singleton, r0, r2]
  decide

/-- All options odd: the loser delays to the largest, `R(5) = 1 + max {1, 3} = 4`. -/
example : smithRemoteness branchGame (5 : ℕ) = 4 := by
  rw [smithRemoteness_eq branchGame (5 : ℕ), show branchGame.moves (5 : ℕ) = {1, 3} from rfl,
    Finset.image_insert, Finset.image_singleton, r1, r3]
  decide

end MetaMathlibExt.SpragueGrundy
