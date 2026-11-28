/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAHJONG SOLITAIRE with perfect information: definitions

Source:
M. de Bondt, "Solving Mahjong Solitaire boards with peeking", arXiv:1203.6559 (2012),
Theorems 2 and 3, https://arxiv.org/abs/1203.6559 (Theorem 2 is credited there to
D. Eppstein, "Computational complexity of games and puzzles", entry Shanghai,
https://ics.uci.edu/~eppstein/cgt/hard.html);
model of the game: A. Condon, J. Feigenbaum, C. Lund and P. Shor, "Random debaters and the
hardness of approximating stochastic functions", SIAM Journal on Computing 26(2) (1997),
369-400, Section 3.4, doi:10.1137/S0097539793260738.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MahjongSolitaire

/-- A tile `(i, j, k, s)`: row `i`, place `j`, height `k`, and its set of matching tiles `s`. -/
abbrev Tile := ℕ × ℕ × ℕ × ℕ

/-- An instance: the tiles of the arrangement. -/
abbrev MahjongSolitaireInstance := List Tile

/-- The position `(i, j, k)` of a tile. -/
def pos (t : Tile) : ℕ × ℕ × ℕ := (t.1, t.2.1, t.2.2.1)

/-- Well-formedness of an instance: distinct positions, no gaps in a row, a tile under every
tile above height `0`, and two or four tiles in each set of matching tiles. -/
def WellFormed (i : MahjongSolitaireInstance) : Prop :=
  (i.map pos).Nodup ∧
    (∀ a ∈ i, ∀ b ∈ i, a.1 = b.1 → a.2.2.1 = b.2.2.1 →
      ∀ j, a.2.1 ≤ j → j ≤ b.2.1 → (a.1, j, a.2.2.1) ∈ i.map pos) ∧
    (∀ a ∈ i, 0 < a.2.2.1 → (a.1, a.2.1, a.2.2.1 - 1) ∈ i.map pos) ∧
    ∀ a ∈ i, (i.filter fun b => b.2.2.2 = a.2.2.2).length = 2 ∨
      (i.filter fun b => b.2.2.2 = a.2.2.2).length = 4

/-- The tile `a` is available among the remaining tiles `C`: no tile of `C` lies on it, and the
place before it or the place after it in its row is empty. -/
def Available (C : List Tile) (a : Tile) : Prop :=
  (a.1, a.2.1, a.2.2.1 + 1) ∉ C.map pos ∧
    ((a.2.1 = 0 ∨ (a.1, a.2.1 - 1, a.2.2.1) ∉ C.map pos) ∨
      (a.1, a.2.1 + 1, a.2.2.1) ∉ C.map pos)

/-- The moves `s` remove all of the tiles `C`: each move removes two distinct available matching
tiles of the remaining ones, and no tile is left at the end. -/
def Clears : List Tile → List (Tile × Tile) → Prop
  | C, [] => C = []
  | C, m :: s => m.1 ∈ C ∧ m.2 ∈ C ∧ m.1 ≠ m.2 ∧ m.1.2.2.2 = m.2.2.2.2 ∧
      Available C m.1 ∧ Available C m.2 ∧ Clears ((C.erase m.1).erase m.2) s

/-- Some sequence of moves removes all tiles. -/
def MahjongSolitaireFeasible (i : MahjongSolitaireInstance) : Prop :=
  ∃ s : List (Tile × Tile), Clears i s

open Classical in
/-- MAHJONG SOLITAIRE with perfect information as a decision problem over bitstrings. -/
noncomputable def mahjongSolitaireDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MahjongSolitaireInstance) x with
  | some i => decide (WellFormed i ∧ MahjongSolitaireFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MahjongSolitaire
