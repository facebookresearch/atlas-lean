/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

/-!
# SOLITAIRE CHESS: definitions

Maßberg (2015), Section 1: "Given a chess board with some chess pieces of the same color placed
on it, the task is to capture all pieces but one using only moves that are allowed in chess.
Moreover, in each move one piece has to be captured." The generalized puzzle has "n pieces on
a chess board of size `N × N`", and "every type of piece might appear several times"; the six
types are king, queen, rook, bishop, knight and pawn. Section 2: squares are positions
`(i, j)`; "a pawn on position `(i, j)` can only capture a piece at position `(i − 1, j + 1)` or
`(i + 1, j + 1)`"; "A move is uniquely defined by a pair of pieces `(p₁, p₂)` where `p₁`
captures `p₂`. A move `(p₁, p₂)` is feasible if `p₁` can capture `p₂` following the rules of
chess (ignoring the color of the pieces)."

INSTANCE: a board size `N` and pieces on distinct squares of the `N × N` board, each with a type.
QUESTION: is there a sequence of feasible moves after which exactly one piece is left?

Representation. A piece is `(t, i, j)`: its type `t` (`0` king, `1` queen, `2` rook,
`3` bishop, `4` knight, `5` pawn) and its square, column `i` and row `j`. A capture from square
`a` to square `b` with `Δi = b.1 - a.1`, `Δj = b.2 - a.2` follows the chess capture rules: a
king moves one square in any direction (`max |Δi| |Δj| = 1`); a rook along a rank or file, a
bishop along a diagonal, a queen along either, in each case with every square strictly between
`a` and `b` empty; a knight moves `(±1, ±2)` or `(±2, ±1)`; a pawn captures to
`(i ± 1, j + 1)`. A move removes the captured piece and puts the capturing piece on its square,
so every move captures one piece and pieces never leave the board. As in the source, a move is
determined by the pair of pieces alone: there is no promotion, and since all pieces have one
color there is no check, castling or en passant.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
J. Maßberg, "Solitaire Chess is NP-complete", arXiv:1501.06398 (2015),
https://arxiv.org/abs/1501.06398.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SolitaireChess

/-- A piece `(t, i, j)`: its type `t` (`0` king, `1` queen, `2` rook, `3` bishop, `4` knight,
`5` pawn) and its square, column `i` and row `j`. -/
abbrev Piece := ℕ × ℕ × ℕ

/-- An instance: the board size `N` and the list of pieces. -/
abbrev SolitaireChessInstance := ℕ × List Piece

/-- The square of a piece, in integer coordinates. -/
def square (p : Piece) : ℤ × ℤ := ((p.2.1 : ℤ), (p.2.2 : ℤ))

/-- Some piece of `s` stands on square `q`. -/
def Occupied (s : List Piece) (q : ℤ × ℤ) : Prop := ∃ p ∈ s, square p = q

/-- Every square strictly between `a` and `b` on the line through them is empty: the squares
`a + k • (sign Δi, sign Δj)` for `0 < k < max |Δi| |Δj|`. -/
def PathClear (s : List Piece) (a b : ℤ × ℤ) : Prop :=
  ∀ k < max (b.1 - a.1).natAbs (b.2 - a.2).natAbs, 0 < k →
    ¬ Occupied s (a.1 + k * (b.1 - a.1).sign, a.2 + k * (b.2 - a.2).sign)

/-- With pieces `s` on the board, a piece of type `t` on square `a` can capture a piece on
square `b` by the rules of chess. -/
def CanCapture (s : List Piece) (t : ℕ) (a b : ℤ × ℤ) : Prop :=
  let di := (b.1 - a.1).natAbs
  let dj := (b.2 - a.2).natAbs
  if t = 0 then max di dj = 1
  else if t = 1 then (di = 0 ∨ dj = 0 ∨ di = dj) ∧ PathClear s a b
  else if t = 2 then (di = 0 ∨ dj = 0) ∧ PathClear s a b
  else if t = 3 then di = dj ∧ PathClear s a b
  else if t = 4 then (di = 1 ∧ dj = 2) ∨ (di = 2 ∧ dj = 1)
  else di = 1 ∧ b.2 = a.2 + 1

/-- One move from pieces `s` to pieces `s'`: piece `s[a]` captures piece `s[b]`; the captured
piece is removed and the capturing piece moves to its square. -/
def Move (s s' : List Piece) : Prop :=
  ∃ a b : Fin s.length, a ≠ b ∧ CanCapture s s[a].1 (square s[a]) (square s[b]) ∧
    s' = (s.set a (s[a].1, s[b].2)).eraseIdx b

/-- Well-formedness: every piece has a type at most `5` and a square on the `N × N` board, and
no two pieces share a square. -/
def WellFormed (i : SolitaireChessInstance) : Prop :=
  (∀ p ∈ i.2, p.1 ≤ 5 ∧ p.2.1 < i.1 ∧ p.2.2 < i.1) ∧ (i.2.map Prod.snd).Nodup

/-- Some sequence of moves leaves exactly one piece. -/
def SolitaireChessFeasible (i : SolitaireChessInstance) : Prop :=
  ∃ s, Relation.ReflTransGen Move i.2 s ∧ s.length = 1

open Classical in
/-- SOLITAIRE CHESS as a decision problem over bitstrings. -/
noncomputable def solitaireChessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SolitaireChessInstance) x with
  | some i => decide (WellFormed i ∧ SolitaireChessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SolitaireChess
