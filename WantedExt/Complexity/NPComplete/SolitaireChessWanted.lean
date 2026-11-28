/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SOLITAIRE CHESS is NP-complete

Source:
J. Maßberg, "Solitaire Chess is NP-complete", arXiv:1501.06398 (2015),
https://arxiv.org/abs/1501.06398.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SolitaireChessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SolitaireChess

/-!
# SOLITAIRE CHESS is NP-complete

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

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SOLITAIRE CHESS is NP-complete.** Source: Maßberg (2015). -/
public theorem_wanted solitaireChess_npComplete :
    solitaireChessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L solitaireChessDec

end MetaMathlibExt.Complexity.NPComplete.SolitaireChess
