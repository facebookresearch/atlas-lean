/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZHED is NP-complete

Source:
S. Saha and E. D. Demaine, "ZHED is NP-complete", arXiv:2112.07914 (2021).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ZhedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Zhed

/-!
# ZHED is NP-complete

INSTANCE: an `n × n` grid, a target square, and numbered tiles on some other squares, each
numbered between `1` and `n - 1`.
QUESTION: is there a sequence of moves of distinct tiles that fills the target square, where a
move of a tile numbered `k` in one of the four directions fills the `k` closest unfilled squares
in that direction?

Saha and Demaine (Section 1): "An instance of this puzzle is played on a `n × n` square grid ...
One of the squares is designated as the target. Several of the other squares are filled by
tiles. Each initial tile has an integer number between `1` and `n − 1` written on it. In each
move, the player selects one of the remaining numbered tiles and a direction (up, down, left, or
right) ... If the tile was numbered `k`, the move replaces the tile with a blank tile (keeping
the square filled, but removing the number) and fills the `k` closest unfilled squares in the
specified direction with blank tiles. The objective of the game is to fill the target square."
They prove deciding whether the target can be filled NP-complete, even when every tile is
numbered `1`.

Representation. Squares are `(row, column)` pairs, `0 ≤ row, column < n`; the moves work in
`ℤ × ℤ` so that steps up and left subtract. The squares in a direction from a square, nearest
first, are those of the board along that ray; a move fills the first `k` of them that are not
yet filled, or all of them if fewer than `k` remain (the board has no squares past its edge).
Filled squares stay filled, and a selected tile loses its number, so each tile moves at most
once; the blank tiles placed by moves carry no number and never move. The board is given
explicitly, row by row, with binary numbers below `n`, so the instance has size `O(n² log n)`,
polynomial in `n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ZHED is NP-complete.** Source: Saha and Demaine (2021). -/
public theorem_wanted zhed_npComplete :
    zhedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L zhedDec

end MetaMathlibExt.Complexity.NPComplete.Zhed
