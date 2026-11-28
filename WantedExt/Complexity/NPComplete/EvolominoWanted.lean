/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EVOLOMINO is NP-complete

Source:
A. V. Nikolaev, "Evolomino is NP-complete", arXiv:2503.07611 (2025), Sections 1 and 2;
puzzle rules: Nikoli Co., Ltd., "Evolomino", https://www.nikoli.co.jp/en/puzzles/evolomino/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EvolominoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Evolomino

open BkVPGRecognition (GridAdj IsGridPath)

/-!
# EVOLOMINO is NP-complete

Nikolaev (Section 2) states the problem. INSTANCE: "a rectangular board of size `p × q`, where
each cell is either white or shaded. Some of the white cells contain pre-drawn squares. The
board also includes a set of pre-drawn arrows. Each arrow starts at the center of one white cell
and ends at the center of another, traversing through the centers of intermediate white cells
horizontally, vertically or with 90 degree turns. No two arrows may pass through the same cell."
QUESTION: "Does there exist at least one solution to the puzzle, i.e., a map from the set of
white cells to the set `{∅, □}` that satisfies the rules of the puzzle: each block contains
exactly one square placed on the arrow; each arrow passes through at least two blocks; each
subsequent block in the direction of the arrow adds one square to the previous block without
rotating or flipping?" A block is "a group of squares connected vertically and horizontally"
(Nikoli's rules, quoted in Section 1). Nikolaev proves the problem NP-complete by a parsimonious
reduction from 3-SAT.

The board is given row by row: entry `c` of row `r` is `0` (white), `1` (shaded) or `2` (white
with a pre-drawn square) for cell `(r, c)`; cells outside the board count as shaded. Each arrow
is the list of its cells from start to end, a grid path of `BkVPGRecognitionWanted`
(`IsGridPath`: distinct cells, consecutive cells adjacent, `GridAdj`) of at least two white
cells; no cell lies on two arrows. A solution is the finite set `S` of cells holding squares: all
white, including every pre-drawn square. The block of a square `p` is the set of squares
reachable from `p` through orthogonally adjacent squares (`block`). Since every block holds
exactly one arrow square, the blocks met by an arrow, in the direction of the arrow, are the
blocks of the squares on the arrow in arrow order (`A.filter (· ∈ S)`); "adds one square without
rotating or flipping" says the next block has one more cell and contains a translate of the
previous one (`Evolves`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EVOLOMINO is NP-complete.** Source: Nikolaev (2025). -/
public theorem_wanted evolomino_npComplete :
    evolominoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L evolominoDec

end MetaMathlibExt.Complexity.NPComplete.Evolomino
