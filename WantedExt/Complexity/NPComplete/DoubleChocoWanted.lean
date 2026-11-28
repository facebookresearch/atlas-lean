/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOUBLE CHOCO is NP-complete

Source:
D. Đurić, "Double Choco is NP-complete", Master thesis, EPFL (2022), arXiv:2203.02815,
Chapter 1 and Chapter 4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DoubleChocoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DoubleChoco

open MetaMathlibExt.Complexity.NPComplete.ChainedBlock (SameShape coords)

/-!
# DOUBLE CHOCO is NP-complete

Đurić (Chapter 1) describes Double Choco (Nikoli): an `m × n` grid board of unit squares, of
white or gray color; some squares contain an integer between `1` and `mn / 2`. A solution is a
set of blocks such that
* the blocks are disjoint, and together they cover all cells of the puzzle;
* each block has the same number of white and gray cells;
* the white and gray areas of any block are connected (both separately and with each other) and
  they have the same size and shape, with respect to rotation or mirroring;
* if any cell inside a block contains a number, then the white and gray area of that block must
  have that number of cells (a block can contain any number of cells with numbers).

INSTANCE: a Double Choco board. QUESTION: does it have a solution? (Đurić proves this
NP-complete, Chapter 4.)

The board is given row by row; every row has the length of the first row. A cell entry is
`(color, number)` with color `0` (white) or `1` (gray), and number `0` for no number. Cells are
`Fin m × Fin n`, adjacent when they share a side in Mathlib's grid graph
`pathGraph m □ pathGraph n`. A solution labels every cell with its block; the blocks are the
nonempty label classes, so they are disjoint and cover the board. Connectivity is
`SimpleGraph.Connected` of the induced subgraph (so each area is nonempty), and "the same
shape, with respect to rotation or mirroring" is `ChainedBlock.SameShape` of the integer
coordinates (`ChainedBlock.coords`): one area is the image of the other under one of the eight
symmetries of the square lattice followed by a translation. Equal shapes have the same number
of cells.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DOUBLE CHOCO is NP-complete.** Source: Đurić (2022), Chapter 4. -/
public theorem_wanted doubleChoco_npComplete :
    doubleChocoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L doubleChocoDec

end MetaMathlibExt.Complexity.NPComplete.DoubleChoco
