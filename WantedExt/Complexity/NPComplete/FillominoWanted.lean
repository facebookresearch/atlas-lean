/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FILLOMINO is NP-complete

Source:
T. Yato, "Complexity and completeness of finding another solution and its application to
puzzles", Master's thesis, University of Tokyo (2003), Section 3.3, Theorem 3.8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FillominoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Fillomino

/-!
# FILLOMINO is NP-complete

Yato (2003, Section 3.3) states the rules of Fillomino:
* "A problem is given as a rectangular grid, with some cells filled with positive integers. The
  length of sides of the rectangle is called the size of the problem."
* "The goal is to fill each blank cell with a integer and divide the board into several blocks
  so that
  - each block consists of one or more consecutive cells (forms a polyomino),
  - all the cells in a block are filled with the same integer, which equals to the area of the
    block,
  - blocks with the same area do not share their edges."

INSTANCE: a rectangular grid, some cells filled with positive integers.
QUESTION: can every blank cell be filled with an integer, and the grid divided into blocks,
satisfying these rules?

Yato (2003, Theorem 3.8) proves that finding a solution is ASP-complete, by a reduction from a
planar version of 3SAT, and (Theorem 2.7, with `n = 0`) that the decision problem of an
ASP-complete problem is NP-complete.

Representation. The grid is given explicitly, row by row: entry `c` of row `r` is `0` when cell
`(r, c)` is blank and the given integer otherwise (given integers are positive). `WellFormed`
requires at least one row and one column and rows of equal length. Cells are `Fin m × Fin n`,
adjacent when they share a side in Mathlib's grid graph `pathGraph m □ pathGraph n`. A solution
is a filling `f` of all cells that keeps the given integers, and a division of the grid into
blocks, the classes of a labeling `block` of the cells. A block forms a polyomino when its cells
induce a connected subgraph of the grid graph. Two blocks share an edge when a cell of one is
adjacent to a cell of the other.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FILLOMINO is NP-complete.** Source: Yato (2003), Theorems 3.8 and 2.7. -/
public theorem_wanted fillomino_npComplete :
    fillominoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L fillominoDec

end MetaMathlibExt.Complexity.NPComplete.Fillomino
