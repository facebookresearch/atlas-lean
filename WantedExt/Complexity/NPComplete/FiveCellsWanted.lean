/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIVE CELLS is NP-complete

Source:
C. Iwamoto and T. Ide, "Five Cells and Tilepaint are NP-complete", IEICE Transactions on
Information and Systems E105-D(3) (2022), 508-516, doi:10.1587/transinf.2021FCP0001.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FiveCellsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiveCells

/-!
# FIVE CELLS is NP-complete

INSTANCE: a rectangular grid of cells whose number of cells is a multiple of five, some of whose
cells contain numbers.
QUESTION: can the grid be divided into blocks of five cells (each block a connected region
enclosed by lines) so that every number equals the number of lines of a block around its cell,
counting the lines of the outer frame?

The grid is given explicitly, row by row: a list of `m` rows of `n` cells each, a cell holding
`0` (no number) or `k + 1` (the number `k`). Its cells are `Fin m × Fin n`, and two cells are
adjacent when they share a side, i.e. in Mathlib's grid graph `pathGraph m □ pathGraph n`
(`Grid`). A division into blocks is a labelling `block` of the cells; the blocks are the label
classes, each of exactly five cells and connected in the grid graph. Each of the four sides of a
cell `x` is either on the outer frame or shared with a neighbor `y`, and it is a line of a block
exactly when it is on the frame or `y` is in another block. So the number of lines around `x` is
`4` minus the number of neighbors of `x` in its own block.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FIVE CELLS is NP-complete.** Source: Iwamoto and Ide (2022). -/
public theorem_wanted fiveCells_npComplete :
    fiveCellsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L fiveCellsDec

end MetaMathlibExt.Complexity.NPComplete.FiveCells
