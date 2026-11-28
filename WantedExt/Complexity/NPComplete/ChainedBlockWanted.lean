/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHAINED BLOCK is NP-complete

Source:
C. Iwamoto and T. Ide, "Chained Block is NP-complete", IEICE Transactions on Information and
Systems E107-D (2024), 320-324, doi:10.1587/transinf.2023FCL0001.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChainedBlockDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainedBlock

/-!
# CHAINED BLOCK is NP-complete

Chained Block is one of Nikoli's pencil puzzles. Iwamoto and Ide (2024): it "is played on a
rectangular grid of cells. Some of the cells are colored black, and each black cell contains a
number or a wildcard character `?`. The purpose of the puzzle is to paint cells in black
according to the following rules: A set of connected black cells are called a block. A set of
two or more blocks connected via corners is called a chain. (1) Every block must contain one
number or one `?`. (2) The number in each block indicates the size of the block. (3) A block
with a wildcard character `?` can have an arbitrary size. (4) Every block must be part of a
chain. (5) All blocks in a single chain must have different shapes. If a block is the rotated
or mirror image of another block, then those two blocks are considered to have the same
shape." The decision problem asks whether a given instance has a solution.

The grid is given row by row; every row has the length of the first row. A cell entry
`(false, 0)` is a cell that is not initially black; `(true, k)` is an initially black cell that
holds the number `k` when `0 < k` and the wildcard `?` when `k = 0` (blocks have at least one
cell, so no number is `0`). A solution is the set `B` of black cells, which contains the
initially black cells. Blocks are the connected components of the grid graph (the box product
of two path graphs, i.e. orthogonal adjacency) induced on `B`. Two different blocks are
connected via corners when a cell of one and a cell of the other are diagonal neighbors
(different blocks are never orthogonally adjacent). A chain is a connected component of the
graph on blocks given by this relation that has at least two blocks, so (4) says that every block
is connected via corners to another block, and (5) says that two different blocks joined by a
path in that graph do not have the same shape. Shapes compare the integer coordinates of the
cells up to the eight symmetries of the square lattice (rotations by multiples of a right angle
and reflections) followed by a translation.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CHAINED BLOCK is NP-complete.** Source: Iwamoto and Ide (2024), Theorem 1. -/
public theorem_wanted chainedBlock_npComplete :
    chainedBlockDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chainedBlockDec

end MetaMathlibExt.Complexity.NPComplete.ChainedBlock
