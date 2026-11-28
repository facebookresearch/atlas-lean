/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAKARO is NP-complete

Source:
C. Iwamoto, M. Haruishi and T. Ibusuki, "Computational complexity of Herugolf and Makaro",
IEICE Transactions on Fundamentals of Electronics, Communications and Computer Sciences
E102-A(9) (2019), 1118-1125, doi:10.1587/transfun.E102.A.1118; conference version:
"Herugolf and Makaro are NP-complete", 9th International Conference on Fun with Algorithms
(FUN 2018), LIPIcs 100 (2018), 24:1-24:11, doi:10.4230/LIPIcs.FUN.2018.24.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MakaroDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Makaro

open DosunFuwari (DosunFuwariInstance label grid)

/-!
# MAKARO is NP-complete

Makaro is played on a rectangular grid of cells. Some cells are colored black and contain an
arrow, and the remaining cells are divided into rooms surrounded by bold lines. All white cells
are filled with numbers so that:
1. each room contains all the natural numbers up to the number of cells in it, starting from 1;
2. every arrow in a black cell points at the biggest number among the numbers in the adjacent
   cells;
3. a number is not next to the same number in another room.

INSTANCE: a rectangular grid of black cells with arrows and rooms.
QUESTION: can the white cells be filled with numbers so that rules 1-3 hold?

Rule 1 says that the numbers of a room with `s` cells are `1, …, s`, each once. In rule 2 the
arrow points at an orthogonally adjacent white cell whose number is bigger than the number of
every other white cell adjacent to the black cell; adjacent means sharing a side. The biggest
number is strict, as in the source's Fig. 2(b), where an arrow between two 2-cell rooms forces
`2` at the cell it points at and `1` at the other neighbor. An arrow pointing off the grid or at
a black cell cannot be satisfied.

The grid of black cells and rooms is a `DosunFuwari.DosunFuwariInstance`, the same board as in
`DosunFuwariWanted`: the rows, top to bottom, where entry `0` is a black cell and an entry
`k ≥ 1` is a cell of room `k`; `DosunFuwari.WellFormed` requires at least one row and one
column, rows of equal length, and every room connected (a room is a region surrounded by bold
lines). The second component gives, row by row, the direction of the arrow of each black cell
(`0` up, `1` right, `2` down, `3` left), and `0` for every room cell (no ignored payload).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAKARO is NP-complete.** Source: Iwamoto, Haruishi and Ibusuki (2019). -/
public theorem_wanted makaro_npComplete :
    makaroDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L makaroDec

end MetaMathlibExt.Complexity.NPComplete.Makaro
