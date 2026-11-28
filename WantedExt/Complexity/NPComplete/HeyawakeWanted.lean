/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HEYAWAKE is NP-complete

Source:
M. Holzer and O. Ruepp, "The troubles of interior design: a complexity analysis of the game
Heyawake", Fun with Algorithms (FUN 2007), Lecture Notes in Computer Science 4475 (2007),
198-212, doi:10.1007/978-3-540-72914-3_18.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HeyawakeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Heyawake

/-!
# HEYAWAKE is NP-complete

Heyawake is played on a rectangular grid of cells divided into rectangular rooms; some rooms
contain a number. Some cells are painted (shaded) so that:
1. painted cells are never orthogonally adjacent;
2. all white (unpainted) cells are interconnected;
3. a numbered room contains exactly that many painted cells (an unnumbered room may contain any
   number);
4. no straight horizontal or vertical line of consecutive white cells contains cells from more
   than two rooms.

INSTANCE: an `m × n` grid partitioned into rectangular rooms, some of them numbered.
QUESTION: can cells be painted so that rules 1-4 hold?

The grid is given explicitly, row by row: entry `c` of row `r` is the index of the room that
contains cell `(r, c)`, so the description lists every cell (a succinct encoding by room
rectangles could describe exponentially many cells). Room `k` carries `(numbered, number)`,
entry `k` of the second component. Rows are `0, …, m - 1` and columns `0, …, n - 1`.
`WellFormed` requires `m, n ≥ 1`, rows of equal length, room indices in range, every room
nonempty, and every room rectangular: with any two of its cells, a room contains every cell of
their bounding box. A painting is a function `ℕ → ℕ → Bool` read on the grid. White-cell
connectivity is `SimpleGraph.Connected` (nonempty and preconnected: the white cells form a
single polyomino) of the subgraph that the grid graph (Mathlib's `pathGraph m □ pathGraph n`,
cells adjacent when they share a side) induces on the white cells.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HEYAWAKE is NP-complete.** Source: Holzer and Ruepp (2007). -/
public theorem_wanted heyawake_npComplete :
    heyawakeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L heyawakeDec

end MetaMathlibExt.Complexity.NPComplete.Heyawake
