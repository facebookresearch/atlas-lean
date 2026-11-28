/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# YAJILIN is NP-complete

Source:
A. Ishibashi, Y. Sato and S. Iwata, "NP-completeness of two pencil puzzles: Yajilin and Country
Road", Utilitas Mathematica 88 (2012), 237-246;
H. Tang, "A framework for loop and path puzzle satisfiability NP-hardness results",
arXiv:2202.02046 (2022), Section 3.3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.YajilinDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Yajilin

/-!
# YAJILIN is NP-complete

Yajilin (Nikoli) is played on a rectangular grid in which some cells carry a clue: a number and
an arrow pointing up, down, left or right. Tang (2022, Section 3.3) states its rules: "Draw a
single loop passing between adjacent cell centres. Some squares are marked in grey; these are
not part of loop. Any other square not passed through by the loop must be shaded, and no two
shaded cells may be adjacent. Grey cells may contain a number n and an arrow pointing
orthogonally: this means that there are n shaded cells in the direction of the arrow."

INSTANCE: a rectangular grid, some cells carrying a clue (a number and an arrow).
QUESTION: is there a loop satisfying these rules, where the grey cells are the clue cells?

Ishibashi, Sato and Iwata (2012) prove this NP-complete; Tang (2022, Section 3.3) reproves
NP-hardness with a T-metacell gadget, notes that his gadget works with every grey cell carrying
a clue, and checks a solution in polynomial time.

Representation. The grid is given explicitly, row by row: entry `c` of row `r` is
`(flag, k, d)` for cell `(r, c)`, with `flag = 0` for an ordinary cell and `flag = 1` for a clue
cell with number `k` and arrow `d`: `0` up, `1` down, `2` left, `3` right. `WellFormed`
requires at least one row and one column, rows of equal length, `flag ≤ 1`, `d ≤ 3`, and
`k = d = 0` in ordinary cells. As in Nikoli's puzzle, the grey cells are exactly the clue cells.
Cells are `Fin m × Fin n` (row, column), adjacent when they share a side in Mathlib's grid graph
`pathGraph m □ pathGraph n`. The loop is a cycle `c` of this graph
(`SimpleGraph.Walk.IsCycle`); a cell is passed through by the loop when it is in `c.support`.
The shaded cells are the ordinary cells not on the loop. The cells in the direction of the arrow
of clue cell `x` are the cells of the same column above `x` (up) or below it (down), or of the
same row left of `x` (left) or right of it (right), up to the edge of the grid.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **YAJILIN is NP-complete.** Source: Ishibashi, Sato and Iwata (2012); Tang (2022),
Section 3.3. -/
public theorem_wanted yajilin_npComplete :
    yajilinDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L yajilinDec

end MetaMathlibExt.Complexity.NPComplete.Yajilin
