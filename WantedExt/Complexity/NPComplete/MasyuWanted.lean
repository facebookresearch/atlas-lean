/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MASYU is NP-complete

Source:
E. Friedman, "Pearl puzzles are NP-complete", manuscript, Stetson University (2002),
https://erich-friedman.github.io/papers/pearl/pearl.html;
H. Tang, "A framework for loop and path puzzle satisfiability NP-hardness results",
arXiv:2202.02046 (2022), Section 3.2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MasyuDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Masyu

/-!
# MASYU is NP-complete

Masyu (Nikoli; Friedman calls it the Pearl puzzle) is played on a rectangular grid of cells,
some of which contain a white or a black pearl. Friedman (2002): "The goal is to find a closed,
non-intersecting path passing through every pearl so that a) the path turns at every black
pearl, but does not turn immediately before or after, and b) the path does not turn at any white
pearl, but does turn immediately before or after." Tang (2022, Section 3.2) states the same
rules: "Draw a single loop through all pearls and passing between adjacent cell centres. The
loop must turn on each black pearl but go straight on the cells immediately before and after,
and it must go straight through each white pearl and turn on a cell immediately before and/or
after."

INSTANCE: a rectangular grid with a white or a black pearl in some cells.
QUESTION: is there a loop satisfying these rules?

Friedman proves NP-hardness by a reduction from Hamiltonian circuit in cubic planar graphs and
notes that a solution is checked in polynomial time; Tang (2022, Section 3.2) reproves
NP-completeness with a T-metacell gadget.

Representation. The grid is given explicitly, row by row: entry `c` of row `r` is `0` (no
pearl), `1` (white pearl) or `2` (black pearl) for cell `(r, c)`, so the instance size is
proportional to the area of the grid. `WellFormed` requires at least one row and one column,
rows of equal length and entries at most `2`. Cells are `Fin m × Fin n` (row, column), adjacent
when they share a side in Mathlib's grid graph `pathGraph m □ pathGraph n`. The loop through
cell centres is a cycle `c` of this graph (`SimpleGraph.Walk.IsCycle`), so it neither crosses
nor branches. A cell `x` on the cycle has exactly two neighbors joined to it by edges of `c`:
the cells immediately before and after `x` on the loop. The loop turns at `x` when these two
neighbors differ in both coordinates (one horizontal and one vertical step, the notion `IsTurn`
of `WantedExt.Complexity.NPComplete.DetourWanted`), and goes straight through `x` when they are
two distinct cells in the same row or the same column, i.e. on opposite sides of `x`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MASYU is NP-complete.** Source: Friedman (2002); Tang (2022), Section 3.2. -/
public theorem_wanted masyu_npComplete :
    masyuDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L masyuDec

end MetaMathlibExt.Complexity.NPComplete.Masyu
