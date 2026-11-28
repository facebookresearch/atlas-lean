/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HITORI is NP-complete

Source:
R. A. Hearn and E. D. Demaine, *Games, Puzzles, and Computation*, A K Peters (2009),
Section 9.2 "Hitori", pp. 112-115, doi:10.1201/b10581;
puzzle rules: M. L. Pacheco, F. Somenzi, D. Srinivas and A. Trivedi, "Explaining Hitori
puzzles: neurosymbolic proof staging for sequential decisions", arXiv:2508.14294 (2025),
Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HitoriDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Hitori

/-!
# HITORI is NP-complete

Hitori (Nikoli) is "a shading puzzle played on a rectangular grid, with each cell containing a
symbol, typically a number" (Pacheco, Somenzi, Srinivas and Trivedi 2025, Section 1). "The
objective of the solver is to shade some of the squares to satisfy three conditions:
1. Uniqueness. No symbol appears more than once unshaded in any row or column of the grid.
2. Separation. Shaded squares cannot share an edge. However, they may share a corner.
3. Connection. The unshaded squares form an edge-connected region. (Two squares that only touch
   in a corner are not edge-connected.)"

INSTANCE: a rectangular grid with a number in each cell.
QUESTION: can some cells be shaded so that conditions 1-3 hold?

Hearn and Demaine (2009, Section 9.2) prove this NP-complete; Pacheco et al. cite them for it.

Representation. The grid is given explicitly, row by row: entry `c` of row `r` is the number
in cell `(r, c)`. `WellFormed` requires at least one row and one column and rows of equal
length. Cells are `Fin m × Fin n` (row, column), adjacent (sharing an edge) when they are
adjacent in Mathlib's grid graph `pathGraph m □ pathGraph n`. A shading is a map `s` from cells
to `Bool` (`true` = shaded). Condition 1: two distinct cells of the same row or column holding
the same number are not both unshaded. Condition 3: the unshaded cells induce a connected
subgraph of the grid graph (a region, so it is nonempty; this changes no answer, since a grid
whose cells are all shaded has one cell by condition 2, and leaving that cell unshaded also
satisfies the conditions).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HITORI is NP-complete.** Source: Hearn and Demaine (2009), Section 9.2. -/
public theorem_wanted hitori_npComplete :
    hitoriDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hitoriDec

end MetaMathlibExt.Complexity.NPComplete.Hitori
