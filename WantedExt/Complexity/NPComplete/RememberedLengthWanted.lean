/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REMEMBERED LENGTH is NP-complete

Source:
P. Eua-anant, P. Apinyanon, T. Jirachaisri, N. Ruangsuksriwong and S. Ruangwises,
"NP-Completeness Proofs of All or Nothing, Water Walk, and Remembered Length Using the
T-Metacell Framework", arXiv:2510.21938 (2025), Section 2.3;
puzzle rules: puzz.link, "Remembered Length", https://puzz.link/rules.html?remlen.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RememberedLengthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RememberedLength

/-!
# REMEMBERED LENGTH is NP-complete

Remembered Length (Palmer Mebane) is played on a rectangular grid divided into polyominoes
called regions, with some cells shaded and some regions labeled with a positive integer. The
goal is to draw a non-crossing directed loop passing through orthogonally adjacent cells such
that (Eua-anant et al. 2025, Section 2.3):
1. the loop passes through all unshaded cells;
2. each time the loop exits a region containing a number, its section in the next region
   consists of exactly that number of cells.
puzz.link's rules add that the loop cannot branch off or cross itself, and that rule 2 applies
again each time the loop passes through the same region.

INSTANCE: a rectangular grid divided into regions, some cells shaded, some regions numbered.
QUESTION: is there a directed loop satisfying rules 1 and 2?

The loop never enters a shaded cell: Eua-anant et al. obtain the shaded version from
Hamiltonian cycles in grid graphs by shading the vertices that are not in the graph.

The instance lists the region numbers (entry `k` for region `k`, `0` for an unnumbered region)
and the grid row by row: entry `c` of row `r` is `(region, shaded)` for cell `(r, c)`. The
regions are `0, …, R - 1` with `R` the length of the number list. `WellFormed` requires at least
one row and one column, rows of equal length, region indices below `R`, and every region a
nonempty connected set of cells (a polyomino).

Cells are `Fin m × Fin n`, adjacent when they share a side in Mathlib's grid graph
`pathGraph m □ pathGraph n`. The loop is a cycle `c` of the grid graph
(`SimpleGraph.Walk.IsCycle`), traversed in the direction of the walk; its cells are exactly the
unshaded cells. Write `L` for the length of `c` and `c_j` for its `j`-th cell, indices taken mod
`L`. Rule 2: whenever `c_j` and `c_{j+1}` lie in different regions and the region of `c_j` has
number `k > 0`, the cells `c_{j+1}, …, c_{j+k}` lie in the region of `c_{j+1}` and `c_{j+k+1}`
does not.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **REMEMBERED LENGTH is NP-complete.** Source: Eua-anant, Apinyanon, Jirachaisri,
Ruangsuksriwong and Ruangwises (2025). -/
public theorem_wanted rememberedLength_npComplete :
    rememberedLengthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rememberedLengthDec

end MetaMathlibExt.Complexity.NPComplete.RememberedLength
