/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NURIKABE is NP-complete

Source:
M. Holzer, A. Klein and M. Kutrib, "On the NP-completeness of the NURIKABE pencil puzzle and
variants thereof", Proceedings of the 3rd International Conference on Fun with Algorithms
(FUN 2004) (rules 1-4 and Theorem 1);
M. Holzer, A. Klein, M. Kutrib and O. Ruepp, "Computational complexity of NURIKABE",
Fundamenta Informaticae 110(1-4) (2011), 159-174, doi:10.3233/FI-2011-534;
first proved by B. McPhail, "The complexity of puzzles: NP-completeness results for Nurikabe
and Minesweeper", BA thesis, Reed College (2003).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NurikabeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nurikabe

/-!
# NURIKABE is NP-complete

Nurikabe is played on a finite rectangular grid, some of whose cells are labelled with natural
numbers. The cells are filled black or white so that (Holzer, Klein and Kutrib 2004):
1. cells containing numbers are filled white;
2. a natural number defines a number of connected white cells (linked horizontally or
   vertically); each area of white cells contains only one natural number, and the areas are
   separated by black cells;
3. all black cells are linked to be a connected area;
4. black cells cannot be linked to form a `2 × 2` square.

INSTANCE: an `m × n` grid with some cells labelled by natural numbers.
QUESTION: can the cells be filled so that rules 1-4 hold?

The grid is given row by row: entry `c` of row `r` is `0` for an unlabelled cell and `k ≥ 1`
for a cell labelled `k`. `WellFormed` requires `m, n ≥ 1` and rows of equal length. A filling
is a function `ℕ → ℕ → Bool` (`true` = black) read on the grid. Cells are `Fin m × Fin n`,
linked horizontally or vertically when adjacent in Mathlib's grid graph
`pathGraph m □ pathGraph n`. An area of white cells is a connected component
(`SimpleGraph.ConnectedComponent`) of the subgraph the grid graph induces on the white cells;
rule 2 says each such area contains exactly one labelled cell and has as many cells as its
label. Rule 3 is `SimpleGraph.Preconnected` of the subgraph induced on the black cells.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NURIKABE is NP-complete.** Source: Holzer, Klein and Kutrib (2004), Theorem 1; Holzer,
Klein, Kutrib and Ruepp (2011); McPhail (2003). -/
public theorem_wanted nurikabe_npComplete :
    nurikabeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nurikabeDec

end MetaMathlibExt.Complexity.NPComplete.Nurikabe
