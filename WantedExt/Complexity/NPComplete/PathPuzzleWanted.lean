/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH PUZZLE (complete row and column information) is NP-complete

Source:
J. Bosboom, E. D. Demaine, M. L. Demaine, A. Hesterberg, R. Kimball and J. Kopinsky, "Path
puzzles: discrete tomography with a path constraint is hard", Graphs and Combinatorics 36
(2020), 251-267, doi:10.1007/s00373-019-02092-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PathPuzzleDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathPuzzle

/-!
# PATH PUZZLE (complete row and column information) is NP-complete

Bosboom, Demaine, Demaine, Hesterberg, Kimball and Kopinsky (2020): "A puzzle consists of a
(rectangular) grid of cells with two exits (or "doors") on the boundary and numerical
constraints on some subset of the rows and columns. A solution consists of a single
non-intersecting path which starts and ends at two boundary doors and which passes through a
number of cells in each constrained row and column equal to the given numerical clue."
Theorem 3.4: "Perfect-information Path Puzzle (with all row and column labels given as labels)
is NP-, #P- and ASP-hard"; the abstract states that path puzzles with complete row and column
information are strongly NP-complete. This module states the perfect-information version:
every row and every column has a clue.

The grid has `R.length` rows and `C.length` columns, numbered from `0`; `R[r]` and `C[c]` are
the clues. A door is a boundary cell together with the side of the grid it opens to
(`0` top, `1` bottom, `2` left, `3` right). The path is a path (a walk without repeated cells)
in the grid graph (the box product of two path graphs, i.e. orthogonal adjacency of cells) from
the cell of the first door to the cell of the second door.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PATH PUZZLE with complete row and column information is NP-complete.** Source: Bosboom,
Demaine, Demaine, Hesterberg, Kimball and Kopinsky (2020), Theorem 3.4. -/
public theorem_wanted pathPuzzle_npComplete :
    pathPuzzleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathPuzzleDec

end MetaMathlibExt.Complexity.NPComplete.PathPuzzle
