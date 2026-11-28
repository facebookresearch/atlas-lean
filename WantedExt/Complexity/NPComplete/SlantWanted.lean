/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SLANT is NP-complete

Source:
J. Lynch and J. Spalding-Jamieson, "Slant/Gokigen Naname is NP-complete, and some variations are
in P", arXiv:2502.13536 (2025) (Section 1: the rules; Theorem 7).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SlantDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Slant

/-!
# SLANT is NP-complete

Lynch and Spalding-Jamieson, Section 1: "Slant is played on a square grid, some of whose vertices
may be given numbers (henceforth called a Slant board). The objective is to add a single diagonal
line to each square obeying the following constraints:
1. There is no cycle formed by diagonal lines.
2. If a vertex has a designated number `k ∈ {0, 1, 2, 3, 4}`, the number of diagonal lines
   adjacent to the vertex must be exactly `k`."

INSTANCE: a Slant board. QUESTION: does it have a solution? Theorem 7: "Deciding if there is a
solution to an `n × n` Slant puzzle is NP-complete"; the boards here are `H × W` (Section 3 also
treats `n × m` boards), and the square boards are among them.

The board is given explicitly by its vertices, row by row: entry `c` of row `r` is
`(numbered, number)` for the vertex `(r, c)`, with `number = 0` when the vertex is unnumbered. A
board with `H + 1` rows of `W + 1` vertices has the `H · W` squares `(r, c)`, `r < H`, `c < W`. A
filling `d : ℕ → ℕ → Bool` puts in square `(r, c)` the diagonal `(r, c) – (r + 1, c + 1)` when
`d r c = true` and `(r, c + 1) – (r + 1, c)` otherwise. `diagGraph` is the graph of these
diagonals on the vertices; the cycle constraint is Mathlib's `SimpleGraph.IsAcyclic`, and the
number of diagonals adjacent to a vertex is the number of its neighbors in that graph (the four
squares around a vertex join it to four different vertices).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SLANT is NP-complete.** Source: Lynch and Spalding-Jamieson (2025), Theorem 7. -/
public theorem_wanted slant_npComplete :
    slantDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L slantDec

end MetaMathlibExt.Complexity.NPComplete.Slant
