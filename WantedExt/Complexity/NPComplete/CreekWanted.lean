/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CREEK is NP-complete

Source:
A. Uejima and K. Oe, "The computational complexity of Creek puzzles on several grids", Journal
of Information Processing 28 (2020), 911-918, doi:10.2197/ipsjjip.28.911, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CreekDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Creek

/-!
# CREEK is NP-complete

Uejima and Oe (Section 1) define the Creek Decision Problem (the 4-Creek Decision Problem):
INSTANCE: a square grid `B` of size `m × n`, with circled integers in `{0, 1, 2, 3, 4}` placed
at some lattice points on `B`.
QUESTION: can some squares of `B` be colored blue while satisfying (1) the number inside each
circle dictates how many of the squares touched by the circle are colored blue, and (2) all
uncolored squares form a single contiguous region connected by edges?
They prove it NP-complete (Theorem 1).

The board is given explicitly, as its `(m + 1) × (n + 1)` lattice points row by row: entry `b`
of row `a` is `0` when no circle sits at the lattice point `(a, b)`, and `d + 1` when a circle
with the number `d` sits there; so the input size grows with the area of the board, as for the
board in the source. The squares are `Fin m × Fin n`, adjacent when they share an edge in
Mathlib's grid graph `pathGraph m □ pathGraph n`. The lattice point `(a, b)` is a corner of
(touches) the squares `(r, c)` with `r ∈ {a - 1, a}` and `c ∈ {b - 1, b}` that lie on the grid.
Rule (2) says that the uncolored squares induce a connected subgraph of the grid graph
(`SimpleGraph.Connected`, which also makes this region nonempty, as "a single region" reads).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CREEK is NP-complete.** Source: Uejima and Oe (2020), Theorem 1. -/
public theorem_wanted creek_npComplete :
    creekDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L creekDec

end MetaMathlibExt.Complexity.NPComplete.Creek
