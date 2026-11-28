/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NORINORI is NP-complete

Source:
M. Biro and C. Schmidt, "Computational complexity and bounds for Norinori and LITS", Proc. 33rd
European Workshop on Computational Geometry (EuroCG 2017), Malmö (2017), Theorem 1,
https://itn-web.it.liu.se/~chrsc91/papers/norinori-lits.pdf.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NorinoriDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Norinori

/-!
# NORINORI is NP-complete

Biro and Schmidt (2017): Norinori is "played on an `m × n` square grid that has been partitioned
into connected polyomino regions"; "the solver places black squares in the polyominos such that
the final board satisfies the following two properties:
1. Each black square has exactly one black neighbor.
2. There are exactly 2 black squares in each polyomino region."
Theorem 1: "Determining if a Norinori board is solvable is NP-complete".

INSTANCE: an `m × n` grid partitioned into connected regions.
QUESTION: can squares be made black so that every black square has exactly one black neighbor
and every region has exactly two black squares?

Representation. The grid is given row by row, each square carrying the label of its region; a
region is the set of squares with one label, so the instance size is proportional to the area
plus the binary length of the labels. Squares are `Fin m × Fin n`, neighbors when adjacent in
Mathlib's grid graph `pathGraph m □ pathGraph n`; `WellFormed` requires every region to be
connected (`SimpleGraph.Preconnected` of the subgraph the grid graph induces on it). A choice of
black squares is a function `ℕ → ℕ → Bool` read on the grid.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NORINORI is NP-complete.** Source: Biro and Schmidt (2017), Theorem 1. -/
public theorem_wanted norinori_npComplete :
    norinoriDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L norinoriDec

end MetaMathlibExt.Complexity.NPComplete.Norinori
