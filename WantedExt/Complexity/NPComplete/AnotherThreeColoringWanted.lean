/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ANOTHER 3-COLORING is NP-complete

Source:
D. P. Dailey, "Uniqueness of colorability and colorability of planar 4-regular graphs are
NP-complete", Discrete Mathematics 30(3) (1980), 289-293, doi:10.1016/0012-365X(80)90236-8;
Shalu M. A. and C. Antony, "Hardness transitions and uniqueness of acyclic colouring", Discrete
Applied Mathematics 345 (2024), 77-98, doi:10.1016/j.dam.2023.11.030, Section 1.4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AnotherThreeColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AnotherThreeColoring

/-!
# ANOTHER 3-COLORING is NP-complete

INSTANCE: a graph `G = (V, E)` and a proper 3-coloring `c : V → {0, 1, 2}` of `G`.
QUESTION: does `G` have a proper 3-coloring that is not obtained from `c` by permuting the
colors, i.e. a proper 3-coloring `f` such that `f ≠ σ ∘ c` for every permutation `σ` of the
three colors?

This is the another-solution problem of GRAPH 3-COLORABILITY ([GT4] with `K = 3`). Shalu and
Antony (Section 1.4) state ANOTHER `k`-COLOURING `[R_swap]` with instance "a graph `G`, and a
`k`-colouring `f` of `G`" and question "Is there another `k`-colouring of `G` up to colour
swaps?", two colorings being equivalent when "the same up to colour swaps", and record that
"Dailey proved that for all `k ≥ 3`, ANOTHER `k`-COLOURING `[R_swap]` is NP-hard" (by a
reduction from `k`-COLOURABILITY), hence NP-complete. This module states the case `k = 3`.
A proper 3-coloring is Mathlib's `SimpleGraph.Coloring (Fin 3)`; two colorings are the same up
to color swaps exactly when one is the other composed with a permutation of `Fin 3`.

The graph is simple and given by an edge list on `Fin n`; the coloring is the list of the
colors `c(0), …, c(n - 1)`, each below `3`, and it must be proper. The list has length `n`, so
the vertex count is bounded by the input length.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ANOTHER 3-COLORING is NP-complete.** Source: Dailey (1980), as recorded by Shalu and
Antony (2024). -/
public theorem_wanted anotherThreeColoring_npComplete :
    anotherThreeColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L anotherThreeColoringDec

end MetaMathlibExt.Complexity.NPComplete.AnotherThreeColoring
