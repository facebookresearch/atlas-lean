/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH SQUARE ROOT is NP-complete

Source:
R. Motwani and M. Sudan, "Computing roots of graphs is hard", Discrete Applied Mathematics 54
(1994), 81-88, doi:10.1016/0166-218X(94)00023-9;
recorded in B. Farzad and M. Karimi, "Square-root finding problem in graphs, a complete dichotomy
theorem", arXiv:1210.7684 (2012), Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphSquareRootDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphSquareRoot

/-!
# GRAPH SQUARE ROOT is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected). QUESTION: is there a graph `H` on the
same vertex set `V` with `H² = G`, that is, distinct `u` and `v` are adjacent in `G` exactly when
their distance in `H` is at most `2`?

Motwani and Sudan prove that deciding whether a graph has a square root is NP-complete; Farzad
and Karimi (Section 1) record it: "Motwani and Sudan proved that it is NP-complete to determine if
a given graph G is the square of some graph".

The graph is given by its vertex count and a simple edge list (`Cslib.Complexity.Karp.edgeGraph`).
The square is MathlibExt's `SimpleGraph.square`: distinct vertices are adjacent when they are
adjacent in `H` or have a common neighbor in `H`, i.e. when their distance in `H` is `1` or `2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH SQUARE ROOT is NP-complete.** Source: Motwani and Sudan (1994). -/
public theorem_wanted graphSquareRoot_npComplete :
    graphSquareRootDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphSquareRootDec

end MetaMathlibExt.Complexity.NPComplete.GraphSquareRoot
