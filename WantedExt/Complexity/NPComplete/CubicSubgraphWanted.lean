/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CUBIC SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT32] CUBIC SUBGRAPH (credited
there to V. Chvátal, 1976); I. A. Stewart, "Deciding whether a planar graph has a cubic
subgraph is NP-complete", Discrete Mathematics 126 (1994), 349-357,
doi:10.1016/0012-365X(94)90277-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CubicSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CubicSubgraph

/-!
# CUBIC SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is there a nonempty subset `E' ⊆ E` such that in
the graph `G' = (V, E')` every vertex has either degree 0 or degree 3?

The subset `E'` is a spanning subgraph `H ≤ G` with a nonempty edge set, and degrees are
Mathlib's `SimpleGraph.degree`. Equivalently, `G` has a nonempty 3-regular subgraph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CUBIC SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT32];
Stewart (1994). -/
public theorem_wanted cubicSubgraph_npComplete :
    cubicSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cubicSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.CubicSubgraph
