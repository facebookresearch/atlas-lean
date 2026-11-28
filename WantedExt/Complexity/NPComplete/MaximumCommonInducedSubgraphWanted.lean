/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM COMMON INDUCED SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MAXIMUM COMMON INDUCED
SUBGRAPH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumCommonInducedSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumCommonInducedSubgraph

/-!
# MAXIMUM COMMON INDUCED SUBGRAPH is NP-complete

Two undirected graphs and a bound `K`. The question is whether they have a common induced
subgraph on at least `K` vertices: subsets of vertices of the two graphs and a bijection
between them preserving adjacency in both directions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM COMMON INDUCED SUBGRAPH is NP-complete.** The decision problem MAXIMUM COMMON
INDUCED SUBGRAPH belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MAXIMUM COMMON INDUCED SUBGRAPH. -/
public theorem_wanted maximumCommonInducedSubgraph_npComplete :
    maximumCommonInducedSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumCommonInducedSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.MaximumCommonInducedSubgraph
