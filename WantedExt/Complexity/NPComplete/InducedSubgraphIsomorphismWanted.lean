/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED SUBGRAPH ISOMORPHISM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), INDUCED SUBGRAPH
ISOMORPHISM.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.InducedSubgraphIsomorphismDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedSubgraphIsomorphism

/-!
# INDUCED SUBGRAPH ISOMORPHISM is NP-complete

Two undirected graphs, pattern `H` and host `G`. The question is whether `H` is an induced
subgraph of `G`: an injective map from the vertices of `H` to those of `G` preserving adjacency
in both directions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDUCED SUBGRAPH ISOMORPHISM is NP-complete.** The decision problem INDUCED SUBGRAPH
ISOMORPHISM is in NP, and every decision problem in NP reduces to it by a polynomial-time
many-one reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), INDUCED SUBGRAPH ISOMORPHISM. -/
public theorem_wanted inducedSubgraphIsomorphism_npComplete :
    inducedSubgraphIsomorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inducedSubgraphIsomorphismDec

end MetaMathlibExt.Complexity.NPComplete.InducedSubgraphIsomorphism
