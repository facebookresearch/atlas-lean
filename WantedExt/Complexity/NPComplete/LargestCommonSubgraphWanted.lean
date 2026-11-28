/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LARGEST COMMON SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT49] LARGEST
COMMON SUBGRAPH (transformation from CLIQUE; no other reference given there).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LargestCommonSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LargestCommonSubgraph

/-!
# LARGEST COMMON SUBGRAPH is NP-complete

INSTANCE: graphs `G = (V₁, E₁)`, `H = (V₂, E₂)`, and a positive integer `K`.
QUESTION: do there exist subsets `E₁' ⊆ E₁` and `E₂' ⊆ E₂` with `|E₁'| = |E₂'| ≥ K` such that
the two subgraphs `G' = (V₁, E₁')` and `H' = (V₂, E₂')` are isomorphic?

A subset `E₁' ⊆ E₁` is the same thing as a spanning subgraph `G' ≤ G` on `V₁` (Mathlib's
order on `SimpleGraph`), with edge set `E₁'`; likewise for `H`. Isomorphism is Mathlib's
`SimpleGraph.Iso`. As in the source, the subgraphs keep all vertices, so a yes-instance has
`|V₁| = |V₂|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LARGEST COMMON SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT49]. -/
public theorem_wanted largestCommonSubgraph_npComplete :
    largestCommonSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L largestCommonSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.LargestCommonSubgraph
