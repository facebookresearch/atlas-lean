/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ISOMORPHIC EDGE BISECTION OF TREES is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fourth edition), Journal of
Algorithms 3 (1982), 288-300, doi:10.1016/0196-6774(82)90026-8, comment to problem [2]
PARTITIONED GRAPH ISOMORPHISM (attribution: R. L. Graham and R. W. Robinson, private
communication (1982); no published proof was available to us).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TreeIsomorphicEdgeBisectionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreeIsomorphicEdgeBisection

/-!
# ISOMORPHIC EDGE BISECTION OF TREES is NP-complete

INSTANCE: a tree `T = (V, E)`.
QUESTION: is there a partition `E = E₁ ∪ E₂` of `E` into disjoint sets such that the graphs
`T₁ = (V, E₁)` and `T₂ = (V, E₂)` are isomorphic?

Johnson's fourth column, in the comment to PARTITIONED GRAPH ISOMORPHISM, records: "The variant
in which we are just given G, and are asked whether there is a partition E = E₁ ∪ E₂ such that
the two graphs G₁ = (V,E₁) and G₂ = (V,E₂) are isomorphic, is NP-complete even for trees",
crediting Graham and Robinson, and adds that for trees it is polynomial if `E₁` and `E₂` must
be connected (Harary and Robinson). This module states the tree case.

The tree is given by its vertex count `n` and an edge list, as a `SimpleGraph (Fin n)` through
`Cslib.Complexity.Karp.edgeGraph`; `WellFormed` asks for a simple edge list and Mathlib's
`SimpleGraph.IsTree` (connected and acyclic), so `n = |E| + 1`. As in
`PartitionedGraphIsomorphismWanted`, a partition of `E` into two disjoint sets is a pair of
spanning subgraphs `T₁`, `T₂` with `Disjoint T₁ T₂` and `T₁ ⊔ T₂ = T`; both keep every vertex of
`V`, so `T₁ ≃g T₂` (Mathlib `SimpleGraph.Iso`) is an isomorphism of graphs on the full vertex set.
The partition and the isomorphism are a certificate of polynomial size, so the problem is in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ISOMORPHIC EDGE BISECTION OF TREES is NP-complete.** Source: Johnson, NP-completeness
column (1982), comment to problem [2] (Graham and Robinson). -/
public theorem_wanted treeIsomorphicEdgeBisection_npComplete :
    treeIsomorphicEdgeBisectionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treeIsomorphicEdgeBisectionDec

end MetaMathlibExt.Complexity.NPComplete.TreeIsomorphicEdgeBisection
