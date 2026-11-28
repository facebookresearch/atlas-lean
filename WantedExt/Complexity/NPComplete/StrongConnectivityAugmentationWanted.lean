/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG CONNECTIVITY AUGMENTATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND19] STRONG CONNECTIVITY
AUGMENTATION;
K. P. Eswaran and R. E. Tarjan, "Augmentation problems", SIAM Journal on Computing 5 (1976),
653-665, doi:10.1137/0205044.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StrongConnectivityAugmentationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentation

/-!
# STRONG CONNECTIVITY AUGMENTATION is NP-complete

Given a directed graph `G = (V, A)`, a weight `w(u, v) ∈ Z⁺` for each ordered pair
`(u, v) ∈ V × V`, and a positive integer `B`, is there a set `A'` of ordered pairs of
vertices from `V` such that `∑_{a ∈ A'} w(a) ≤ B` and the graph `G' = (V, A ∪ A')` is
strongly connected?

The vertices are `0, ..., n - 1`; as in the repository's other directed-graph problems,
`G` has no loops. The weights are an `n × n` matrix of positive entries. `A'` is a list of
ordered pairs of vertices; listing a pair twice only adds its weight twice. Strong
connectivity: every vertex reaches every vertex along arcs of `G'`
(`Relation.ReflTransGen` of the adjacency of a Mathlib `Digraph`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STRONG CONNECTIVITY AUGMENTATION is NP-complete.** Source: Garey and Johnson
(1979), [ND19]; Eswaran and Tarjan (1976). -/
public theorem_wanted strongConnectivityAugmentation_npComplete :
    strongConnectivityAugmentationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L strongConnectivityAugmentationDec

end MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentation
