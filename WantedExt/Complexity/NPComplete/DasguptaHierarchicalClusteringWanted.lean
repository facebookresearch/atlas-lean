/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HIERARCHICAL CLUSTERING with Dasgupta's cost is NP-complete

Source:
S. Dasgupta, "A cost function for similarity-based hierarchical clustering", Proceedings of the
48th Annual ACM Symposium on Theory of Computing (STOC 2016), 118-127,
doi:10.1145/2897518.2897527 (arXiv:1510.05043), Section 2 (the cost function) and Section 4
(NP-hardness of finding a tree of minimum cost).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DasguptaHierarchicalClusteringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DasguptaHierarchicalClustering

open Cslib.Bioinformatics.Clustering.OptimalLeafOrdering

/-!
# HIERARCHICAL CLUSTERING with Dasgupta's cost is NP-complete

INSTANCE: an undirected graph `G = (V, E, w)` with positive integer edge weights `w`, and an
integer `K`. QUESTION: is there a rooted binary tree `T` whose leaves are in one-to-one
correspondence with `V` such that
`cost_G(T) = ∑_{{i, j} ∈ E} w_{ij} · |leaves(T[i ∨ j])| ≤ K`, where `T[i ∨ j]` is the smallest
subtree of `T` whose leaves include both `i` and `j` (the subtree rooted at their lowest common
ancestor)?

Dasgupta defines the cost for rooted trees that need not be binary and shows that some
cost-minimizing tree is always binary (Section 2.3, "The optimal tree is binary"), so asking for
a binary tree does not change the answer. Trees are CSLibExt's `Dendrogram` (the rooted binary
trees with labeled leaves of `CSLibExt.Bioinformatics.Clustering.OptimalLeafOrdering`), with
leaves labeled by the vertices `0, …, n - 1`; one-to-one correspondence means that the leaf list
is a permutation of `List.range n`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HIERARCHICAL CLUSTERING with Dasgupta's cost is NP-complete.** Source: Dasgupta (2016),
Section 4. -/
public theorem_wanted dasguptaHierarchicalClustering_npComplete :
    dasguptaHierarchicalClusteringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dasguptaHierarchicalClusteringDec

end MetaMathlibExt.Complexity.NPComplete.DasguptaHierarchicalClustering
