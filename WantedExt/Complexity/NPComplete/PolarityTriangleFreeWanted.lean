/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLARITY ON TRIANGLE-FREE GRAPHS is NP-complete

Source:
R. Churchley and J. Huang, "On the polarity and monopolarity of graphs", Journal of Graph Theory
76 (2014), 138-148, doi:10.1002/jgt.21755 (abstract: "we prove that recognizing polarity or
monopolarity remains NP-complete for triangle-free graphs");
ISGCI, *Information System on Graph Classes and their Inclusions*, class "triangle-free"
(gc_371), problem Polarity: NP-complete, with the reference to Churchley and Huang.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PolarityTriangleFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolarityTriangleFree

/-!
# POLARITY ON TRIANGLE-FREE GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is triangle-free.
QUESTION: is `G` polar, i.e. can `V` be partitioned into sets `A` and `B` such that `A` induces a
complete multipartite graph and `B` induces the complement of a complete multipartite graph (a
disjoint union of cliques)?

Polarity (Tyshkevich and Chernyak, 1985) generalizes bipartite and split graphs. The part `A`
induces (Mathlib's `G.induce A`) a complete multipartite graph, Mathlib's
`SimpleGraph.IsCompleteMultipartite` (non-adjacency is transitive); the rest `B = Aᶜ` induces a
disjoint union of cliques, i.e. a cluster graph: every two distinct vertices in the same connected
component are adjacent, the predicate `ClusterDeletion.IsClusterGraph` of `ClusterDeletionWanted`,
which is reused here (as in `ThreeColorabilityMonopolarWanted`, whose monopolar graphs are the
polar graphs with `A` independent). Either part may be empty. Triangle-freeness belongs to the
instance class, so it is a conjunct of `WellFormed`: Mathlib's `CliqueFree 3`. Churchley and Huang
prove that recognizing polar graphs remains NP-complete for triangle-free graphs; membership in NP
holds for all graphs (the partition is a certificate).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **POLARITY ON TRIANGLE-FREE GRAPHS is NP-complete.** Source: Churchley and Huang (2014);
ISGCI, class "triangle-free", problem Polarity. -/
public theorem_wanted polarityTriangleFree_npComplete :
    polarityTriangleFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L polarityTriangleFreeDec

end MetaMathlibExt.Complexity.NPComplete.PolarityTriangleFree
