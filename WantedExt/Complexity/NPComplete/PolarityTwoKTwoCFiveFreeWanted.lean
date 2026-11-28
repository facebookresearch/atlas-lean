/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLARITY OF (2K₂, C₅)-FREE GRAPHS is NP-complete

Source:
V. B. Le and R. Nevries, "Complexity and algorithms for recognizing polar and monopolar
graphs", Theoretical Computer Science 528 (2014), 1-11, doi:10.1016/j.tcs.2014.01.032
(recognizing polar graphs is NP-complete on `{2K₂, C₅}`-free co-planar graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PolarityTwoKTwoCFiveFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolarityTwoKTwoCFiveFree

open MetaMathlibExt.Complexity.NPComplete.PolarityTriangleFree (IsPolar)

/-!
# POLARITY OF (2K₂, C₅)-FREE GRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)` with no induced subgraph isomorphic to `2K₂` (two disjoint edges)
and none isomorphic to the cycle `C₅` (ISGCI class `gc_1275`).
QUESTION: is `G` polar, i.e. can `V` be partitioned into `A` and `B` such that `G[A]` is a complete
multipartite graph (its complement is a disjoint union of cliques) and `G[B]` is a disjoint union of
cliques?

Le and Nevries define polar graphs this way ("a partition `V = A ∪ B` such that `A` induces a
complete multipartite graph and `B` the complement of a complete multipartite graph") and prove
that recognizing polar graphs is NP-complete already on `{2K₂, C₅}`-free co-planar graphs, a
subclass of the class here. Membership in NP: the partition is a polynomial certificate.

`G[A]` is `G.induce A` and `G[B]` is `G.induce Aᶜ`. Polarity is `PolarityTriangleFree.IsPolar` of
`PolarityTriangleFreeWanted`, reused here: `G[A]` is complete multipartite (Mathlib's
`SimpleGraph.IsCompleteMultipartite`: non-adjacency is transitive) and `G[B]` is a cluster graph
(`ClusterDeletion.IsClusterGraph`: any two distinct vertices joined by a walk are adjacent). A graph
is a cluster graph exactly when its complement is complete multipartite, so this is Le and Nevries'
condition that `B` induces the complement of a complete multipartite graph. `2K₂` is
`SimpleGraph.pathGraph 2 ⊕g SimpleGraph.pathGraph 2` and `C₅` is `SimpleGraph.cycleGraph 5`; induced
subgraphs are Mathlib's `SimpleGraph.IsIndContained`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **POLARITY OF (2K₂, C₅)-FREE GRAPHS is NP-complete.** Source: Le and Nevries (2014). -/
public theorem_wanted polarityTwoKTwoCFiveFree_npComplete :
    polarityTwoKTwoCFiveFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L polarityTwoKTwoCFiveFreeDec

end MetaMathlibExt.Complexity.NPComplete.PolarityTwoKTwoCFiveFree
