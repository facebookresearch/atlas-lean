/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES for K₄-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES, comment:
remains NP-complete for graphs containing no complete subgraphs on 4 vertices (see the
construction for PARTITION INTO TRIANGLES in Chapter 3, Theorem 3.7);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (the unrestricted
problem, there called CLIQUE COVER).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesK4FreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesK4Free

open MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliques
  (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

/-!
# PARTITION INTO CLIQUES for K₄-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` containing no complete subgraph on 4 vertices, and a positive
integer `K ≤ |V|`. QUESTION: can the vertices of `G` be partitioned into `k ≤ K` disjoint sets
`V₁, V₂, …, V_k` such that, for `1 ≤ i ≤ k`, the subgraph induced by `Vᵢ` is a complete graph?

This is the restriction of PARTITION INTO CLIQUES
(`CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs`, [GT15]) to graphs with no `K₄`. The
instance, the graph, the parent well-formedness condition (simple edge list, `0 < K ≤ |V|`) and the
question are that module's; the restriction is added to `WellFormed` as Mathlib's
`SimpleGraph.CliqueFree 4` (no 4 pairwise adjacent vertices). Garey and Johnson point to their
PARTITION INTO TRIANGLES construction (Theorem 3.7, from EXACT COVER BY 3-SETS), whose graph has no
`K₄`; in a `K₄`-free graph on `3q` vertices every clique has at most 3 vertices, so a partition into
at most `q` cliques is a partition into triangles.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO CLIQUES is NP-complete for K₄-free graphs.** Source: Garey and Johnson
(1979), [GT15], comment, and Theorem 3.7. -/
public theorem_wanted partitionIntoCliquesK4Free_npComplete :
    partitionIntoCliquesK4FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesK4FreeDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesK4Free
