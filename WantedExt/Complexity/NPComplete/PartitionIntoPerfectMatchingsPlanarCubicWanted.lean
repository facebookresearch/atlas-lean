/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO PERFECT MATCHINGS for planar cubic graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT16] PARTITION INTO PERFECT MATCHINGS,
comment: remains NP-complete for planar cubic graphs;
T. J. Schaefer, "The complexity of satisfiability problems", Proceedings of the 10th Annual ACM
Symposium on Theory of Computing (STOC 1978), 216-226, doi:10.1145/800133.804350;
E. D. Demaine, K. Karntikoon and N. Pitimanaaree, "2-Colorable perfect matching is NP-complete in
2-connected 3-regular planar graphs", Theory of Computing Systems 69 (2025),
doi:10.1007/s00224-025-10221-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartitionIntoPerfectMatchingsPlanarCubicDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchingsPlanarCubic

open MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchings
  (PartitionIntoPerfectMatchingsInstance Graph PartitionIntoPerfectMatchingsFeasible)

/-!
# PARTITION INTO PERFECT MATCHINGS for planar cubic graphs is NP-complete

INSTANCE: a planar cubic graph `G = (V, E)` (every vertex has degree exactly 3) and a positive
integer `K ≤ |V|`. QUESTION: can the vertices of `G` be partitioned into `k ≤ K` disjoint sets
`V₁, …, V_k` such that, for `1 ≤ i ≤ k`, the subgraph induced by `Vᵢ` is a perfect matching
(consists entirely of vertices with degree one)?

This is the restriction of PARTITION INTO PERFECT MATCHINGS
(`WantedExt.Complexity.NPComplete.PartitionIntoPerfectMatchingsWanted`, [GT16]) to planar cubic
graphs. Garey and Johnson's comment records it (Schaefer 1978, stated there without proof);
Demaine, Karntikoon and Pitimanaaree supply the proof, already for `K = 2` on 2-connected
3-regular planar graphs, which gives hardness with `K` in the input. The instance, the graph, the
parent well-formedness condition (simple edge list, `0 < K ≤ |V|`) and the question are that
module's; the restriction is added to `WellFormed` as in `PartitionIntoCliquesCubicPlanarWanted`:
the shared MathlibExt predicate `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by
Fáry's theorem the usual notion for simple graphs) and Mathlib's `SimpleGraph.IsRegularOfDegree 3`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO PERFECT MATCHINGS is NP-complete for planar cubic graphs.** Source: Garey and
Johnson (1979), [GT16], comment; Schaefer (1978); Demaine, Karntikoon and Pitimanaaree (2025). -/
public theorem_wanted partitionIntoPerfectMatchingsPlanarCubic_npComplete :
    partitionIntoPerfectMatchingsPlanarCubicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoPerfectMatchingsPlanarCubicDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchingsPlanarCubic
