/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO PERFECT MATCHINGS with K = 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT16] PARTITION INTO PERFECT MATCHINGS,
comment: remains NP-complete for `K = 2`;
T. J. Schaefer, "The complexity of satisfiability problems", Proceedings of the 10th Annual ACM
Symposium on Theory of Computing (STOC 1978), 216-226, doi:10.1145/800133.804350;
E. D. Demaine, K. Karntikoon and N. Pitimanaaree, "2-Colorable perfect matching is NP-complete in
2-connected 3-regular planar graphs", Theory of Computing Systems 69 (2025),
doi:10.1007/s00224-025-10221-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartitionIntoPerfectMatchingsTwoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchingsTwo

open MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchings
  (PartitionIntoPerfectMatchingsInstance PartitionIntoPerfectMatchingsFeasible)

/-!
# PARTITION INTO PERFECT MATCHINGS with K = 2 is NP-complete

INSTANCE: a graph `G = (V, E)` (with `2 ≤ |V|`). QUESTION: can the vertices of `G` be
partitioned into `k ≤ 2` disjoint sets `V₁, …, V_k` such that, for `1 ≤ i ≤ k`, the subgraph
induced by `Vᵢ` is a perfect matching (consists entirely of vertices with degree one)?

Garey and Johnson [GT16] state PARTITION INTO PERFECT MATCHINGS with `K` in the instance
(Schaefer 1978, from NOT-ALL-EQUAL 3SAT) and comment that it remains NP-complete for `K = 2`.
Demaine, Karntikoon and Pitimanaaree call the `K = 2` problem 2-COLORABLE PERFECT MATCHING
(colour the vertices with two colours so that each vertex has exactly one neighbour of its own
colour) and record that Schaefer proved it NP-complete in general graphs.

The instance, the graph and the question are those of `PartitionIntoPerfectMatchingsWanted`,
reused unchanged; the restriction adds to the parent's well-formedness (simple edge list,
`0 < K ≤ |V|`) that the bound in the instance is `2`, as in `FixedKColorabilityWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO PERFECT MATCHINGS with `K = 2` is NP-complete.** Source: Garey and Johnson
(1979), [GT16], comment; Schaefer (1978); Demaine, Karntikoon and Pitimanaaree (2025). -/
public theorem_wanted partitionIntoPerfectMatchingsTwo_npComplete :
    partitionIntoPerfectMatchingsTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoPerfectMatchingsTwoDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchingsTwo
