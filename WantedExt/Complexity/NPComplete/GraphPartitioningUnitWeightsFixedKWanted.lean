/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH PARTITIONING with unit weights and fixed `K ≥ 3` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND14] GRAPH PARTITIONING, p. 209, comment:
"Remains NP-complete for fixed K ≥ 3 even if all vertex and edge weights are 1" (the entry's
reference is [Hyafil and Rivest, 1973], transformation from PARTITION INTO TRIANGLES);
L. Hyafil and R. L. Rivest, "Graph partitioning and constructing optimal decision trees are
polynomial complete problems", IRIA-Laboria Rapport 33 (1973).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphPartitioningUnitWeightsFixedKDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphPartitioningUnitWeightsFixedK

open MetaMathlibExt.Complexity.NPComplete.GraphPartitioning
  (GraphPartitioningInstance GraphPartitioningFeasible)

/-!
# GRAPH PARTITIONING with unit weights and fixed `K ≥ 3` is NP-complete

For a fixed integer `K ≥ 3`: INSTANCE: a graph `G = (V, E)`, weights `w(v) = 1` for each
`v ∈ V` and `l(e) = 1` for each `e ∈ E`, and a positive integer `J`. QUESTION: is there a
partition of `V` into disjoint sets `V₁, V₂, …, V_m` such that `∑_{v ∈ Vᵢ} w(v) ≤ K` (at most
`K` vertices) for `1 ≤ i ≤ m` and such that, if `E' ⊆ E` is the set of edges that have their
two endpoints in two different sets `Vᵢ`, then `∑_{e ∈ E'} l(e) ≤ J` (at most `J` such edges)?

This is GRAPH PARTITIONING (`GraphPartitioningWanted`, [ND14]) with `K` no longer part of the
instance. The instance is the vertex weights, the weighted edges and `J`, and `withBound i K`
inserts the fixed `K` to obtain an instance of that problem, whose `WellFormed` (one positive
weight per vertex, a simple edge list with positive lengths, `0 < K`, `0 < J`) and question
are reused unchanged; `WellFormed` here adds that every vertex weight and every edge length
equals `1`. For `K = 2` the problem is polynomial (by matching), so `3` is where hardness
starts. Hyafil and Rivest's transformation from PARTITION INTO TRIANGLES gives the case
`K = 3` with unit weights.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH PARTITIONING with unit weights is NP-complete for every fixed `K ≥ 3`.** Source:
Garey and Johnson (1979), [ND14], comment; Hyafil and Rivest (1973). -/
public theorem_wanted graphPartitioningUnitWeightsFixedK_npComplete (K : ℕ) (hK : 3 ≤ K) :
    graphPartitioningUnitWeightsDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (graphPartitioningUnitWeightsDec K)

end MetaMathlibExt.Complexity.NPComplete.GraphPartitioningUnitWeightsFixedK
