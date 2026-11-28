/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACYCLIC PARTITION for trees is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND15] ACYCLIC PARTITION, comment;
the pseudo-polynomial algorithm cited there: J. A. Lukes, "Efficient algorithm for the
partitioning of trees", IBM Journal of Research and Development 18 (1974), 217-224,
doi:10.1147/rd.183.0217.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AcyclicPartitionTreesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AcyclicPartitionTrees

/-!
# ACYCLIC PARTITION for trees is NP-complete

INSTANCE: a directed graph `G = (V, A)` that is a tree, a weight `w(v) ∈ Z⁺` for each `v ∈ V`,
a cost `c(a) ∈ Z⁺` for each `a ∈ A`, and positive integers `B` and `K`. QUESTION: is there a
partition of `V` into disjoint sets `V₁, ..., Vₘ` such that the quotient digraph `G'` on the
blocks is acyclic, the sum of the weights of the vertices in each `Vᵢ` does not exceed `B`, and
the sum of the costs of all arcs having their endpoints in different sets does not exceed `K`?

This is ACYCLIC PARTITION (`WantedExt.Complexity.NPComplete.AcyclicPartitionWanted`, Garey and
Johnson [ND15]) restricted to trees, as recorded in the [ND15] comment: "If G is a tree the
general problem is NP-complete in the ordinary sense, but can be solved in pseudo-polynomial
time [Lukes, 1974]." Garey and Johnson give no reference for this NP-completeness result; their
entry is its literature record. Numbers use the binary encoding.

"`G` is a tree" is read as: the underlying undirected graph (an edge `{u, v}` for each arc
`(u, v)`) is a tree (Mathlib's `SimpleGraph.IsTree`), and no two arcs join the same two vertices
in opposite directions, so `G` is an oriented tree with `|V| - 1` arcs. The narrower reading,
rooted trees, is equally hard: on an out-star (every arc leaves one centre) every partition has
an acyclic quotient, because blocks without the centre have no outgoing arcs, so the question
is a KNAPSACK instance (choose leaves of total weight at most `B` minus the centre's weight to
share the centre's block, so that the arcs to the other leaves cost at most `K` in total).

The instance type, `AcyclicPartition.WellFormed` (positive weights and costs, a loopless
directed graph without repeated arcs, `0 < B`, `0 < K`) and
`AcyclicPartition.AcyclicPartitionFeasible` are reused unchanged; the tree condition is added
to well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ACYCLIC PARTITION is NP-complete for trees.** Source: Garey and Johnson (1979), [ND15],
comment. -/
public theorem_wanted acyclicPartitionTrees_npComplete :
    acyclicPartitionTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L acyclicPartitionTreesDec

end MetaMathlibExt.Complexity.NPComplete.AcyclicPartitionTrees
