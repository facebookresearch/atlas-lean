/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BIPARTITE EDGE COLORING WITH CONFLICT PARTITION is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2, Section 2, entry CHROMATIC INDEX (reference: A. A. Bertossi,
"An NP-complete coloring problem in bipartite graphs", manuscript (1983); the manuscript was not
available);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 2 (1981), 393-405,
doi:10.1016/0196-6774(81)90037-7, problem [5] CHROMATIC INDEX (the base problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BipartiteEdgeColoringConflictPartitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BipartiteEdgeColoringConflictPartition

open EdgeColoring (EdgeColoringInstance)

/-!
# BIPARTITE EDGE COLORING WITH CONFLICT PARTITION is NP-complete

INSTANCE: a bipartite graph `G = (V, E)`, a partition of `E` into disjoint sets, and a positive
integer `K`.
QUESTION: can the edges of `G` be colored with at most `K` colors so that no two edges sharing an
endpoint get the same color, and no two edges in the same set of the partition get the same
color?

Johnson's column (1984), updating CHROMATIC INDEX ("can `E` be partitioned into disjoint sets
`E₁, E₂, …, E_k`, with `k ≤ K`, such that, for `1 ≤ i ≤ k`, no two edges in `Eᵢ` share a common
endpoint in `G`?", problem [5] of the 1981 column): "The polynomial time solvable case of
bipartite graphs becomes NP-complete when generalized by adding to the instance a partition of
the edges and requiring that no two edges in the same subset of the partition be assigned the
same color [Bertossi], a result that holds even if the maximum vertex degree and set cardinality
are both 3 (if they are both 2, polynomial time solvability returns)."

The graph and `K` are a CHROMATIC INDEX instance of `EdgeColoringWanted`
(`EdgeColoring.EdgeColoringInstance`: vertex count `n`, edge list, `K`) with its well-formedness
`EdgeColoring.WellFormed` (a simple edge list on `Fin n`), and a coloring is given as there: a
list with one color below `K` per listed edge, distinct on edges at distinct positions that share
an endpoint. The partition is a second list giving each edge, by position, the label of its set:
edges with equal labels form one set of the partition (every partition of `E` arises this way).
Bipartiteness is Mathlib's `SimpleGraph.IsBipartite` of the graph
`Cslib.Complexity.Karp.edgeGraph`, and `0 < K` is Johnson's "positive integer `K`".

Membership in NP: the coloring is the certificate, and bipartiteness is checked in polynomial
time. Isolated vertices change neither the class nor the answer, so the binary vertex count does
not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BIPARTITE EDGE COLORING WITH CONFLICT PARTITION is NP-complete.** Source: Johnson (1984),
Section 2, CHROMATIC INDEX (Bertossi 1983). -/
public theorem_wanted bipartiteEdgeColoringConflictPartition_npComplete :
    bipartiteEdgeColoringConflictPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bipartiteEdgeColoringConflictPartitionDec

end MetaMathlibExt.Complexity.NPComplete.BipartiteEdgeColoringConflictPartition
