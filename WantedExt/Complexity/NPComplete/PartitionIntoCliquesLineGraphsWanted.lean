/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES for line graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES (comment: "Remains
NP-complete for edge graphs [Arjomandi, 1977]"); D. S. Johnson, "The NP-completeness column: an
ongoing guide" (sixteenth edition), Journal of Algorithms 6 (1985), 434-451,
doi:10.1016/0196-6774(85)90012-4, Table 1 (row "Edge (or Line)", partition into cliques); A.
Munaro, "Bounded clique cover of some sparse graphs", Discrete Mathematics 340 (2017), 2208-2216,
doi:10.1016/j.disc.2017.04.004 (NP-complete already for line graphs of triangle-free graphs, a
subclass).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesLineGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLineGraphs

open MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliques
  (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

/-!
# PARTITION INTO CLIQUES for line graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is an edge (line) graph, and a positive integer `K ≤ |V|`.
QUESTION: can the vertices of `G` be partitioned into `k ≤ K` disjoint sets `V₁, ..., V_k` such
that, for `1 ≤ i ≤ k`, the subgraph induced by `Vᵢ` is a complete graph?

This is PARTITION INTO CLIQUES ([GT15], `PartitionIntoCliquesDefs`) restricted to line graphs,
the restriction recorded in the entry's comment. The instance type, `PartitionIntoCliques.Graph`,
`PartitionIntoCliques.WellFormed` (simple edge list, `0 < K ≤ |V|`) and
`PartitionIntoCliques.PartitionIntoCliquesFeasible` are the parent's, unchanged; `WellFormed` adds
`MetaMathlibExt.SimpleGraph.IsLineGraph` (from `MathlibExt.Combinatorics.SimpleGraph.LineGraph`:
isomorphic to Mathlib's `SimpleGraph.lineGraph` of a graph on some `Fin k`), as in
`LineGraphHamiltonianCircuitWanted`. The instance is the line graph itself. The subclass of line
graphs of triangle-free graphs is `PartitionIntoCliquesLineGraphTriangleFreeWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO CLIQUES is NP-complete for line graphs.** Source: Garey and Johnson
(1979), [GT15], comment; Johnson, NP-completeness column (1985), Table 1; Munaro (2017). -/
public theorem_wanted partitionIntoCliquesLineGraphs_npComplete :
    partitionIntoCliquesLineGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesLineGraphsDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLineGraphs
