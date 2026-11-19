/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED EDGE-SUBGRAPH on graphs of maximum degree 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT28] EDGE-SUBGRAPH, comment;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 12 and its Remark (2)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import WantedExt.Complexity.NPComplete.EdgeSubgraphWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedEdgeSubgraphMaxDegreeThree

/-!
# CONNECTED EDGE-SUBGRAPH on graphs of maximum degree 3 is NP-complete

INSTANCE: a graph `G = (V, E)` with no vertex of degree exceeding 3, and a positive integer
`K ≤ |E|`. QUESTION: is there a subset `E' ⊆ E` with `|E'| ≥ K` such that the subgraph
`G' = (V, E')` is connected and is an edge graph (line graph) of some graph?

This is the variant of EDGE-SUBGRAPH (`WantedExt.Complexity.NPComplete.EdgeSubgraphWanted`,
Garey and Johnson [GT28]) recorded in the [GT28] comment: "If we require that the subgraph be
connected, the degree bound for NP-completeness can be reduced to 3." Yannakakis (1978),
Theorem 12, proves EDGE-SUBGRAPH NP-complete on graphs of maximum degree 4, and his Remark (2)
after it reads: "If a connectivity requirement is included, then the best bound can be brought
down to 3." (Without the connectivity requirement, maximum degree 3 is polynomial: Remark (1).)

The instance type, the graph and `EdgeSubgraph.WellFormed` (a simple edge list on `Fin n` and
`0 < K ≤ |E|`) are reused from EDGE-SUBGRAPH; the degree bound is added to well-formedness, with
Mathlib's `SimpleGraph.degree`. `E'` is a sublist of the duplicate-free edge list, so its length
is `|E'|`. `G' = (V, E')` is the spanning subgraph `edgeGraph n E'` on all `n` vertices, as in
Garey and Johnson's question and in Yannakakis's edge-deletion problems, where deleting edges
keeps every vertex. It must be connected (Mathlib's `SimpleGraph.Connected`) and a line graph
(the shared MathlibExt predicate `MetaMathlibExt.SimpleGraph.IsLineGraph`: isomorphic to
Mathlib's `SimpleGraph.lineGraph` of a finite simple graph). A connected `(V, E')` has
`|V| ≤ |E'| + 1`, so yes-instances have `n ≤ |E| + 1` and the binary vertex count does not
affect membership in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance: EDGE-SUBGRAPH well-formedness (a simple edge list on
`Fin n` and `0 < K ≤ |E|`), and every vertex of the graph has degree at most 3. -/
def WellFormed (i : EdgeSubgraph.EdgeSubgraphInstance) : Prop :=
  EdgeSubgraph.WellFormed i ∧ ∀ v, (EdgeSubgraph.Graph i).degree v ≤ 3

/-- Some sublist `E'` of the edge list with at least `K` entries spans a connected subgraph
`(V, E')` on all vertices that is a line graph. -/
def ConnectedEdgeSubgraphFeasible (i : EdgeSubgraph.EdgeSubgraphInstance) : Prop :=
  ∃ es : List (ℕ × ℕ), es.Sublist i.2.1 ∧ i.2.2 ≤ es.length ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 es).Connected ∧
      MetaMathlibExt.SimpleGraph.IsLineGraph (Cslib.Complexity.Karp.edgeGraph i.1 es)

open Classical in
/-- CONNECTED EDGE-SUBGRAPH on graphs of maximum degree 3 as a decision problem over
bitstrings. -/
noncomputable def connectedEdgeSubgraphMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeSubgraph.EdgeSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ ConnectedEdgeSubgraphFeasible i)
  | none => false

/-- **CONNECTED EDGE-SUBGRAPH is NP-complete on graphs of maximum degree 3.** Source: Garey
and Johnson (1979), [GT28], comment; Yannakakis (1978), Theorem 12, Remark (2). -/
public theorem_wanted connectedEdgeSubgraphMaxDegreeThree_npComplete :
    connectedEdgeSubgraphMaxDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L connectedEdgeSubgraphMaxDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.ConnectedEdgeSubgraphMaxDegreeThree
