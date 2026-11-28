/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED EDGE-SUBGRAPH on graphs of maximum degree 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT28] EDGE-SUBGRAPH, comment;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 12 and its Remark (2)).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import CSLibExt.Complexity.NPComplete.EdgeSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedEdgeSubgraphMaxDegreeThree

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

end MetaMathlibExt.Complexity.NPComplete.ConnectedEdgeSubgraphMaxDegreeThree
