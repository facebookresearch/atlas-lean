/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE-SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT28] EDGE-SUBGRAPH;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 12);
M. Yannakakis, "Edge-deletion problems", SIAM Journal on Computing 10 (1981),
297-309, doi:10.1137/0210021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeSubgraph

/-!
# EDGE-SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: is there a subset
`E' ⊆ E` with `|E'| ≥ K` such that the subgraph `G' = (V', E')`, where `V'` is the set of
endpoints of edges in `E'`, is an edge graph (line graph) of some graph?

`E'` is a sublist of the edge list; under `WellFormed` the edge list has no duplicate edges in
either orientation, so the sublist's length is `|E'|` and the edge list's length is `|E|`.
`G' = (V', E')` is the spanning graph `edgeGraph n E'` induced on its support (the vertices
with a neighbour, which under `WellFormed` are exactly the endpoints of edges in `E'`). "Is the
edge graph of some graph" is the shared MathlibExt predicate
`MetaMathlibExt.SimpleGraph.IsLineGraph`: isomorphic to Mathlib's `SimpleGraph.lineGraph` of a
finite simple graph. Taking `V'` or all of `V` as the vertex set gives the same problem: an
isolated vertex of a line graph is an edge of the root graph forming its own component, so
adding or deleting isolated vertices preserves being a line graph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev EdgeSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : EdgeSubgraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |E|`, the length of the edge list. -/
def WellFormed (i : EdgeSubgraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

open Classical in
/-- Some sublist `E'` of the edge list with at least `K` entries forms, on the endpoints of its
edges, a line graph. -/
def EdgeSubgraphFeasible (i : EdgeSubgraphInstance) : Prop :=
  ∃ es : List (ℕ × ℕ), es.Sublist i.2.1 ∧ i.2.2 ≤ es.length ∧
    MetaMathlibExt.SimpleGraph.IsLineGraph
      ((Cslib.Complexity.Karp.edgeGraph i.1 es).induce
        (Cslib.Complexity.Karp.edgeGraph i.1 es).support)

open Classical in
/-- EDGE-SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def edgeSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ EdgeSubgraphFeasible i)
  | none => false

/-- **EDGE-SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT28];
Yannakakis (1978), Theorem 12; Yannakakis (1981). -/
public theorem_wanted edgeSubgraph_npComplete :
    edgeSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.EdgeSubgraph
