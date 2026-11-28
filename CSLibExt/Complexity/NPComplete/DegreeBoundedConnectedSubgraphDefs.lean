/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEGREE-BOUNDED CONNECTED SUBGRAPH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT26]
DEGREE-BOUNDED CONNECTED SUBGRAPH;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 9);
M. Yannakakis, "Edge-deletion problems", SIAM Journal on Computing 10 (1981),
297-309, doi:10.1137/0210021.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DegreeBoundedConnectedSubgraph

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, degree bound `d`, and edge
bound `K`. -/
abbrev DegreeBoundedConnectedSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : DegreeBoundedConnectedSubgraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `d ≤ |V|`, and
`0 < K ≤ |E|`, the length of the edge list. -/
def WellFormed (i : DegreeBoundedConnectedSubgraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2 ∧ i.2.2.2 ≤ i.2.1.length

open Classical in
/-- Some sublist `E'` of the edge list with at least `K` entries spans a connected subgraph
`(V, E')` of maximum degree at most `d`. -/
def DegreeBoundedConnectedSubgraphFeasible (i : DegreeBoundedConnectedSubgraphInstance) :
    Prop :=
  ∃ es : List (ℕ × ℕ), es.Sublist i.2.1 ∧ i.2.2.2 ≤ es.length ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 es).Connected ∧
      ∀ v, (Cslib.Complexity.Karp.edgeGraph i.1 es).degree v ≤ i.2.2.1

open Classical in
/-- DEGREE-BOUNDED CONNECTED SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def degreeBoundedConnectedSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DegreeBoundedConnectedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ DegreeBoundedConnectedSubgraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DegreeBoundedConnectedSubgraph
