/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST DIRECTED CIRCUIT: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND28] LONGEST CIRCUIT, p. 213,
comment: "Remains NP-complete if l(e) = 1 for all e ∈ E, as does the corresponding problem for
directed circuits in directed graphs"; problem [GT38] DIRECTED HAMILTONIAN CIRCUIT;
R. M. Karp, "Reducibility among combinatorial problems", in Complexity of Computer
Computations (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Dijkstra
public import CSLibExt.Algorithms.Lean.Graph.TopologicalSort

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestDirectedCircuit

/-- An instance: vertex count `n` (vertices `Fin n`), the arc list with lengths (an entry
`(u, v, l)` is the arc `u → v` of length `l`), and the bound `K`. -/
abbrev LongestDirectedCircuitInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The directed graph of the instance on `Fin n`: the out-neighbors of `u` are the vertices
`v` with an entry `(u, v, l)` in the arc list. -/
def Graph (i : LongestDirectedCircuitInstance) :
    Cslib.Algorithms.Lean.DirectedAdjacency (Fin i.1) where
  vertices := List.finRange i.1
  vertices_nodup := List.nodup_finRange i.1
  vertices_complete := List.mem_finRange
  adjacency u := (List.finRange i.1).filter fun v =>
    ((u : ℕ), (v : ℕ)) ∈ i.2.1.map fun a => (a.1, a.2.1)

/-- The length `l(u → v)`: the length recorded for the arc-list entry `(u, v, l)` (unique
under `WellFormed`). -/
def arcLength (i : LongestDirectedCircuitInstance) (u v : Fin i.1) : ℕ :=
  ((i.2.1.find? fun a => a.1 = (u : ℕ) ∧ a.2.1 = (v : ℕ)).map fun a => a.2.2).getD 0

/-- Well-formedness of an instance: the arc list describes a directed graph on `Fin n` (no two
entries for the same ordered pair, no loops, endpoints in range), every length is positive,
and `0 < K`. -/
def WellFormed (i : LongestDirectedCircuitInstance) : Prop :=
  (i.2.1.map fun a => (a.1, a.2.1)).Nodup ∧
    (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2.1 < i.1 ∧ a.1 ≠ a.2.1 ∧ 0 < a.2.2) ∧ 0 < i.2.2

/-- Some simple directed circuit has length at least `K`: a directed cycle `c` (nonempty,
distinct vertices, consecutive vertices and the last and first joined by arcs) whose arc
lengths, including the closing arc, sum to at least `K`. -/
def LongestDirectedCircuitFeasible (i : LongestDirectedCircuitInstance) : Prop :=
  ∃ c : List (Fin i.1),
    Cslib.Algorithms.Lean.TopologicalSort.DirectedCycleIn (Graph i) (Graph i).vertices c ∧
      i.2.2 ≤ Cslib.Algorithms.Lean.DirectedAdjacency.pathWeight (arcLength i) (c ++ c.take 1)

open Classical in
/-- LONGEST DIRECTED CIRCUIT as a decision problem over bitstrings. -/
noncomputable def longestDirectedCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LongestDirectedCircuitInstance) x with
  | some i => decide (WellFormed i ∧ LongestDirectedCircuitFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LongestDirectedCircuit
