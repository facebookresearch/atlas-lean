/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

open SimpleGraph

/-- The triangle on the vertices `0, 1, 2`. -/
private abbrev triangle : HamiltonianCycleUndirectedInstance := (3, [(0, 1), (1, 2), (2, 0)])

/-- The triangle on `0, 1, 2` with a fourth, isolated vertex `3`. -/
private abbrev triangleAndPoint : HamiltonianCycleUndirectedInstance :=
  (4, [(0, 1), (1, 2), (2, 0)])

/-- The triangle with its first edge listed twice. -/
private abbrev triangleRepeated : HamiltonianCycleUndirectedInstance :=
  (3, [(0, 1), (0, 1), (1, 2), (2, 0)])

/-- The triangle with its first edge listed in both directions. -/
private abbrev triangleReversed : HamiltonianCycleUndirectedInstance :=
  (3, [(0, 1), (1, 0), (1, 2), (2, 0)])

/-- The triangle is well formed. -/
example : WellFormed triangle := by unfold WellFormed; decide

/-- Well formedness allows a vertex that no edge touches. -/
example : WellFormed triangleAndPoint := by unfold WellFormed; decide

/-- The one-vertex graph with no edges is well formed. -/
example : WellFormed (1, []) := by unfold WellFormed; decide

/-- The two-vertex graph with one edge is well formed. -/
example : WellFormed (2, [(0, 1)]) := by unfold WellFormed; decide

/-- Malformed: the empty instance has no vertex. -/
example : ¬ WellFormed (0, []) := by unfold WellFormed; decide

/-- Malformed: an edge listed twice. -/
example : ¬ WellFormed triangleRepeated := by unfold WellFormed; decide

/-- Malformed: an edge listed in both directions. -/
example : ¬ WellFormed triangleReversed := by unfold WellFormed; decide

/-- Malformed: a loop. -/
example : ¬ WellFormed (3, [(0, 0)]) := by unfold WellFormed; decide

/-- Malformed: an endpoint `3` outside `{0, 1, 2}`. -/
example : ¬ WellFormed (3, [(0, 1), (1, 3)]) := by unfold WellFormed; decide

/-- The graph is symmetric: the edge `(0, 1)` makes `1` adjacent to `0`. -/
example : (Graph triangle).Adj 1 0 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- An edge with an endpoint outside the vertices contributes no adjacency. -/
example : ∀ u v, ¬ (Graph (2, [(0, 2)])).Adj u v := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- The isolated vertex `3` has no neighbour. -/
private theorem triangleAndPoint_not_adj_three (v : Fin 4) :
    ¬ (Graph triangleAndPoint).Adj 3 v := by
  revert v
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- The closed walk `0, 1, 2, 0` around a graph whose edges include those of the triangle. -/
private def triangleWalk (E : List (ℕ × ℕ)) (h01 : (Graph (3, E)).Adj 0 1)
    (h12 : (Graph (3, E)).Adj 1 2) (h20 : (Graph (3, E)).Adj 2 0) :
    (Graph (3, E)).Walk 0 0 :=
  .cons h01 (.cons h12 (.cons h20 .nil))

/-- The walk `0, 1, 2, 0` is a Hamiltonian cycle, whatever the edge list repeats. -/
private theorem triangleWalk_isHamiltonianCycle (E : List (ℕ × ℕ))
    (h01 : (Graph (3, E)).Adj 0 1) (h12 : (Graph (3, E)).Adj 1 2)
    (h20 : (Graph (3, E)).Adj 2 0) : (triangleWalk E h01 h12 h20).IsHamiltonianCycle := by
  refine Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨?_, ?_⟩
  · simp [triangleWalk, Walk.cons_isCycle_iff, Walk.cons_isPath_iff]
  · simp [triangleWalk]

/-- The triangle is feasible, with the explicit Hamiltonian cycle `0, 1, 2, 0`. -/
private theorem triangle_feasible : HamiltonianCycleUndirectedFeasible triangle :=
  ⟨le_rfl, fun _ => ⟨0, _, triangleWalk_isHamiltonianCycle _
    (by simp [Graph, Cslib.Complexity.Karp.edgeGraph])
    (by simp [Graph, Cslib.Complexity.Karp.edgeGraph])
    (by simp [Graph, Cslib.Complexity.Karp.edgeGraph])⟩⟩

/-- Repeating an edge leaves the graph, and so feasibility, unchanged. -/
private theorem triangleRepeated_feasible : HamiltonianCycleUndirectedFeasible triangleRepeated :=
  ⟨le_rfl, fun _ => ⟨0, _, triangleWalk_isHamiltonianCycle _
    (by simp [Graph, Cslib.Complexity.Karp.edgeGraph])
    (by simp [Graph, Cslib.Complexity.Karp.edgeGraph])
    (by simp [Graph, Cslib.Complexity.Karp.edgeGraph])⟩⟩

/-- A walk that starts at the isolated vertex `3` never leaves it. -/
private theorem triangleAndPoint_walk_stays {u v : Fin 4} (p : (Graph triangleAndPoint).Walk u v) :
    u = 3 → v = 3 := by
  induction p with
  | nil => exact id
  | cons h _ _ =>
    rintro rfl
    exact absurd h (triangleAndPoint_not_adj_three _)

/-- A graph with an isolated vertex is not Hamiltonian: it is not connected. -/
private theorem triangleAndPoint_not_feasible :
    ¬ HamiltonianCycleUndirectedFeasible triangleAndPoint := by
  rintro ⟨-, h⟩
  obtain ⟨p⟩ := h.connected.preconnected 3 0
  exact absurd (triangleAndPoint_walk_stays p rfl) (by decide)

/-- Mathlib counts the one-vertex graph as Hamiltonian. -/
private theorem one_isHamiltonian : (Graph (1, [])).IsHamiltonian := fun h => absurd h (by simp)

/-- The bound `3 ≤ n` alone makes the one-vertex graph infeasible. -/
private theorem one_not_feasible : ¬ HamiltonianCycleUndirectedFeasible (1, []) :=
  fun h => absurd h.1 (by decide)

/-- The two-vertex graph with one edge has no Hamiltonian cycle: a cycle has length at least
three, and a Hamiltonian cycle here would have length two. -/
example : ¬ (Graph (2, [(0, 1)])).IsHamiltonian := by
  intro h
  obtain ⟨_, p, hp⟩ := h (by simp)
  have := hp.length_eq
  have := hp.three_le_length
  simp_all

/-- The bound `3 ≤ n` rules out the two-vertex graph too. -/
example : ¬ HamiltonianCycleUndirectedFeasible (2, [(0, 1)]) := fun h => absurd h.1 (by decide)

/-- The empty instance is infeasible. -/
example : ¬ HamiltonianCycleUndirectedFeasible (0, []) := fun h => absurd h.1 (by decide)

open MetaMathlibExt.BitstringEncoding

/-- The decision problem accepts the encoding of the triangle. -/
example : hamiltonianCycleUndirectedDec (bitEncode triangle) = true := by
  have hw : WellFormed triangle := by unfold WellFormed; decide
  simp [hamiltonianCycleUndirectedDec, hw, triangle_feasible]

/-- It rejects the encoding of a well-formed graph with no Hamiltonian cycle. -/
example : hamiltonianCycleUndirectedDec (bitEncode triangleAndPoint) = false := by
  simp [hamiltonianCycleUndirectedDec, triangleAndPoint_not_feasible]

/-- It rejects the encoding of the one-vertex graph, a well-formed instance whose graph Mathlib
counts as Hamiltonian: only the bound `3 ≤ n` rejects it. -/
example : WellFormed (1, []) ∧ (Graph (1, [])).IsHamiltonian ∧
    hamiltonianCycleUndirectedDec
      (bitEncode ((1, []) : HamiltonianCycleUndirectedInstance)) = false := by
  refine ⟨by unfold WellFormed; decide, one_isHamiltonian, ?_⟩
  simp [hamiltonianCycleUndirectedDec, one_not_feasible]

/-- It rejects a malformed encoding of a Hamiltonian graph: the triangle with an edge listed
twice is feasible, and only well formedness rejects it. -/
example : HamiltonianCycleUndirectedFeasible triangleRepeated ∧
    hamiltonianCycleUndirectedDec (bitEncode triangleRepeated) = false := by
  have hw : ¬ WellFormed triangleRepeated := by unfold WellFormed; decide
  exact ⟨triangleRepeated_feasible, by simp [hamiltonianCycleUndirectedDec, hw]⟩

/-- It rejects the empty bitstring, which decodes to no instance. -/
example : hamiltonianCycleUndirectedDec [] = false := by
  have h : bitDecode (α := HamiltonianCycleUndirectedInstance) [] = none := rfl
  simp [hamiltonianCycleUndirectedDec, h]

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
