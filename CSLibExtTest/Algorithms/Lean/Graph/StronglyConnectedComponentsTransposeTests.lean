/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.StronglyConnectedComponents.Transpose

/-!
# Consumers of strong-connectivity invariance under transposition

The three-vertex graph with edges `0 → 1`, `1 → 0`, and `1 → 2` has the strongly
connected component `{0, 1}` and the singleton component `{2}`. Its transpose reverses
reachability (`1` reaches `2` only in the original graph) but has the same components.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.StronglyConnectedComponentsTransposeTests

open StronglyConnectedComponents

private def pairGraph : DirectedAdjacency (Fin 3) where
  vertices := List.finRange 3
  vertices_nodup := List.nodup_finRange 3
  vertices_complete := List.mem_finRange
  adjacency vertex := if vertex = 0 then [1] else if vertex = 1 then [0, 2] else []

private theorem pairGraph_connected : StronglyConnected pairGraph 0 1 :=
  ⟨.single (by simp [DirectedAdjacency.Edge, pairGraph]),
    .single (by simp [DirectedAdjacency.Edge, pairGraph])⟩

private theorem not_reachable_two_one : ¬ pairGraph.Reachable 2 1 := by
  intro reach
  rcases Relation.ReflTransGen.cases_head reach with same | ⟨next, edge, _⟩
  · exact absurd same (by decide)
  · simp [DirectedAdjacency.Edge, pairGraph] at edge

/-- Transposition changes reachability: `1` reaches `2` in the graph but not in its
transpose. -/
example : pairGraph.Reachable 1 2 ∧ ¬ pairGraph.transpose.Reachable 1 2 := by
  refine ⟨.single (by simp [DirectedAdjacency.Edge, pairGraph]), ?_⟩
  rw [DirectedAdjacency.reachable_transpose_iff]
  exact not_reachable_two_one

/-- The component `{0, 1}` is strongly connected in the transpose. -/
example : StronglyConnected pairGraph.transpose 0 1 :=
  stronglyConnected_transpose_iff.mpr pairGraph_connected

/-- Vertex `2` lies outside that component in the transpose, as in the graph. -/
example : ¬ StronglyConnected pairGraph.transpose 1 2 := by
  rw [stronglyConnected_transpose_iff]
  exact fun connected => not_reachable_two_one connected.2

/-- The component relations of the graph and its transpose coincide. -/
example : (stronglyConnectedSetoid pairGraph.transpose).r 0 1 ∧
    ¬ (stronglyConnectedSetoid pairGraph.transpose).r 1 2 := by
  rw [stronglyConnectedSetoid_transpose]
  exact ⟨pairGraph_connected, fun connected => not_reachable_two_one connected.2⟩

/-- The relation-level theorem on the same edges: `0` and `1` are mutually reachable
under the reversed edge relation. -/
example : Relation.ReflTransGen (Function.swap pairGraph.Edge) 0 1 ∧
    Relation.ReflTransGen (Function.swap pairGraph.Edge) 1 0 :=
  (mutual_reflTransGen_swap_iff 0 1).mpr pairGraph_connected

/-- Under the reversed edge relation, `1` and `2` are not mutually reachable. -/
example : ¬ (Relation.ReflTransGen (Function.swap pairGraph.Edge) 1 2 ∧
    Relation.ReflTransGen (Function.swap pairGraph.Edge) 2 1) := by
  rw [mutual_reflTransGen_swap_iff]
  exact fun connected => not_reachable_two_one connected.2

end Cslib.Algorithms.Lean.StronglyConnectedComponentsTransposeTests
