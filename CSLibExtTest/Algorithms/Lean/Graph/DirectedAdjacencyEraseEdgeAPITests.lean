/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency.EraseEdge

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DirectedAdjacencyEraseEdgeAPITests

open DirectedAdjacency

universe u

variable {V : Type u} [DecidableEq V]
variable {graph : DirectedAdjacency V}
variable {length : Nat} {source target left right other : V}

example : (eraseEdge graph source target).vertices = graph.vertices :=
  vertices_eraseEdge

example :
    (eraseEdge graph source target).adjacency source =
      (graph.adjacency source).filter (fun vertex => decide (vertex ≠ target)) :=
  adjacency_eraseEdge_source

example (different : other ≠ source) :
    (eraseEdge graph source target).adjacency other = graph.adjacency other :=
  adjacency_eraseEdge_of_ne different

example :
    (eraseEdge graph source target).Edge left right ↔
      graph.Edge left right ∧ ¬(left = source ∧ right = target) :=
  edge_eraseEdge

example : (eraseEdge graph source target).hasEdge source target = false :=
  hasEdge_eraseEdge_self

example :
    (eraseEdge (eraseEdge graph source target) source target).adjacency =
      (eraseEdge graph source target).adjacency :=
  eraseEdge_idempotent

example (walk : Walk (eraseEdge graph source target) length left right) :
    Walk graph length left right :=
  walk_eraseEdge_imp walk

example (reachable : (eraseEdge graph source target).Reachable left right) :
    graph.Reachable left right :=
  reachable_eraseEdge_imp reachable

inductive Vertex
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

open Vertex

private def duplicateGraph : DirectedAdjacency Vertex where
  vertices := [a, b, c, d]
  vertices_nodup := by decide
  vertices_complete vertex := by cases vertex <;> simp
  adjacency
    | a => [b, b]
    | b => [a]
    | c => []
    | d => [d, d]

private def mixedGraph : DirectedAdjacency Vertex where
  vertices := [a, b, c, d]
  vertices_nodup := by decide
  vertices_complete vertex := by cases vertex <;> simp
  adjacency
    | a => [b, c, b]
    | b => [a]
    | c => []
    | d => [d, d]

private def isolatedSourceGraph : DirectedAdjacency Vertex where
  vertices := [a, b, c, d]
  vertices_nodup := by decide
  vertices_complete vertex := by cases vertex <;> simp
  adjacency
    | a => []
    | b => [a]
    | c => []
    | d => [d, d]

private theorem duplicate_targets_all_removed :
    (eraseEdge duplicateGraph a b).adjacency a = [] := by
  decide

private theorem mixed_row_order_and_multiplicity_preserved :
    (eraseEdge mixedGraph a b).adjacency a = [c] := by
  decide

private theorem reverse_edge_preserved :
    (eraseEdge duplicateGraph a b).Edge b a := by
  simp [DirectedAdjacency.Edge, eraseEdge, duplicateGraph]

private theorem unrelated_repeated_row_unchanged :
    (eraseEdge mixedGraph a b).adjacency d = [d, d] := by
  decide

private theorem absent_target_is_noop_on_row :
    (eraseEdge duplicateGraph c a).adjacency c = [] := by
  decide

private theorem isolated_source_stays_isolated :
    (eraseEdge isolatedSourceGraph a b).adjacency a = [] := by
  decide

private theorem self_loop_removed :
    (eraseEdge mixedGraph d d).adjacency d = [] := by
  decide

private theorem repeated_erasure_has_same_adjacency :
    (eraseEdge (eraseEdge mixedGraph a b) a b).adjacency =
      (eraseEdge mixedGraph a b).adjacency :=
  eraseEdge_idempotent

private theorem exact_vertex_order_preserved :
    (eraseEdge mixedGraph a b).vertices = [a, b, c, d] :=
  rfl

private theorem alternate_path_survives :
    (eraseEdge mixedGraph a b).Reachable a c := by
  exact reachable_iff_exists_walk.mpr
    ⟨1, Relation.RelatesInSteps.single
      (by simp [DirectedAdjacency.Edge, eraseEdge, mixedGraph])⟩

#print axioms Cslib.Algorithms.Lean.DirectedAdjacency.vertices_eraseEdge
#print axioms Cslib.Algorithms.Lean.DirectedAdjacency.adjacency_eraseEdge_source
#print axioms Cslib.Algorithms.Lean.DirectedAdjacency.adjacency_eraseEdge_of_ne
#print axioms Cslib.Algorithms.Lean.DirectedAdjacency.edge_eraseEdge
#print axioms Cslib.Algorithms.Lean.DirectedAdjacency.hasEdge_eraseEdge_self
#print axioms Cslib.Algorithms.Lean.DirectedAdjacency.eraseEdge_idempotent
#print axioms Cslib.Algorithms.Lean.DirectedAdjacency.walk_eraseEdge_imp
#print axioms Cslib.Algorithms.Lean.DirectedAdjacency.reachable_eraseEdge_imp

end Cslib.Algorithms.Lean.DirectedAdjacencyEraseEdgeAPITests
