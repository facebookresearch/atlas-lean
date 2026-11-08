/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency

/-!
# Ordered directed-edge erasure

This module removes every occurrence of one ordered edge while retaining the
canonical vertex and neighbor orders of a directed-adjacency graph.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DirectedAdjacency

universe u

variable {V : Type u} {graph : DirectedAdjacency V}
variable {length : Nat} {source target left right : V}

/-- Remove every occurrence of the ordered edge `source → target`. -/
def eraseEdge [DecidableEq V] (graph : DirectedAdjacency V)
    (source target : V) : DirectedAdjacency V where
  vertices := graph.vertices
  vertices_nodup := graph.vertices_nodup
  vertices_complete := graph.vertices_complete
  adjacency vertex :=
    if vertex = source then
      (graph.adjacency vertex).filter fun neighbor => decide (neighbor ≠ target)
    else
      graph.adjacency vertex

/-- Erasing an edge preserves the exact vertex enumeration. -/
@[simp]
theorem vertices_eraseEdge [DecidableEq V] :
    (eraseEdge graph source target).vertices = graph.vertices :=
  rfl

/-- At the selected source, erasure stably filters out every target occurrence. -/
@[simp]
theorem adjacency_eraseEdge_source [DecidableEq V] :
    (eraseEdge graph source target).adjacency source =
      (graph.adjacency source).filter (fun vertex => decide (vertex ≠ target)) := by
  simp [eraseEdge]

/-- Erasing an edge leaves every other adjacency row exactly unchanged. -/
theorem adjacency_eraseEdge_of_ne [DecidableEq V]
    (different : left ≠ source) :
    (eraseEdge graph source target).adjacency left = graph.adjacency left := by
  simp [eraseEdge, different]

/-- Edge membership after erasure is original membership excluding the ordered pair. -/
@[simp]
theorem edge_eraseEdge [DecidableEq V] :
    (eraseEdge graph source target).Edge left right ↔
      graph.Edge left right ∧ ¬(left = source ∧ right = target) := by
  by_cases selected : left = source
  · subst left
    simp [Edge, eraseEdge]
  · simp [Edge, eraseEdge, selected]

/-- Boolean lookup reports that the erased ordered edge is absent. -/
@[simp]
theorem hasEdge_eraseEdge_self [DecidableEq V] :
    (eraseEdge graph source target).hasEdge source target = false := by
  simp [hasEdge, eraseEdge]

/-- Repeating the same erasure leaves every observable adjacency row unchanged. -/
theorem eraseEdge_idempotent [DecidableEq V] :
    (eraseEdge (eraseEdge graph source target) source target).adjacency =
      (eraseEdge graph source target).adjacency := by
  funext vertex
  by_cases selected : vertex = source
  · subst vertex
    simp [eraseEdge, List.filter_filter]
  · simp [eraseEdge, selected]

/-- Every exact-length walk after erasure was already a walk in the original graph. -/
theorem walk_eraseEdge_imp [DecidableEq V]
    (walk : Walk (eraseEdge graph source target) length left right) :
    Walk graph length left right :=
  Relation.RelatesInSteps.map id
    (fun a b edge =>
      (edge_eraseEdge (graph := graph) (source := source) (target := target)
        (left := a) (right := b)).mp edge |>.1)
    walk

/-- Reachability after erasure implies reachability in the original graph. -/
theorem reachable_eraseEdge_imp [DecidableEq V]
    (reachable : (eraseEdge graph source target).Reachable left right) :
    graph.Reachable left right := by
  obtain ⟨walkLength, walk⟩ := reachable_iff_exists_walk.mp reachable
  exact reachable_iff_exists_walk.mpr
    ⟨walkLength, walk_eraseEdge_imp (graph := graph) (source := source)
      (target := target) walk⟩

end Cslib.Algorithms.Lean.DirectedAdjacency
