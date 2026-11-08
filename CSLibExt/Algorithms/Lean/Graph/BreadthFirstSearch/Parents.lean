/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Internal

import all CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Internal

/-!
# Breadth-first predecessor trees

The timed first-discovery search erases to the existing ordered FIFO BFS result.
The predecessor relation, reconstructed paths and selected event costs are proved in companion
correctness and cost modules. The state and execution helpers remain module-private.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BreadthFirstSearch

universe u

/-- Erasing the timing and predecessor table gives the whole existing ordered BFS result. -/
public theorem bfsWithParents_ret {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) :
    (bfsWithParents graph source).ret.toBFSResult = bfs graph source := by
  simp only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure, parentInitial]
  rw [parentRun_ret_core]
  rfl

private lemma old_distance_none_iff {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V) :
    (bfs graph source).distance vertex = none ↔ ¬ graph.Reachable source vertex := by
  constructor
  · intro missing reachable
    obtain ⟨distance, found⟩ := (distance_present_iff_reachable graph source vertex).mpr reachable
    rw [missing] at found
    contradiction
  · intro unreachable
    cases found : (bfs graph source).distance vertex with
    | none => rfl
    | some distance =>
        exact False.elim (unreachable
          ((distance_present_iff_reachable graph source vertex).mp ⟨distance, found⟩))

/-- A vertex lacks a saved parent exactly when it is the source or unreachable. -/
public theorem predecessor_eq_none_iff {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V) :
    (bfsWithParents graph source).ret.predecessor vertex = none ↔
      vertex = source ∨ ¬ graph.Reachable source vertex := by
  have rule :
      (bfsWithParents graph source).ret.predecessor vertex = none ↔
        vertex = source ∨ (bfsWithParents graph source).ret.distance vertex = none := by
    simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using
      (parentFinal_invariant graph source).parent_none vertex
  rw [rule]
  change (vertex = source ∨
    (bfsWithParents graph source).ret.toBFSResult.distance vertex = none) ↔ _
  rw [bfsWithParents_ret, old_distance_none_iff]

/-- Every saved predecessor is an actual directed input edge. -/
public theorem predecessor_edge {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex parent : V)
    (found : (bfsWithParents graph source).ret.predecessor vertex = some parent) :
    graph.Edge parent vertex := by
  apply (parentFinal_invariant graph source).parent_edge vertex parent
  simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using found

/-- Saved predecessors have distance exactly one less than their children. -/
public theorem predecessor_distance {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex parent : V)
    (found : (bfsWithParents graph source).ret.predecessor vertex = some parent) :
    ∃ distance : Nat,
      (bfsWithParents graph source).ret.distance parent = some distance ∧
      (bfsWithParents graph source).ret.distance vertex = some (distance + 1) := by
  have saved :
      (parentRun graph graph.vertices.length (parentInitial source).ret).ret.parents[vertex]? =
        some parent := by
    simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using found
  simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using
    (parentFinal_invariant graph source).parent_distance vertex parent saved

/-- A nonsource parent is the first outgoing witness in the existing BFS source order. -/
public theorem predecessor_eq_find? {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V) (nonsource : vertex ≠ source) :
    (bfsWithParents graph source).ret.predecessor vertex =
      (bfs graph source).order.find?
        (fun parent => (graph.adjacency parent).contains vertex) := by
  have rule := parentRun_predecessor_eq_find? graph source (parentInitial source).ret
    graph.vertices.length
    (fun count _ => parentRun_invariant graph source count (parentInitial source).ret
      (parentInitial_invariant graph source))
    (by intro target _; simp [parentInitial]) vertex nonsource
  have decorated :
      (bfsWithParents graph source).ret.predecessor vertex =
        (bfsWithParents graph source).ret.toBFSResult.order.find?
          (fun parent => (graph.adjacency parent).contains vertex) := by
    simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using rule
  simpa only [bfsWithParents_ret] using decorated

end Cslib.Algorithms.Lean.BreadthFirstSearch

end
