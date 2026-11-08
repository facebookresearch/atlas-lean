/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

import all CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Internal

/-!
# Selected-event bounds for predecessor BFS

Ticks charge outer dequeue attempts, adjacency membership checks, successful enqueues and
saved-parent writes, including the initial source enqueue and stuttering empty attempts.
The exact total preserves adjacency multiplicity. It is not a HashMap or full RAM-cost bound.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BreadthFirstSearch

universe u

private structure ScanEvents where
  checks : Nat
  enqueues : Nat
  writes : Nat

@[no_expose] private def scanEvents {V : Type u} [BEq V] [Hashable V]
    (parent : V) (distance : Nat) : List V → ParentState V → ScanEvents
  | [], _ => ⟨0, 0, 0⟩
  | vertex :: neighbors, state =>
      if state.core.2.2.contains vertex then
        let rest := scanEvents parent distance neighbors state
        ⟨rest.checks + 1, rest.enqueues, rest.writes⟩
      else
        let rest := scanEvents parent distance neighbors
          ⟨(state.core.1, (state.core.2.1.enqueue (vertex, distance + 1),
            state.core.2.2.insert vertex (distance + 1))), state.parents.insert vertex parent⟩
        ⟨rest.checks + 1, rest.enqueues + 1, rest.writes + 1⟩

private lemma scanEvents_spec {V : Type u} [BEq V] [Hashable V]
    (parent : V) (distance : Nat) (neighbors : List V) (state : ParentState V) :
    (scanEvents parent distance neighbors state).checks = neighbors.length ∧
      (scanEvents parent distance neighbors state).enqueues + (parentEntries state).length =
        (parentEntries (scanParents parent distance neighbors state).ret).length ∧
      (scanEvents parent distance neighbors state).writes =
        (scanEvents parent distance neighbors state).enqueues := by
  induction neighbors generalizing state with
  | nil => simp [scanEvents, scanParents]
  | cons vertex neighbors ih =>
      cases seen : state.core.2.2.contains vertex with
      | true =>
          simpa only [scanEvents, scanParents, seen, TimeM.ret_bind, ↓reduceIte,
            List.length_cons, Nat.add_right_cancel_iff] using ih state
      | false =>
          have rest := ih
            ⟨(state.core.1, (state.core.2.1.enqueue (vertex, distance + 1),
              state.core.2.2.insert vertex (distance + 1))), state.parents.insert vertex parent⟩
          have size := parentEntries_insert state parent vertex distance
          simp only [scanEvents, scanParents, seen, Bool.false_eq_true, ↓reduceIte,
            TimeM.ret_bind, List.length_cons]
          simp only [size, List.length_append, List.length_singleton] at rest
          omega

private structure ParentEvents where
  attempts : Nat
  checks : Nat
  enqueues : Nat
  writes : Nat
  successes : Nat

@[no_expose] private def stepEvents {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (state : ParentState V) : ParentEvents :=
  match state.core.2.1.dequeue? with
  | none => ⟨1, 0, 0, 0, 0⟩
  | some (entry, queue) =>
      let scanned := scanEvents entry.1 entry.2 (graph.adjacency entry.1)
        ⟨(entry :: state.core.1, (queue, state.core.2.2)), state.parents⟩
      ⟨1, scanned.checks, scanned.enqueues, scanned.writes, 1⟩

@[no_expose] private def runEvents {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) : Nat → ParentState V → ParentEvents
  | 0, _ => ⟨0, 0, 0, 0, 0⟩
  | fuel + 1, state =>
      let previous := runEvents graph fuel state
      let next := stepEvents graph (parentRun graph fuel state).ret
      ⟨previous.attempts + next.attempts, previous.checks + next.checks,
        previous.enqueues + next.enqueues, previous.writes + next.writes,
        previous.successes + next.successes⟩

private lemma stepEvents_spec {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (state : ParentState V) :
    (stepEvents graph state).attempts = 1 ∧
      (stepEvents graph state).checks +
          (state.core.1.map fun entry => (graph.adjacency entry.1).length).sum =
        ((parentStep graph state).ret.core.1.map
          fun entry => (graph.adjacency entry.1).length).sum ∧
      (stepEvents graph state).enqueues + (parentEntries state).length =
        (parentEntries (parentStep graph state).ret).length ∧
      (stepEvents graph state).writes = (stepEvents graph state).enqueues ∧
      (stepEvents graph state).successes + state.core.1.length =
        (parentStep graph state).ret.core.1.length := by
  cases next : state.core.2.1.dequeue? with
  | none => simp [stepEvents, parentStep, next]
  | some pair =>
      rcases pair with ⟨entry, queue⟩
      have scanned := scanEvents_spec entry.1 entry.2 (graph.adjacency entry.1)
        ⟨(entry :: state.core.1, (queue, state.core.2.2)), state.parents⟩
      simp only [parentEntries_dequeue state entry queue next] at scanned
      simp only [stepEvents, parentStep, next, TimeM.ret_bind, scanParents_ret_order,
        List.map_cons, List.sum_cons, List.length_cons]
      exact ⟨trivial, by omega, scanned.2.1, scanned.2.2, by omega⟩

private lemma runEvents_spec {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (fuel : Nat) (state : ParentState V) :
    (runEvents graph fuel state).attempts = fuel ∧
      (runEvents graph fuel state).checks +
          (state.core.1.map fun entry => (graph.adjacency entry.1).length).sum =
        ((parentRun graph fuel state).ret.core.1.map
          fun entry => (graph.adjacency entry.1).length).sum ∧
      (runEvents graph fuel state).enqueues + (parentEntries state).length =
        (parentEntries (parentRun graph fuel state).ret).length ∧
      (runEvents graph fuel state).writes = (runEvents graph fuel state).enqueues ∧
      (runEvents graph fuel state).successes + state.core.1.length =
        (parentRun graph fuel state).ret.core.1.length := by
  induction fuel with
  | zero => simp [runEvents, parentRun, Nat.fold_zero]
  | succ fuel ih =>
      have step := stepEvents_spec graph (parentRun graph fuel state).ret
      simp only [runEvents, parentRun, Nat.fold_succ, TimeM.ret_bind] at *
      omega

private lemma runEvents_time {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (fuel : Nat) (state : ParentState V) :
    (parentRun graph fuel state).time =
      (runEvents graph fuel state).attempts + (runEvents graph fuel state).checks +
        (runEvents graph fuel state).enqueues + (runEvents graph fuel state).writes := by
  have events := runEvents_spec graph fuel state
  have potential := parentRun_time_potential graph fuel state
  omega

private lemma parentFinal_queue_empty {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) :
    (parentRun graph graph.vertices.length (parentInitial source).ret).ret.core.2.1.dequeue? =
      none :=
  parentRun_queue_empty graph source graph.vertices.length (parentInitial source).ret
    (by simp [parentInitial]) (parentFinal_invariant graph source)

private lemma parentFinal_order {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) :
    (parentRun graph graph.vertices.length (parentInitial source).ret).ret.core.1.reverse.map
      Prod.fst = (bfs graph source).order := by
  have projection := congrArg (fun result : BFSResult V => result.order)
    (bfsWithParents_ret graph source)
  simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using projection

@[no_expose] private def bfsEvents {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (source : V) : ParentEvents :=
  let run := runEvents graph graph.vertices.length (parentInitial source).ret
  ⟨run.attempts, run.checks, run.enqueues + 1, run.writes, run.successes⟩

private lemma bfsEvents_spec {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) :
    (bfsEvents graph source).attempts = graph.vertices.length ∧
      (bfsEvents graph source).checks =
        ((bfs graph source).order.map fun vertex => (graph.adjacency vertex).length).sum ∧
      (bfsEvents graph source).enqueues = (bfs graph source).order.length ∧
      (bfsEvents graph source).writes = (bfs graph source).order.length - 1 ∧
      (bfsEvents graph source).successes = (bfs graph source).order.length ∧
      (bfsWithParents graph source).time =
        (bfsEvents graph source).attempts + (bfsEvents graph source).checks +
          (bfsEvents graph source).enqueues + (bfsEvents graph source).writes := by
  have events := runEvents_spec graph graph.vertices.length (parentInitial source).ret
  have timed := runEvents_time graph graph.vertices.length (parentInitial source).ret
  have empty := (Queue.dequeue?_eq_none_iff _).mp (parentFinal_queue_empty graph source)
  have orderLength := congrArg List.length (parentFinal_order graph source)
  simp only [List.length_map, List.length_reverse] at orderLength
  have adjacencySum :
      ((parentRun graph graph.vertices.length (parentInitial source).ret).ret.core.1.map
        fun entry => (graph.adjacency entry.1).length).sum =
      ((bfs graph source).order.map fun vertex => (graph.adjacency vertex).length).sum := by
    rw [← parentFinal_order]
    simp [List.map_map, Function.comp_def]
  have initialEntries : (parentEntries (parentInitial source).ret).length = 1 := by
    simp [parentInitial, parentEntries]
  have initialSize : (parentInitial source).ret.core.1.length = 0 := rfl
  have initialSum :
      ((parentInitial source).ret.core.1.map
        fun entry => (graph.adjacency entry.1).length).sum = 0 := rfl
  have finalEntries :
      (parentEntries
        (parentRun graph graph.vertices.length (parentInitial source).ret).ret).length =
        (bfs graph source).order.length := by
    simp only [parentEntries, List.length_append, List.length_reverse, empty,
      List.length_nil, Nat.add_zero, orderLength]
  rw [initialEntries, initialSize, initialSum, finalEntries, orderLength, adjacencySum] at events
  have timing : (bfsWithParents graph source).time =
      1 + (parentRun graph graph.vertices.length (parentInitial source).ret).time := by
    simp only [bfsWithParents, TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
    rfl
  simp only [bfsEvents]
  omega

/-- Exact selected BFS events: attempts, adjacency checks, enqueues and parent writes. -/
public theorem bfsWithParents_time {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) :
    (bfsWithParents graph source).time =
      graph.vertices.length +
        ((bfs graph source).order.map fun vertex => (graph.adjacency vertex).length).sum +
        (bfs graph source).order.length + ((bfs graph source).order.length - 1) := by
  have events := bfsEvents_spec graph source
  omega

/-- The selected event count is bounded by three vertex passes plus all adjacency entries. -/
public theorem bfsWithParents_time_le {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) :
    (bfsWithParents graph source).time ≤
      3 * graph.vertices.length +
        (graph.vertices.map fun vertex => (graph.adjacency vertex).length).sum := by
  classical
  have orderBound := (order_nodup graph source).length_le_of_subset
    (fun vertex _ => graph.vertices_complete vertex)
  have adjacencyBound :
      ((bfs graph source).order.map fun vertex => (graph.adjacency vertex).length).sum ≤
        (graph.vertices.map fun vertex => (graph.adjacency vertex).length).sum := by
    rw [← List.sum_toFinset _ (order_nodup graph source),
      ← List.sum_toFinset _ graph.vertices_nodup]
    apply Finset.sum_le_sum_of_subset
    intro vertex _
    exact List.mem_toFinset.mpr (graph.vertices_complete vertex)
  rw [bfsWithParents_time]
  omega

end Cslib.Algorithms.Lean.BreadthFirstSearch

end
