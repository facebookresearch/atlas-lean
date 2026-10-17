/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency
public meta import CSLibExt.Algorithms.Lean.Graph.TopologicalSort
import CSLibExt.Algorithms.Lean.DataStructures.Queue.Semantics
import all CSLibExt.Algorithms.Lean.Graph.TopologicalSort

/-!
# Tests for deterministic FIFO Kahn topological sorting

These examples exercise the canonical graph API, edge semantics for duplicate entries and
self-loops, cycle witnesses, and the production FIFO traversal.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.privateModule false

namespace Cslib.Algorithms.Lean.Tests

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TopologicalSort

private def emptyGraph : DirectedAdjacency (Fin 0) where
  vertices := []
  vertices_nodup := by simp
  vertices_complete v := nomatch v
  adjacency v := nomatch v

example : sort emptyGraph = .success [] := by decide

private def isolated : DirectedAdjacency (Fin 1) where
  vertices := [0]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency _ := []

example : sort isolated = .success [0] := by decide

example : IsTopologicalOrder isolated [0] :=
  success_isTopologicalOrder isolated [0] (by decide)

private def selfLoop : DirectedAdjacency (Fin 1) where
  vertices := [0]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency _ := [0]

example : indegree selfLoop 0 = 1 := by decide

example : sort selfLoop = .failure [] [0] := by decide

#eval do
  assert! sort selfLoop == Result.failure [] [0]

example : DirectedCycleIn selfLoop [0] [0] := by
  apply (directedCycleIn_iff selfLoop [0] [0]).2
  simp [selfLoop, DirectedAdjacency.Edge]

example : ∃ cycle, DirectedCycleIn selfLoop [0] cycle :=
  failure_cycle selfLoop [] [0] (by decide)

private def duplicateGraph : DirectedAdjacency (Fin 2) where
  vertices := [0, 1]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency
    | 0 => [1, 1]
    | 1 => []

-- Duplicate adjacency entries denote one edge in the public graph semantics.
example : indegree duplicateGraph 1 = 1 := by decide

-- Logical and executable counters both ignore later occurrences of the same edge.
example : sort duplicateGraph = .success [0, 1] := by decide

#eval do
  assert! sort duplicateGraph == Result.success [0, 1]

private def threeCycle : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency
    | 0 => [1]
    | 1 => [2]
    | 2 => [0]

example : sort threeCycle = .failure [] [0, 1, 2] := by decide

example : ∃ cycle, DirectedCycleIn threeCycle [0, 1, 2] cycle :=
  failure_cycle threeCycle [] [0, 1, 2] (by decide)

private def disconnected : DirectedAdjacency (Fin 5) where
  vertices := [0, 1, 2, 3, 4]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency
    | 0 => [1]
    | 2 => [3]
    | _ => []

example : sort disconnected = .success [0, 2, 4, 1, 3] := by decide

private def fifoGraph : DirectedAdjacency (Fin 4) where
  vertices := [0, 1, 2, 3]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency
    | 0 => [3]
    | 1 => [3]
    | _ => []

-- A stack would move newly ready `3` ahead of the older queued vertex `2`.
example : sort fifoGraph = .success [0, 1, 2, 3] := by decide

-- `#eval` uses `sort`'s hash-indexed production implementation.
#eval do
  assert! sort fifoGraph == Result.success [0, 1, 2, 3]

private def fifoStateAfterZero : Option (State (Fin 4)) :=
  step fifoGraph (initialState fifoGraph)

private def fifoStateAfterOne : Option (State (Fin 4)) :=
  fifoStateAfterZero.bind (step fifoGraph)

example : fifoStateAfterZero.map (fun state => Queue.contents state.queue) =
    some [1, 2] := by decide

example : fifoStateAfterOne.map (fun state => Queue.contents state.queue) =
    some [2, 3] := by decide

private def simultaneous : DirectedAdjacency (Fin 5) where
  vertices := [0, 1, 2, 3, 4]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency
    | 0 => [3, 4]
    | _ => []

example : sort simultaneous = .success [0, 1, 2, 3, 4] := by decide

#eval do
  assert! sort simultaneous == Result.success [0, 1, 2, 3, 4]

private def reverseReady : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency
    | 0 => [2, 1, 2]
    | _ => []

-- Vertices released together follow their first occurrence in the outgoing adjacency list.
example : sort reverseReady = .success [0, 2, 1] := by decide

#eval do
  assert! sort reverseReady == Result.success [0, 2, 1]

private def permutedVertices : DirectedAdjacency (Fin 3) where
  vertices := [2, 0, 1]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency
    | 0 => [1]
    | _ => []

-- Initial readiness follows the certified carrier order, not the type's canonical order.
example : sort permutedVertices = .success [2, 0, 1] := by decide

#eval do
  assert! sort permutedVertices == Result.success [2, 0, 1]

private def partialFailure : DirectedAdjacency (Fin 3) where
  vertices := [2, 0, 1]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency
    | 0 => [1]
    | 1 => [0]
    | 2 => []

-- Failure preserves both the processed prefix and the carrier-ordered remainder.
example : sort partialFailure = .failure [2] [0, 1] := by decide

#eval do
  assert! sort partialFailure == Result.failure [2] [0, 1]

end Cslib.Algorithms.Lean.Tests
