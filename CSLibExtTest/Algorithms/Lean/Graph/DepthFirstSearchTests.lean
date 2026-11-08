/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DepthFirstSearch

import Std.Data.HashSet.Lemmas

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DepthFirstSearchTests

open DepthFirstSearch
open DepthFirstSearch.Internal

attribute [local simp] Std.HashSet.not_mem_empty Std.HashSet.mem_insert

private def branchingGraph : DirectedAdjacency (Fin 4) where
  vertices := List.finRange 4
  vertices_nodup := List.nodup_finRange 4
  vertices_complete := List.mem_finRange
  adjacency
    | 0 => [1, 2]
    | 1 => [3]
    | _ => []

example : (dfs branchingGraph [0]).preorder = [0, 1, 3, 2] := by
  simp [dfs, loop, initial, finish, enterFrames, branchingGraph]

example : (dfs branchingGraph [0]).postorder = [3, 1, 2, 0] := by
  simp [dfs, loop, initial, finish, enterFrames, branchingGraph]

example : (dfs branchingGraph [0]).parents = [(1, 0), (3, 1), (2, 0)] := by
  simp [dfs, loop, initial, finish, enterFrames, branchingGraph]

/-- Scheduling every vertex must not erase actual discovering-parent edges. -/
example : (dfs branchingGraph [0, 1, 2, 3]).parents =
    [(1, 0), (3, 1), (2, 0)] := by
  simp [dfs, loop, initial, finish, enterFrames, branchingGraph]

example : (dfs branchingGraph [0, 1, 2, 3]).forestRoots = [0] := by
  simp [Traversal.forestRoots, dfs, loop, initial, finish, enterFrames, branchingGraph]

example : (dfsAll branchingGraph).preorder = [0, 1, 3, 2] := by
  change (dfs branchingGraph [0, 1, 2, 3]).preorder = [0, 1, 3, 2]
  simp [dfs, loop, initial, finish, enterFrames, branchingGraph]

example : decreasingFinishAll branchingGraph = [0, 2, 1, 3] := by
  change decreasingFinish branchingGraph [0, 1, 2, 3] = [0, 2, 1, 3]
  simp [decreasingFinish, dfs, loop, initial, finish, enterFrames, branchingGraph]

example : (3 : Fin 4) ∈ (dfs branchingGraph [0]).preorder ↔
    ∃ root ∈ [0], branchingGraph.Reachable root 3 :=
  mem_preorder_iff_reachable branchingGraph [0] 3

example : Before (0 : Fin 4) 1 (dfs branchingGraph [0]).preorder := by
  apply parent_before_child branchingGraph [0] 1 0
  simp [dfs, loop, initial, finish, enterFrames, branchingGraph]

example : Before (3 : Fin 4) 1 (dfs branchingGraph [0]).postorder := by
  apply child_before_parent_postorder branchingGraph [0] 3 1
  simp [dfs, loop, initial, finish, enterFrames, branchingGraph]

example : dfs branchingGraph [] = ⟨[], [], []⟩ := by
  simp [dfs, loop, initial, finish, enterFrames]

private def isolatedGraph : DirectedAdjacency (Fin 1) where
  vertices := List.finRange 1
  vertices_nodup := List.nodup_finRange 1
  vertices_complete := List.mem_finRange
  adjacency _ := []

example : dfs isolatedGraph [0] = ⟨[0], [0], []⟩ := by
  simp [dfs, loop, initial, finish, enterFrames, isolatedGraph]

private def selfLoopGraph : DirectedAdjacency (Fin 1) where
  vertices := List.finRange 1
  vertices_nodup := List.nodup_finRange 1
  vertices_complete := List.mem_finRange
  adjacency _ := [0]

example : dfs selfLoopGraph [0] = ⟨[0], [0], []⟩ := by
  simp [dfs, loop, initial, finish, enterFrames, selfLoopGraph]

private def cycleGraph : DirectedAdjacency (Fin 3) where
  vertices := List.finRange 3
  vertices_nodup := List.nodup_finRange 3
  vertices_complete := List.mem_finRange
  adjacency
    | 0 => [1]
    | 1 => [2]
    | _ => [0]

example : dfs cycleGraph [0] = ⟨[0, 1, 2], [2, 1, 0], [(1, 0), (2, 1)]⟩ := by
  simp [dfs, loop, initial, finish, enterFrames, cycleGraph]

example : dfs branchingGraph [0, 0] = dfs branchingGraph [0] := by
  simp [dfs, loop, initial, finish, enterFrames, branchingGraph]

private def disconnectedGraph : DirectedAdjacency (Fin 4) where
  vertices := List.finRange 4
  vertices_nodup := List.nodup_finRange 4
  vertices_complete := List.mem_finRange
  adjacency
    | 0 => [1]
    | 2 => [3]
    | _ => []

example : dfs disconnectedGraph [0] = ⟨[0, 1], [1, 0], [(1, 0)]⟩ := by
  simp [dfs, loop, initial, finish, enterFrames, disconnectedGraph]

example : dfs disconnectedGraph [2, 0] =
    ⟨[2, 3, 0, 1], [3, 2, 1, 0], [(3, 2), (1, 0)]⟩ := by
  simp [dfs, loop, initial, finish, enterFrames, disconnectedGraph]

example : (dfs disconnectedGraph [2, 0]).forestRoots = [2, 0] := by
  simp [Traversal.forestRoots, dfs, loop, initial, finish, enterFrames, disconnectedGraph]

private def crossEdgeGraph : DirectedAdjacency (Fin 4) where
  vertices := List.finRange 4
  vertices_nodup := List.nodup_finRange 4
  vertices_complete := List.mem_finRange
  adjacency
    | 0 => [1]
    | 2 => [3]
    | 3 => [1]
    | _ => []

/-- The edge `3 → 1` enters a DFS tree that has already finished. -/
example : decreasingFinishAll crossEdgeGraph = [2, 3, 0, 1] := by
  change decreasingFinish crossEdgeGraph [0, 1, 2, 3] = [2, 3, 0, 1]
  simp [decreasingFinish, dfs, loop, initial, finish, enterFrames, crossEdgeGraph]

private def twoComponentGraph : DirectedAdjacency (Fin 4) where
  vertices := List.finRange 4
  vertices_nodup := List.nodup_finRange 4
  vertices_complete := List.mem_finRange
  adjacency
    | 0 => [1]
    | 1 => [0, 2]
    | 2 => [3]
    | _ => [2]

/-- The first two vertices form an SCC with a one-way edge to the second SCC. -/
example : decreasingFinishAll twoComponentGraph = [0, 1, 2, 3] := by
  change decreasingFinish twoComponentGraph [0, 1, 2, 3] = [0, 1, 2, 3]
  simp [decreasingFinish, dfs, loop, initial, finish, enterFrames, twoComponentGraph]

private def duplicateGraph : DirectedAdjacency (Fin 2) where
  vertices := List.finRange 2
  vertices_nodup := List.nodup_finRange 2
  vertices_complete := List.mem_finRange
  adjacency
    | 0 => [1, 1]
    | _ => []

example : dfs duplicateGraph [0] = ⟨[0, 1], [1, 0], [(1, 0)]⟩ := by
  simp [dfs, loop, initial, finish, enterFrames, duplicateGraph]

example : branchingGraph.transpose.Reachable 3 0 ↔ branchingGraph.Reachable 0 3 :=
  DirectedAdjacency.reachable_transpose_iff

/-- Whole-graph parent chains end at an actual forest root, so vertex `3`
cannot use the reflexive witness merely because it was scheduled. -/
example : ∃ r ∈ (dfsAll branchingGraph).forestRoots,
    Relation.ReflTransGen (ParentRel (dfsAll branchingGraph).parents) 3 r := by
  exact parent_chain_reaches_root branchingGraph branchingGraph.vertices 3
    (mem_dfsAll_preorder branchingGraph 3)

example : IsLeftFirstDFS branchingGraph [0] (dfs branchingGraph [0]) :=
  dfs_is_left_first branchingGraph [0]

example : ¬ IsLeftFirstDFS branchingGraph [0]
    ⟨[0, 1, 2, 3], [3, 1, 2, 0], [(1, 0), (3, 1), (2, 0)]⟩ := by
  intro h
  have heq := h.eq_dfs
  simp [dfs, loop, initial, finish, enterFrames, branchingGraph] at heq

end Cslib.Algorithms.Lean.DepthFirstSearchTests
