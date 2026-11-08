/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.StronglyConnectedComponents

import Mathlib.Tactic.FinCases
import Std.Data.HashSet.Lemmas

@[expose] public section

set_option autoImplicit false
set_option linter.privateModule false

namespace Cslib.Algorithms.Lean.StronglyConnectedComponentsTests

open StronglyConnectedComponents
open DepthFirstSearch
open DepthFirstSearch.Internal

private instance : Hashable Empty where
  hash value := nomatch value

private def emptyGraph : DirectedAdjacency Empty where
  vertices := []
  vertices_nodup := by simp
  vertices_complete vertex := nomatch vertex
  adjacency vertex := nomatch vertex

example : components emptyGraph = [] := by
  simp [components, decreasingFinishAll, decreasingFinish, dfs, loop, initial, finish,
    enterFrames, emptyGraph]

private def singletonGraph : DirectedAdjacency (Fin 1) where
  vertices := List.finRange 1
  vertices_nodup := List.nodup_finRange 1
  vertices_complete := List.mem_finRange
  adjacency _ := []

private theorem components_singletonGraph : components singletonGraph = [[0]] := by
  have horder : decreasingFinishAll singletonGraph = [0] := by
    change decreasingFinish singletonGraph [0] = [0]
    simp [decreasingFinish, dfs, loop, initial, finish, enterFrames, singletonGraph]
  have hsame : sameComponentB singletonGraph 0 0 = true := by
    simp [sameComponentB, dfs, loop, initial, finish, enterFrames, singletonGraph]
  simp [components, horder, hsame]

example : components singletonGraph = [[0]] := components_singletonGraph

private def selfLoopGraph : DirectedAdjacency (Fin 1) where
  vertices := List.finRange 1
  vertices_nodup := List.nodup_finRange 1
  vertices_complete := List.mem_finRange
  adjacency _ := [0]

private theorem components_selfLoopGraph : components selfLoopGraph = [[0]] := by
  have horder : decreasingFinishAll selfLoopGraph = [0] := by
    change decreasingFinish selfLoopGraph [0] = [0]
    simp [decreasingFinish, dfs, loop, initial, finish, enterFrames, selfLoopGraph]
  have hsame : sameComponentB selfLoopGraph 0 0 = true := by
    simp [sameComponentB, dfs, loop, initial, finish, enterFrames, selfLoopGraph]
  simp [components, horder, hsame]

example : components selfLoopGraph = [[0]] := components_selfLoopGraph

private def disconnectedGraph : DirectedAdjacency (Fin 3) where
  vertices := List.finRange 3
  vertices_nodup := List.nodup_finRange 3
  vertices_complete := List.mem_finRange
  adjacency _ := []

private theorem components_disconnectedGraph :
    components disconnectedGraph = [[2], [1], [0]] := by
  have horder : decreasingFinishAll disconnectedGraph = [2, 1, 0] := by
    change decreasingFinish disconnectedGraph [0, 1, 2] = [2, 1, 0]
    simp [decreasingFinish, dfs, loop, initial, finish, enterFrames, disconnectedGraph]
  have hsame (left right : Fin 3) :
      sameComponentB disconnectedGraph left right = decide (left = right) := by
    fin_cases left <;> fin_cases right <;>
      simp [sameComponentB, dfs, loop, initial, finish, enterFrames, disconnectedGraph]
  simp [components, horder, hsame]

example : components disconnectedGraph = [[2], [1], [0]] :=
  components_disconnectedGraph

private def cycleGraph : DirectedAdjacency (Fin 3) where
  vertices := List.finRange 3
  vertices_nodup := List.nodup_finRange 3
  vertices_complete := List.mem_finRange
  adjacency
    | 0 => [1]
    | 1 => [2]
    | _ => [0]

private theorem components_cycleGraph : components cycleGraph = [[0, 1, 2]] := by
  have horder : decreasingFinishAll cycleGraph = [0, 1, 2] := by
    change decreasingFinish cycleGraph [0, 1, 2] = [0, 1, 2]
    simp [decreasingFinish, dfs, loop, initial, finish, enterFrames, cycleGraph]
  have hsame (left right : Fin 3) : sameComponentB cycleGraph left right = true := by
    fin_cases left <;> fin_cases right <;>
      simp [sameComponentB, dfs, loop, initial, finish, enterFrames, cycleGraph]
  simp [components, horder, hsame]

example : components cycleGraph = [[0, 1, 2]] := components_cycleGraph

private def twoComponentGraph : DirectedAdjacency (Fin 4) where
  vertices := List.finRange 4
  vertices_nodup := List.nodup_finRange 4
  vertices_complete := List.mem_finRange
  adjacency
    | 0 => [1]
    | 1 => [0, 2]
    | 2 => [3]
    | _ => [2]

private theorem components_twoComponentGraph :
    components twoComponentGraph = [[0, 1], [2, 3]] := by
  have horder : decreasingFinishAll twoComponentGraph = [0, 1, 2, 3] := by
    change decreasingFinish twoComponentGraph [0, 1, 2, 3] = [0, 1, 2, 3]
    simp [decreasingFinish, dfs, loop, initial, finish, enterFrames, twoComponentGraph]
  have hsame (left right : Fin 4) :
      sameComponentB twoComponentGraph left right =
        decide ((left.val < 2 ∧ right.val < 2) ∨ (2 ≤ left.val ∧ 2 ≤ right.val)) := by
    fin_cases left <;> fin_cases right <;>
      simp [sameComponentB, dfs, loop, initial, finish, enterFrames, twoComponentGraph]
  simp [components, horder, hsame]

example : components twoComponentGraph = [[0, 1], [2, 3]] :=
  components_twoComponentGraph

example : StronglyConnected twoComponentGraph 0 1 := by
  exact (share_component_iff_stronglyConnected twoComponentGraph 0 1).mp
    ⟨[0, 1], by simp [components_twoComponentGraph], by simp, by simp⟩

example : ¬ StronglyConnected twoComponentGraph 0 2 := by
  intro connected
  obtain ⟨block, blockMem, hzero, htwo⟩ :=
    (share_component_iff_stronglyConnected twoComponentGraph 0 2).mpr connected
  rw [components_twoComponentGraph] at blockMem
  have blockCases : block = [0, 1] ∨ block = [2, 3] := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using blockMem
  rcases blockCases with rfl | rfl
  · simp at htwo
  · simp at hzero

private def duplicateGraph : DirectedAdjacency (Fin 4) where
  vertices := List.finRange 4
  vertices_nodup := List.nodup_finRange 4
  vertices_complete := List.mem_finRange
  adjacency
    | 0 => [1, 1]
    | 1 => [0, 0, 2, 2]
    | 2 => [3, 3]
    | _ => [2, 2]

private theorem components_duplicateGraph :
    components duplicateGraph = [[0, 1], [2, 3]] := by
  have horder : decreasingFinishAll duplicateGraph = [0, 1, 2, 3] := by
    change decreasingFinish duplicateGraph [0, 1, 2, 3] = [0, 1, 2, 3]
    simp [decreasingFinish, dfs, loop, initial, finish, enterFrames, duplicateGraph]
  have hsame (left right : Fin 4) :
      sameComponentB duplicateGraph left right =
        decide ((left.val < 2 ∧ right.val < 2) ∨ (2 ≤ left.val ∧ 2 ≤ right.val)) := by
    fin_cases left <;> fin_cases right <;>
      simp [sameComponentB, dfs, loop, initial, finish, enterFrames, duplicateGraph]
  simp [components, horder, hsame]

example : components duplicateGraph = [[0, 1], [2, 3]] :=
  components_duplicateGraph

/-- Adjacency endpoints cannot lie outside the certified carrier. -/
example {V : Type} (graph : DirectedAdjacency V) (u v : V)
    (_edge : graph.Edge u v) : v ∈ graph.vertices :=
  graph.vertices_complete v

example : IsSCCPartition twoComponentGraph (components twoComponentGraph) :=
  components_isSCCPartition twoComponentGraph

example : CondensationAcyclic twoComponentGraph (components twoComponentGraph) :=
  components_condensationAcyclic twoComponentGraph

end Cslib.Algorithms.Lean.StronglyConnectedComponentsTests
