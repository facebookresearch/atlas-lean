/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch
public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency

import all Init.Data.Queue

/-! Importing executable and theorem tests for breadth-first search. -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BreadthFirstSearchTests

open BreadthFirstSearch

private def emptyGraph : DirectedAdjacency (Fin 0) where
  vertices := []
  vertices_nodup := by simp
  vertices_complete vertex := Fin.elim0 vertex
  adjacency vertex := Fin.elim0 vertex

example : Nonempty (DirectedAdjacency (Fin 0)) := ⟨emptyGraph⟩

example : ¬ Nonempty (Fin 0) := by simp

private def singletonGraph : Fin 1 → List (Fin 1)
  | _ => []

example : (bfsFin singletonGraph 0).order = [0] := by
  unfold bfsFin
  rw [bfs_eq_bfsModel]
  decide

example : (bfsFin singletonGraph 0).distance 0 = some 0 := by
  unfold bfsFin
  rw [bfs_eq_bfsModel]
  decide

private def directedCycle : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => [2]
  | _ => [0]

example : (bfsFin directedCycle 0).order = [0, 1, 2] := by
  unfold bfsFin
  rw [bfs_eq_bfsModel]
  decide

example : (bfsFin directedCycle 0).order.Nodup := by
  unfold bfsFin
  exact order_nodup _ _

example : (bfsFin directedCycle 0).distance 0 = some 0 := by
  unfold bfsFin
  rw [bfs_eq_bfsModel]
  decide

example : (bfsFin directedCycle 0).distance 1 = some 1 := by
  unfold bfsFin
  rw [bfs_eq_bfsModel]
  decide

example : (bfsFin directedCycle 0).distance 2 = some 2 := by
  unfold bfsFin
  rw [bfs_eq_bfsModel]
  decide

/-- Four vertices used by the importing BFS regression tests. -/
inductive Vertex
  | source
  | left
  | right
  | target
  deriving DecidableEq, Hashable

private def vertexBEq : Vertex → Vertex → Bool
  | .source, .source => true
  | .left, .left => true
  | .right, .right => true
  | .target, .target => true
  | _, _ => false

private instance : BEq Vertex := ⟨vertexBEq⟩

private instance : ReflBEq Vertex where
  rfl := by
    intro vertex
    change vertexBEq vertex vertex = true
    cases vertex <;> rfl

private instance : LawfulBEq Vertex where
  eq_of_beq := by
    intro a b h
    change vertexBEq a b = true at h
    cases a <;> cases b <;> simp_all [vertexBEq]

open Vertex

private def diamond : DirectedAdjacency Vertex where
  vertices := [source, left, right, target]
  vertices_nodup := by decide
  vertices_complete vertex := by cases vertex <;> simp
  adjacency
    | source => [left, right]
    | left => [target]
    | right => [target]
    | target => []

example : (bfs diamond source).order.Nodup :=
  order_nodup diamond source

example : (bfs diamond source).distance source = some 0 :=
  source_distance diamond source

example : target ∈ (bfs diamond source).order ↔ diamond.Reachable source target :=
  order_mem_iff_reachable diamond source target

example : (∃ distance, (bfs diamond source).distance target = some distance) ↔
    diamond.Reachable source target :=
  distance_present_iff_reachable diamond source target

example : (bfs diamond source).order = [source, left, right, target] := by
  rw [bfs_eq_bfsModel]
  decide

example : (bfs diamond source).distance left = some 1 := by
  rw [bfs_eq_bfsModel]
  decide

example : (bfs diamond source).distance right = some 1 := by
  rw [bfs_eq_bfsModel]
  decide

example : (bfs diamond source).distance target = some 2 := by
  rw [bfs_eq_bfsModel]
  decide

private def reversedDiamond : DirectedAdjacency Vertex where
  vertices := [source, left, right, target]
  vertices_nodup := by decide
  vertices_complete vertex := by cases vertex <;> simp
  adjacency
    | source => [right, left]
    | left => [target]
    | right => [target]
    | target => []

example : (bfs reversedDiamond source).order = [source, right, left, target] := by
  rw [bfs_eq_bfsModel]
  decide

example : (bfs reversedDiamond source).distance left = some 1 := by
  rw [bfs_eq_bfsModel]
  decide

example : (bfs reversedDiamond source).distance right = some 1 := by
  rw [bfs_eq_bfsModel]
  decide

example : (bfs reversedDiamond source).distance source = some 0 := by
  rw [bfs_eq_bfsModel]
  decide

example : (bfs reversedDiamond source).distance target = some 2 := by
  rw [bfs_eq_bfsModel]
  decide

private def duplicateSelfLoop : DirectedAdjacency Vertex where
  vertices := [source, left, right, target]
  vertices_nodup := by decide
  vertices_complete vertex := by cases vertex <;> simp
  adjacency
    | source => [source, left, left]
    | _ => []

example : (bfs duplicateSelfLoop source).order = [source, left] := by
  rw [bfs_eq_bfsModel]
  decide

example : (bfs duplicateSelfLoop source).distance source = some 0 := by
  rw [bfs_eq_bfsModel]
  decide

example : (bfs duplicateSelfLoop source).distance target = none := by
  rw [bfs_eq_bfsModel]
  decide

private def fifoDiscriminator : Fin 5 → List (Fin 5)
  | 0 => [1, 2]
  | 1 => [3]
  | 2 => [4]
  | 3 => [4]
  | _ => []

example : (bfsFin fifoDiscriminator 0).order = [0, 1, 2, 3, 4] := by
  unfold bfsFin
  rw [bfs_eq_bfsModel]
  decide

example : (bfsFin fifoDiscriminator 0).distance 4 = some 2 := by
  unfold bfsFin
  rw [bfs_eq_bfsModel]
  decide

end Cslib.Algorithms.Lean.BreadthFirstSearchTests
