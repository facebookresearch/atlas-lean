/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Dijkstra
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Dijkstra

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DirectedAdjacencyTests

open DirectedAdjacency

@[simp]
private lemma get_vectorOfFn {α : Type*} {n : Nat} (function : Fin n → α)
    (index : Fin n) : (Vector.ofFn function).get index = function index := by
  change (Vector.ofFn function)[index.val] = function index
  simp

@[simp]
private lemma get_vectorSet {α : Type*} {n : Nat} (values : Vector α n)
    (updated index : Fin n) (value : α) :
    (values.set updated.val value updated.isLt).get index =
      if updated = index then value else values.get index := by
  by_cases h : updated = index
  · subst index
    simp only [↓reduceIte]
    change (values.set updated.val value updated.isLt)[updated.val] = value
    exact Vector.getElem_set_self updated.isLt
  · simp only [h, ↓reduceIte]
    have hval : updated.val ≠ index.val := by
      intro equality
      exact h (Fin.ext equality)
    change (values.set updated.val value updated.isLt)[index.val] = values[index.val]
    exact Vector.getElem_set_ne updated.isLt index.isLt hval

@[simp]
private lemma get_vectorSetNat {α : Type*} {n : Nat} (values : Vector α n)
    (updated : Nat) (value : α) (hupdated : updated < n) (index : Fin n) :
    (values.set updated value hupdated).get index =
      if updated = index.val then value else values.get index := by
  change (values.set updated value hupdated)[index.val] =
    if updated = index.val then value else values[index.val]
  exact Vector.getElem_set hupdated index.isLt

#check pathWeight
#check HasPathWeight
#check reachable_iff_exists_hasPathWeight
#check adjacencyEntryCount
#check DijkstraCost
#check DijkstraResult
#check DijkstraResult.pathTo?
#check dijkstra
#check dijkstra_distance_realized
#check dijkstra_distance_minimal
#check dijkstra_distance_eq_none_iff
#check dijkstra_predecessor_spec
#check dijkstra_pathTo?_eq_none_iff
#check dijkstra_pathTo?_spec
#check dijkstra_minScans
#check dijkstra_edgeRelaxations
#check dijkstra_time

example : AddMonoid DijkstraCost := inferInstance

example : LawfulMonad (TimeM DijkstraCost) := inferInstance

private def singletonGraph : DirectedAdjacency (Fin 1) where
  vertices := [0]
  vertices_nodup := by simp
  vertices_complete vertex := by
    have : vertex = 0 := Fin.eq_zero vertex
    simp [this]
  adjacency _ := []

private def singletonRun := dijkstra singletonGraph (fun _ _ => 0) 0

example : singletonRun.ret.distance.get 0 = some 0 := by
  simp [singletonRun, dijkstra, singletonGraph]

example : singletonRun.ret.predecessor.get 0 = none := by
  simp [singletonRun, dijkstra, singletonGraph]

example : singletonRun.ret.pathTo? 0 = some [0] := by
  simp [singletonRun, dijkstra, singletonGraph, DijkstraResult.pathTo?]

example : singletonRun.time.minScans = 1 := by
  simpa [singletonRun] using dijkstra_minScans singletonGraph (fun _ _ => 0) 0

example : singletonRun.time.edgeRelaxations = 0 := by
  simpa [singletonRun, adjacencyEntryCount, singletonGraph] using
    dijkstra_edgeRelaxations singletonGraph (fun _ _ => 0) 0

example : singletonRun.time.total = 1 := by
  simpa [singletonRun, adjacencyEntryCount, singletonGraph] using
    dijkstra_time singletonGraph (fun _ _ => 0) 0

private def selfLoopGraph : DirectedAdjacency (Fin 1) where
  vertices := [0]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency _ := [0]

example : (dijkstra selfLoopGraph (fun _ _ => 7) 0).ret.distance.get 0 = some 0 := by
  simp [dijkstra, selfLoopGraph]

example : (dijkstra selfLoopGraph (fun _ _ => 7) 0).ret.predecessor.get 0 = none := by
  simp [dijkstra, selfLoopGraph]

example : (dijkstra selfLoopGraph (fun _ _ => 7) 0).ret.pathTo? 0 = some [0] := by
  simp [dijkstra, selfLoopGraph, DijkstraResult.pathTo?]

example : (dijkstra selfLoopGraph (fun _ _ => 0) 0).ret.pathTo? 0 = some [0] := by
  simp [dijkstra, selfLoopGraph, DijkstraResult.pathTo?]

example : (dijkstra selfLoopGraph (fun _ _ => 0) 0).time.edgeRelaxations = 1 := by
  simpa [adjacencyEntryCount, selfLoopGraph] using
    dijkstra_edgeRelaxations selfLoopGraph (fun _ _ => 0) 0

private def cheaperGraph : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency vertex :=
    if vertex = 0 then [2, 1] else if vertex = 1 then [2] else []

private def cheaperWeight (source target : Fin 3) : Nat :=
  if source = 0 ∧ target = 2 then 10
  else if source = 0 ∧ target = 1 then 3
  else if source = 1 ∧ target = 2 then 4
  else 0

private def cheaperRun := dijkstra cheaperGraph cheaperWeight 0

example : cheaperRun.ret.distance.get 2 = some 7 := by
  simp [cheaperRun, dijkstra, cheaperGraph, cheaperWeight]

example : cheaperRun.ret.predecessor.get 2 = some 1 := by
  simp [cheaperRun, dijkstra, cheaperGraph, cheaperWeight]

example : cheaperRun.ret.pathTo? 2 = some [0, 1, 2] := by
  have htwo : cheaperRun.ret.predecessor.get 2 = some 1 := by
    simp [cheaperRun, dijkstra, cheaperGraph, cheaperWeight]
  have hone : cheaperRun.ret.predecessor.get 1 = some 0 := by
    simp [cheaperRun, dijkstra, cheaperGraph, cheaperWeight]
  have hsource : cheaperRun.ret.source = 0 := rfl
  simp [DijkstraResult.pathTo?, DijkstraResult.pathTo?.go, htwo, hone, hsource]

private def disconnectedGraph : DirectedAdjacency (Fin 4) where
  vertices := [0, 1, 2, 3]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency vertex :=
    if vertex = 0 then [1]
    else if vertex = 2 then [3]
    else if vertex = 3 then [2]
    else []

private def disconnectedRun := dijkstra disconnectedGraph (fun _ _ => 1) 0

example : disconnectedRun.ret.distance.get 2 = none := by
  simp [disconnectedRun, dijkstra, disconnectedGraph]

example : disconnectedRun.ret.predecessor.get 2 = none := by
  simp [disconnectedRun, dijkstra, disconnectedGraph]

example : disconnectedRun.ret.pathTo? 2 = none := by
  apply (dijkstra_pathTo?_eq_none_iff disconnectedGraph (fun _ _ => 1) 0 2).mpr
  simp [dijkstra, disconnectedGraph]

example : disconnectedRun.time.minScans = 16 := by
  simpa [disconnectedRun] using
    dijkstra_minScans disconnectedGraph (fun _ _ => 1) 0

example : disconnectedRun.time.edgeRelaxations = 3 := by
  simpa [disconnectedRun, adjacencyEntryCount, disconnectedGraph] using
    dijkstra_edgeRelaxations disconnectedGraph (fun _ _ => 1) 0

example : disconnectedRun.time.total = 19 := by
  simpa [disconnectedRun, adjacencyEntryCount, disconnectedGraph] using
    dijkstra_time disconnectedGraph (fun _ _ => 1) 0

example : ¬disconnectedGraph.Reachable 0 2 :=
  (dijkstra_distance_eq_none_iff disconnectedGraph (fun _ _ => 1) 0 2).mp (by
    simp [dijkstra, disconnectedGraph])

private def zeroCycleGraph : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency vertex :=
    if vertex = 0 then [1] else if vertex = 1 then [2] else [1]

private def zeroCycleRun := dijkstra zeroCycleGraph (fun _ _ => 0) 0

example : zeroCycleRun.ret.distance.get 2 = some 0 := by
  simp [zeroCycleRun, dijkstra, zeroCycleGraph]

example : zeroCycleRun.ret.pathTo? 2 = some [0, 1, 2] := by
  have htwo : zeroCycleRun.ret.predecessor.get 2 = some 1 := by
    simp [zeroCycleRun, dijkstra, zeroCycleGraph]
  have hone : zeroCycleRun.ret.predecessor.get 1 = some 0 := by
    simp [zeroCycleRun, dijkstra, zeroCycleGraph]
  have hsource : zeroCycleRun.ret.source = 0 := rfl
  simp [DijkstraResult.pathTo?, DijkstraResult.pathTo?.go, htwo, hone, hsource]

private def tieGraph : DirectedAdjacency (Fin 4) where
  vertices := [0, 2, 1, 3]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency vertex :=
    if vertex = 0 then [1, 2]
    else if vertex = 1 ∨ vertex = 2 then [3]
    else []

private def tieRun := dijkstra tieGraph (fun _ _ => 1) 0

example : tieRun.ret.predecessor.get 3 = some 2 := by
  simp [tieRun, dijkstra, tieGraph]

example : tieRun.ret.pathTo? 3 = some [0, 2, 3] := by
  have hthree : tieRun.ret.predecessor.get 3 = some 2 := by
    simp [tieRun, dijkstra, tieGraph]
  have htwo : tieRun.ret.predecessor.get 2 = some 0 := by
    simp [tieRun, dijkstra, tieGraph]
  have hsource : tieRun.ret.source = 0 := rfl
  simp [DijkstraResult.pathTo?, DijkstraResult.pathTo?.go, hthree, htwo, hsource]

private def duplicateGraph : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency vertex :=
    if vertex = 0 then [0, 1, 1]
    else if vertex = 1 then [1, 2]
    else []

private def duplicateWeight (source target : Fin 3) : Nat :=
  if source = 0 ∧ target = 1 then 5
  else if source = 1 ∧ target = 2 then 2
  else 0

private def duplicateRun := dijkstra duplicateGraph duplicateWeight 0

example : duplicateRun.ret.distance.get 2 = some 7 := by
  simp [duplicateRun, dijkstra, duplicateGraph, duplicateWeight]

example : duplicateRun.ret.pathTo? 2 = some [0, 1, 2] := by
  have htwo : duplicateRun.ret.predecessor.get 2 = some 1 := by
    simp [duplicateRun, dijkstra, duplicateGraph, duplicateWeight]
  have hone : duplicateRun.ret.predecessor.get 1 = some 0 := by
    simp [duplicateRun, dijkstra, duplicateGraph, duplicateWeight]
  have hsource : duplicateRun.ret.source = 0 := rfl
  simp [DijkstraResult.pathTo?, DijkstraResult.pathTo?.go, htwo, hone, hsource]

example : adjacencyEntryCount duplicateGraph = 5 := by
  simp [adjacencyEntryCount, duplicateGraph]

example : duplicateRun.time.edgeRelaxations = 5 := by
  simpa [duplicateRun, adjacencyEntryCount, duplicateGraph] using
    dijkstra_edgeRelaxations duplicateGraph duplicateWeight 0

private def repeatedEdgeGraph : DirectedAdjacency (Fin 2) where
  vertices := [0, 1]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency vertex := if vertex = 0 then [1, 1] else []

example : (dijkstra repeatedEdgeGraph (fun _ _ => 6) 0).ret.distance.get 1 = some 6 := by
  simp [dijkstra, repeatedEdgeGraph]

example : (dijkstra repeatedEdgeGraph (fun _ _ => 6) 0).time.edgeRelaxations = 2 := by
  simpa [adjacencyEntryCount, repeatedEdgeGraph] using
    dijkstra_edgeRelaxations repeatedEdgeGraph (fun _ _ => 6) 0

private def largeGraph : DirectedAdjacency (Fin 2) where
  vertices := [0, 1]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency vertex := if vertex = 0 then [1] else []

private def largeWeight : Fin 2 → Fin 2 → Nat := fun _ _ => 100000000000000000000

example : (dijkstra largeGraph largeWeight 0).ret.distance.get 1 =
    some 100000000000000000000 := by
  simp [dijkstra, largeGraph, largeWeight]

private def emptyFinGraph : DirectedAdjacency (Fin 0) where
  vertices := []
  vertices_nodup := by simp
  vertices_complete vertex := Fin.elim0 vertex
  adjacency vertex := Fin.elim0 vertex

example : emptyFinGraph.vertices = [] := rfl

example {target : Fin 3} {distance : Nat}
    (h : cheaperRun.ret.distance.get target = some distance) :
    HasPathWeight cheaperGraph cheaperWeight 0 target distance :=
  dijkstra_distance_realized cheaperGraph cheaperWeight 0 target distance h

example {target : Fin 3} {distance otherDistance : Nat}
    (h : cheaperRun.ret.distance.get target = some distance)
    (path : HasPathWeight cheaperGraph cheaperWeight 0 target otherDistance) :
    distance ≤ otherDistance :=
  dijkstra_distance_minimal cheaperGraph cheaperWeight 0 target distance otherDistance h path

example : cheaperRun.time.minScans = 3 * 3 :=
  dijkstra_minScans cheaperGraph cheaperWeight 0

example : cheaperRun.time.edgeRelaxations = adjacencyEntryCount cheaperGraph :=
  dijkstra_edgeRelaxations cheaperGraph cheaperWeight 0

example : cheaperRun.time.total = 3 * 3 + adjacencyEntryCount cheaperGraph :=
  dijkstra_time cheaperGraph cheaperWeight 0

example (target : Fin 3) :
    cheaperRun.ret.distance.get target = none ↔ ¬cheaperGraph.Reachable 0 target :=
  dijkstra_distance_eq_none_iff cheaperGraph cheaperWeight 0 target

example {target previous : Fin 3}
    (h : cheaperRun.ret.predecessor.get target = some previous) :
    cheaperGraph.Edge previous target ∧
      ∃ previousDistance targetDistance,
        cheaperRun.ret.distance.get previous = some previousDistance ∧
        cheaperRun.ret.distance.get target = some targetDistance ∧
        targetDistance = previousDistance + cheaperWeight previous target :=
  dijkstra_predecessor_spec cheaperGraph cheaperWeight 0 target previous h

example (target : Fin 3) :
    cheaperRun.ret.pathTo? target = none ↔ cheaperRun.ret.distance.get target = none :=
  dijkstra_pathTo?_eq_none_iff cheaperGraph cheaperWeight 0 target

example {target : Fin 3} {path : List (Fin 3)}
    (h : cheaperRun.ret.pathTo? target = some path) :
    ∃ distance, cheaperRun.ret.distance.get target = some distance ∧
      path.head? = some 0 ∧ path.getLast? = some target ∧
      path.IsChain cheaperGraph.Edge ∧ path.Nodup ∧
      pathWeight cheaperWeight path = distance :=
  dijkstra_pathTo?_spec cheaperGraph cheaperWeight 0 target path h

universe v

example {W : Type (v + 1)} (graph : DirectedAdjacency W) (weight : W → W → Nat)
    (source target : W) :
    graph.Reachable source target ↔
      ∃ distance, HasPathWeight graph weight source target distance :=
  reachable_iff_exists_hasPathWeight graph weight source target

end Cslib.Algorithms.Lean.DirectedAdjacencyTests
