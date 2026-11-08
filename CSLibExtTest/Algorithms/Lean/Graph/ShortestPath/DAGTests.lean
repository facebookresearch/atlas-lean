/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG
public meta import CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG.Basic
public meta import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Basic
public meta import CSLibExt.Algorithms.Lean.Graph.TopologicalSort
public meta import Cslib.Algorithms.Lean.TimeM

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DAGShortestPathsTests

open BellmanFord DAGShortestPaths

private def require (condition : Bool) (description : String) : IO Unit :=
  unless condition do throw (IO.userError description)

private def checkSuccess {n : Nat} (name : String) (edges : List (Edge n))
    (source : Fin n) (expected : List (Option Int))
    (updates : Nat) : IO (Distances n) := do
  let computation := dagShortestPaths edges source
  match computation.ret with
  | .error _ => throw (IO.userError s!"{name}: topology rejected")
  | .ok result =>
      let actual := (List.finRange n).map result.distance.get
      require (actual == expected) s!"{name}: distances {actual}, expected {expected}"
      require (computation.time.vertexVisits == n) s!"{name}: vertex visits"
      require (computation.time.edgeRelaxations == edges.length) s!"{name}: relaxations"
      require (computation.time.distanceUpdates == updates) s!"{name}: installations"
      require (result.source == source) s!"{name}: source field"
      require (result.predecessor.get source == none) s!"{name}: source predecessor"
      for vertex in List.finRange n do
        match result.distance.get vertex, result.pathTo? vertex with
        | none, none => pure ()
        | some value, some path =>
            letI : Decidable (IsWeightedPath edges source vertex path) := by
              unfold IsWeightedPath
              rw [List.isChain_iff_forall₂]
              cases path <;> infer_instance
            require (decide (IsWeightedPath edges source vertex path))
              s!"{name}: invalid extracted path"
            require (pathWeight path == value) s!"{name}: extracted weight"
            require (path.length < n) s!"{name}: extracted path length"
        | _, _ => throw (IO.userError s!"{name}: reachability/extraction mismatch")
      IO.println s!"{name}: {actual}; cost {repr computation.time}"
      pure result

private def clrsFigure22_5 : List (Edge 6) :=
  [⟨0, 1, 5⟩, ⟨0, 2, 3⟩, ⟨1, 2, 2⟩, ⟨1, 3, 6⟩,
    ⟨2, 3, 7⟩, ⟨2, 4, 4⟩, ⟨2, 5, 2⟩,
    ⟨3, 4, -1⟩, ⟨3, 5, 1⟩, ⟨4, 5, -2⟩]

private def diamond : List (Edge 4) := [⟨0, 1, 0⟩, ⟨0, 2, 0⟩, ⟨1, 3, 0⟩, ⟨2, 3, 0⟩]

/- Figure 22.5, CLRS fourth edition printed p618 (PDF p640), rendered and checked:
   vertices r,s,t,x,y,z are 0,1,2,3,4,5; source s is 1. -/
#eval do
  let _ ← checkSuccess "CLRS Figure 22.5" clrsFigure22_5 1
    [none, some 0, some 2, some 6, some 5, some 3] 6
  let negative : List (Edge 3) := [⟨0, 1, 2⟩, ⟨0, 2, 1⟩, ⟨1, 2, -5⟩]
  let _ ← checkSuccess "negative improvement" negative 0 [some 0, some 2, some (-3)] 3
  let parallel : List (Edge 2) := [⟨0, 1, 7⟩, ⟨0, 1, -2⟩, ⟨0, 1, -2⟩]
  let _ ← checkSuccess "parallel with identical duplicate" parallel 0 [some 0, some (-2)] 2
  let _ ← checkSuccess "parallel reversed" parallel.reverse 0 [some 0, some (-2)] 1
  let singleton ← checkSuccess "edgeless singleton" ([] : List (Edge 1)) 0 [some 0] 0
  require (singleton.pathTo? 0 == some []) "singleton empty path"
  let _ ← checkSuccess "edgeless disconnected" ([] : List (Edge 3)) 1
    [none, some 0, none] 0
  let _ ← checkSuccess "unreachable negative component" ([⟨2, 3, -9⟩] : List (Edge 4)) 0
    [some 0, none, none, none] 0
  let tied ← checkSuccess "zero-weight diamond" diamond 0
    [some 0, some 0, some 0, some 0] 3
  require (tied.predecessor.get 3 == some (⟨1, 3, 0⟩ : Edge 4)) "first predecessor on tie"
  let _ ← checkSuccess "negative chain" ([⟨0, 1, -2⟩, ⟨1, 2, -3⟩,
    ⟨2, 3, -4⟩, ⟨3, 4, -5⟩] : List (Edge 5)) 0
    [some 0, some (-2), some (-5), some (-9), some (-14)] 4
  let _ ← checkSuccess "negative incoming source edge" ([⟨0, 1, -7⟩] : List (Edge 2)) 1
    [none, some 0] 0
  let _ ← checkSuccess "non-numeric topological order" ([⟨0, 2, 4⟩, ⟨2, 1, -9⟩] : List (Edge 3)) 0
    [some 0, some (-5), some 4] 2
  let fifo : List (Edge 4) := [⟨0, 2, 0⟩, ⟨0, 1, 0⟩, ⟨2, 3, 0⟩, ⟨1, 3, 0⟩]
  let fifoFirst ← checkSuccess "source-order FIFO tie" fifo 0
    [some 0, some 0, some 0, some 0] 3
  require (fifoFirst.predecessor.get 3 == some (⟨2, 3, 0⟩ : Edge 4))
    "source-order FIFO predecessor"
  let fifoReversed ← checkSuccess "reversed source-order FIFO tie" fifo.reverse 0
    [some 0, some 0, some 0, some 0] 3
  require (fifoReversed.predecessor.get 3 == some (⟨1, 3, 0⟩ : Edge 4))
    "reversed source-order FIFO predecessor"

private def checkFailure {n : Nat} (name : String) (edges : List (Edge n))
    (source : Fin n) : IO Unit := do
  let computation := dagShortestPaths edges source
  match computation.ret with
  | .ok _ => throw (IO.userError s!"{name}: cyclic input accepted")
  | .error (processed, remaining) =>
      require (!remaining.isEmpty) s!"{name}: no remaining vertices"
      require (computation.time == 0) s!"{name}: relaxation charged on failure"
      IO.println s!"{name}: processed {processed}, remaining {remaining}"

#eval do
  checkFailure "positive cycle" ([⟨0, 1, 3⟩, ⟨1, 0, 4⟩] : List (Edge 2)) 0
  checkFailure "negative cycle" ([⟨0, 1, -3⟩, ⟨1, 0, -4⟩] : List (Edge 2)) 0
  checkFailure "positive self-loop" ([⟨0, 0, 7⟩] : List (Edge 1)) 0
  checkFailure "unreachable cycle" ([⟨1, 2, 1⟩, ⟨2, 1, 1⟩] : List (Edge 3)) 0

#eval require
  (match TopologicalSort.sort (toDirectedAdjacency ([] : List (Edge 0))) with
  | .success order => order.isEmpty
  | .failure _ _ => false) "empty topology"

private theorem diamond_orderA :
    TopologicalSort.IsTopologicalOrder (toDirectedAdjacency diamond) [0, 1, 2, 3] := by
  simp only [TopologicalSort.IsTopologicalOrder, toDirectedAdjacency, DirectedAdjacency.Edge]
  decide

private theorem diamond_orderB :
    TopologicalSort.IsTopologicalOrder (toDirectedAdjacency diamond) [0, 2, 1, 3] := by
  simp only [TopologicalSort.IsTopologicalOrder, toDirectedAdjacency, DirectedAdjacency.Edge]
  decide

#eval do
  let first := run diamond 0 [0, 1, 2, 3] diamond_orderA
  let second := run diamond 0 [0, 2, 1, 3] diamond_orderB
  require ((List.finRange 4).map first.ret.distance.get ==
    (List.finRange 4).map second.ret.distance.get) "valid-order distance independence"
  require (first.ret.predecessor.get 3 == some (⟨1, 3, 0⟩ : Edge 4)) "first-order tie"
  require (second.ret.predecessor.get 3 == some (⟨2, 3, 0⟩ : Edge 4)) "reordered tie"
  require (first.time == second.time) "reordered event counts"
  IO.println "two certified orders: same distances/counts, different valid tie predecessors"

example : ¬TopologicalSort.IsTopologicalOrder (toDirectedAdjacency diamond) [0, 1, 3] := by
  simp only [TopologicalSort.IsTopologicalOrder, toDirectedAdjacency, DirectedAdjacency.Edge]
  decide

example : ¬TopologicalSort.IsTopologicalOrder (toDirectedAdjacency diamond) [0, 1, 1, 2, 3] := by
  simp only [TopologicalSort.IsTopologicalOrder, toDirectedAdjacency, DirectedAdjacency.Edge]
  decide

example : ¬TopologicalSort.IsTopologicalOrder (toDirectedAdjacency diamond) [3, 2, 1, 0] := by
  simp only [TopologicalSort.IsTopologicalOrder, toDirectedAdjacency, DirectedAdjacency.Edge]
  decide

example : (run diamond 0 [0, 1, 2, 3] diamond_orderA).time.vertexVisits = 4 :=
  run_vertexVisits diamond 0 [0, 1, 2, 3] diamond_orderA

example : (run diamond 0 [0, 1, 2, 3] diamond_orderA).time.edgeRelaxations = 4 :=
  run_edgeRelaxations diamond 0 [0, 1, 2, 3] diamond_orderA

example : (run diamond 0 [0, 1, 2, 3] diamond_orderA).ret.distance.get 0 = some 0 :=
  run_source_distance diamond 0 [0, 1, 2, 3] diamond_orderA

#check run_distance_realized
#check run_distance_minimal
#check run_predecessor_spec
#check run_pathTo?_eq_none_iff
#check run_pathTo?_spec
#check dagShortestPaths_returns_iff_acyclic
#check dagShortestPaths_distance_spec
#check dagShortestPaths_distance_eq_none_iff
#check dagShortestPaths_pathTo?_spec
#check dagShortestPaths_failure_cycle

end Cslib.Algorithms.Lean.DAGShortestPathsTests
