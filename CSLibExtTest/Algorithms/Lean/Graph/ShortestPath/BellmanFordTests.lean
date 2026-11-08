/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Basic
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Correctness

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BellmanFordTests

open BellmanFord

#check Edge
#check toDirectedAdjacency
#check pathVertices
#check pathWeight
#check IsWeightedPath
#check edge_toDirectedAdjacency_iff
#check reachable_iff_exists_isWeightedPath
#check ReachableNegativeCycle
#check HasReachableNegativeCycle
#check Distances
#check Distances.pathTo?
#check Cost
#check Cost.total
#check Result
#check bellmanFord
#check bellmanFord_returns_distances_iff
#check bellmanFord_returns_negativeCycle_iff
#check bellmanFord_distance_realized
#check bellmanFord_distance_minimal
#check bellmanFord_distance_eq_none_iff
#check bellmanFord_source_predecessor_eq_none
#check bellmanFord_predecessor_spec
#check bellmanFord_pathTo?_eq_none_iff
#check bellmanFord_pathTo?_spec
#check bellmanFord_relaxationChecks
#check bellmanFord_relaxationChecks_eq_mul
#check bellmanFord_cycleWitnessSteps_eq_zero
#check bellmanFord_cycleWitnessSteps_eq
#check bellmanFord_cycleWitnessSteps_le
#check bellmanFord_total_le

def edge {n : Nat} (source target : Fin n) (weight : Int) : Edge n :=
  ⟨source, target, weight⟩

structure RunSummary where
  success : Bool
  distance : Option Int
  predecessorWeight : Option Int
  pathWeights : Option (List Int)
  prefixWeights : List Int
  cycleWeights : List Int
  relaxationChecks : Nat
  cycleWitnessSteps : Nat
deriving DecidableEq

def summary (success : Bool) (distance predecessorWeight : Option Int)
    (pathWeights : Option (List Int)) (prefixWeights cycleWeights : List Int)
    (relaxationChecks cycleWitnessSteps : Nat) : RunSummary :=
  ⟨success, distance, predecessorWeight, pathWeights, prefixWeights, cycleWeights,
    relaxationChecks, cycleWitnessSteps⟩

def runSummary {n : Nat} (edges : List (Edge n)) (source target : Fin n) :
    RunSummary :=
  let run := bellmanFord edges source
  match run.ret with
  | .distances result =>
      summary true (result.distance.get target)
        ((result.predecessor.get target).map Edge.weight)
        ((result.pathTo? target).map (·.map Edge.weight)) [] []
        run.time.relaxationChecks run.time.cycleWitnessSteps
  | .negativeCycle witness =>
      summary false none none none (witness.prefix.map Edge.weight)
        (witness.cycle.map Edge.weight) run.time.relaxationChecks run.time.cycleWitnessSteps

def runPredecessorSource? {n : Nat} (edges : List (Edge n))
    (source target : Fin n) : Option (Fin n) :=
  match (bellmanFord edges source).ret with
  | .distances result => (result.predecessor.get target).map Edge.source
  | .negativeCycle _ => none

def allMemDecidable {n : Nat} (left right : List (Edge n)) :
    Decidable (∀ item ∈ left, item ∈ right) := by
  induction left with
  | nil => exact isTrue (by simp)
  | cons item rest induction =>
      if item_mem : item ∈ right then
        match induction with
        | isTrue rest_mem => exact isTrue (by simp_all)
        | isFalse rest_not_mem => exact isFalse (by simp_all)
      else exact isFalse (by simp_all)

def weightedPathDecidable {n : Nat} (edges : List (Edge n))
    (source target : Fin n) (path : List (Edge n)) :
    Decidable (IsWeightedPath edges source target path) := by
  cases path with
  | nil =>
      unfold IsWeightedPath
      letI : Decidable (∀ edge ∈ ([] : List (Edge n)), edge ∈ edges) :=
        allMemDecidable [] edges
      infer_instance
  | cons first rest =>
      unfold IsWeightedPath
      letI : Decidable (∀ edge ∈ first :: rest, edge ∈ edges) :=
        allMemDecidable (first :: rest) edges
      infer_instance

def candidateChecks {n : Nat} (edges : List (Edge n)) (source base : Fin n)
    (sourcePath cycle : List (Edge n)) : Bool × Bool × Bool × Bool × Bool × Bool :=
  letI : Decidable (IsWeightedPath edges source base sourcePath) :=
    weightedPathDecidable edges source base sourcePath
  letI : Decidable (IsWeightedPath edges base base cycle) :=
    weightedPathDecidable edges base base cycle
  (decide (IsWeightedPath edges source base sourcePath),
    decide (pathVertices source sourcePath).Nodup,
    decide (IsWeightedPath edges base base cycle),
    decide (cycle ≠ []),
    decide (cycle.map Edge.source).Nodup,
    decide (pathWeight cycle < 0))

macro "bf_reduce" : tactic =>
  `(tactic| norm_num [edge, Fin.ext_iff] <;>
    simp [runSummary, summary, bellmanFord, Distances.pathTo?, Distances.pathTo?.follow,
    runPredecessorSource?, IsWeightedPath,
    pathVertices, pathWeight,
    Vector.get, Fin.cast] <;> norm_num <;> with_reducible decide)

/-- The singleton edgeless graph succeeds with the initialized source state and zero cost. -/
example :
    runSummary ([] : List (Edge 1)) 0 0 =
      summary true (some 0) none (some []) [] [] 0 0 := by
  bf_reduce

example : runSummary [edge 0 0 3] (0 : Fin 1) 0 =
    summary true (some 0) none (some []) [] [] 1 0 := by
  bf_reduce

example : runSummary [edge 0 0 0] (0 : Fin 1) 0 =
    summary true (some 0) none (some []) [] [] 1 0 := by
  bf_reduce

example : runSummary [edge 0 0 (-1)] (0 : Fin 1) 0 =
    summary false none none none [] [-1] 1 2 := by
  bf_reduce

example : runSummary [edge 0 1 (-7)] (0 : Fin 2) 1 =
    summary true (some (-7)) (some (-7)) (some [-7]) [] [] 2 0 := by
  bf_reduce

example : runSummary [edge 0 1 5, edge 0 1 (-2)] (0 : Fin 2) 1 =
    summary true (some (-2)) (some (-2)) (some [-2]) [] [] 4 0 := by
  bf_reduce

example : runSummary [edge 0 1 4, edge 0 1 4] (0 : Fin 2) 1 =
    summary true (some 4) (some 4) (some [4]) [] [] 4 0 := by
  bf_reduce

example : runSummary [edge 0 2 8, edge 0 1 2, edge 1 2 3] (0 : Fin 3) 2 =
    summary true (some 5) (some 3) (some [2, 3]) [] [] 9 0 := by
  bf_reduce

example : runSummary [edge 1 1 (-1)] (0 : Fin 2) 1 =
    summary true none none none [] [] 2 0 := by
  bf_reduce

example : runSummary [edge 0 1 1, edge 1 2 (-3), edge 2 1 1] (0 : Fin 3) 2 =
    summary false none none none [1, -3] [1, -3] 9 7 := by
  bf_reduce

example : runSummary [edge 0 1 (-2), edge 1 0 1] (0 : Fin 2) 1 =
    summary false none none none [] [-2, 1] 4 4 := by
  bf_reduce

example : runSummary [edge 0 1 0, edge 1 0 0] (0 : Fin 2) 1 =
    summary true (some 0) (some 0) (some [0]) [] [] 4 0 := by
  bf_reduce

example : runSummary [edge 1 0 4, edge 0 1 4] (0 : Fin 2) 1 =
    summary true (some 4) (some 4) (some [4]) [] [] 4 0 := by
  bf_reduce

example : runSummary [edge 0 1 (10 ^ 30), edge 1 2 (-(10 ^ 30) - 7)]
    (0 : Fin 3) 2 =
    summary true (some (-7)) (some (-(10 ^ 30) - 7))
      (some [10 ^ 30, -(10 ^ 30) - 7]) [] [] 6 0 := by
  bf_reduce

/-- An unreachable negative two-cycle does not affect the successful branch. -/
example : runSummary [edge 1 2 (-3), edge 2 1 1] (0 : Fin 4) 2 =
    summary true none none none [] [] 8 0 := by
  bf_reduce

/-- Mixed positive, zero, and negative loops plus duplicate ordinary edges retain one witness. -/
example : runSummary
    [edge 0 0 2, edge 0 0 0, edge 0 1 4, edge 0 1 4, edge 1 1 (-1)]
    (0 : Fin 2) 1 = summary false none none none [4] [-1] 10 4 := by
  bf_reduce

/-- Equal alternatives preserve the first predecessor selected by edge order. -/
example : runPredecessorSource?
    [edge 0 1 1, edge 1 3 2, edge 0 2 1, edge 2 3 2] (0 : Fin 4) 3 = some 1 := by
  bf_reduce

example : runPredecessorSource?
    [edge 0 2 1, edge 2 3 2, edge 0 1 1, edge 1 3 2] (0 : Fin 4) 3 = some 2 := by
  bf_reduce

/-- An edge leaving a disconnected component never creates a finite target distance. -/
example : runSummary [edge 2 3 (-5)] (0 : Fin 4) 3 =
    summary true none none none [] [] 4 0 := by
  bf_reduce

/-- A four-vertex acyclic instance exercises populated distance and reconstruction fields. -/
example : runSummary
    [edge 0 1 1, edge 1 3 2, edge 0 2 7, edge 2 3 1] (0 : Fin 4) 3 =
    summary true (some 3) (some 2) (some [1, 2]) [] [] 16 0 := by
  bf_reduce

/-- A four-vertex reachable cycle returns a populated witness branch. -/
example : runSummary
    [edge 0 1 1, edge 1 2 (-3), edge 2 1 1, edge 2 3 4] (0 : Fin 4) 3 =
    summary false none none none [1] [-3, 1] 16 7 := by
  bf_reduce

/-- The chosen parallel occurrence makes the reachable two-cycle negative. -/
example : runSummary [edge 0 1 5, edge 0 1 (-2), edge 1 0 1] (0 : Fin 2) 1 =
    summary false none none none [] [-2, 1] 6 4 := by
  bf_reduce

/-- A positive closed candidate passes structural fields but fails negativity. -/
example : candidateChecks [edge 0 1 0, edge 1 1 2] (0 : Fin 2) 1
    [edge 0 1 0] [edge 1 1 2] = (true, true, true, true, true, false) := by
  decide

/-- A disconnected candidate fails prefix reachability while its cycle fields remain valid. -/
example : candidateChecks [edge 1 1 (-1)] (0 : Fin 2) 1 [] [edge 1 1 (-1)] =
    (false, true, true, true, true, true) := by
  decide

example {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    (∃ result, (bellmanFord edges source).ret = Result.distances result) ↔
      ¬HasReachableNegativeCycle edges source :=
  bellmanFord_returns_distances_iff edges source

example {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    (∃ witness, (bellmanFord edges source).ret = Result.negativeCycle witness) ↔
      HasReachableNegativeCycle edges source :=
  bellmanFord_returns_negativeCycle_iff edges source

example {n : Nat} {edges : List (Edge n)} {source target : Fin n}
    {result : Distances n} {distance : Int}
    (hRun : (bellmanFord edges source).ret = Result.distances result)
    (hDistance : result.distance.get target = some distance) :
    ∃ path, IsWeightedPath edges source target path ∧ pathWeight path = distance :=
  bellmanFord_distance_realized hRun hDistance

example {n : Nat} {edges : List (Edge n)} {source target : Fin n}
    {result : Distances n} {distance : Int} {path : List (Edge n)}
    (hRun : (bellmanFord edges source).ret = Result.distances result)
    (hDistance : result.distance.get target = some distance)
    (hPath : IsWeightedPath edges source target path) : distance ≤ pathWeight path :=
  bellmanFord_distance_minimal hRun hDistance hPath

example {n : Nat} {edges : List (Edge n)} {source target : Fin n}
    {result : Distances n}
    (hRun : (bellmanFord edges source).ret = Result.distances result) :
    result.distance.get target = none ↔
      ¬(toDirectedAdjacency edges).Reachable source target :=
  bellmanFord_distance_eq_none_iff hRun

example {n : Nat} {edges : List (Edge n)} {source : Fin n}
    {result : Distances n}
    (hRun : (bellmanFord edges source).ret = Result.distances result) :
    result.predecessor.get source = none :=
  bellmanFord_source_predecessor_eq_none hRun

example {n : Nat} {edges : List (Edge n)} {source target : Fin n}
    {result : Distances n} {predecessor : Edge n}
    (hRun : (bellmanFord edges source).ret = Result.distances result)
    (hPredecessor : result.predecessor.get target = some predecessor) :
    predecessor ∈ edges ∧ predecessor.target = target ∧
      ∃ sourceDistance targetDistance,
        result.distance.get predecessor.source = some sourceDistance ∧
          result.distance.get target = some targetDistance ∧
          targetDistance = sourceDistance + predecessor.weight :=
  bellmanFord_predecessor_spec hRun hPredecessor

example {n : Nat} {edges : List (Edge n)} {source target : Fin n}
    {result : Distances n}
    (hRun : (bellmanFord edges source).ret = Result.distances result) :
    result.pathTo? target = none ↔ result.distance.get target = none :=
  bellmanFord_pathTo?_eq_none_iff hRun

example {n : Nat} {edges : List (Edge n)} {source target : Fin n}
    {result : Distances n} {path : List (Edge n)}
    (hRun : (bellmanFord edges source).ret = Result.distances result)
    (hPath : result.pathTo? target = some path) :
    IsWeightedPath edges source target path ∧
      result.distance.get target = some (pathWeight path) ∧
      (pathVertices source path).Nodup ∧ path.length < n :=
  bellmanFord_pathTo?_spec hRun hPath

example {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (witness : ReachableNegativeCycle edges source)
    (hRun : (bellmanFord edges source).ret = Result.negativeCycle witness) :
    (bellmanFord edges source).time.cycleWitnessSteps =
      n + witness.cycle.length + witness.prefix.length :=
  bellmanFord_cycleWitnessSteps_eq edges source witness hRun

example {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    (bellmanFord edges source).time.relaxationChecks =
      (n - 1) * edges.length + edges.length :=
  bellmanFord_relaxationChecks edges source

example {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    (bellmanFord edges source).time.relaxationChecks = n * edges.length :=
  bellmanFord_relaxationChecks_eq_mul edges source

example {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (result : Distances n)
    (hRun : (bellmanFord edges source).ret = Result.distances result) :
    (bellmanFord edges source).time.cycleWitnessSteps = 0 :=
  bellmanFord_cycleWitnessSteps_eq_zero edges source result hRun

example {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    (bellmanFord edges source).time.cycleWitnessSteps ≤ 3 * n :=
  bellmanFord_cycleWitnessSteps_le edges source

example {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    (bellmanFord edges source).time.total ≤ 4 * n * edges.length :=
  bellmanFord_total_le edges source

example : (toDirectedAdjacency ([] : List (Edge 0))).vertices = [] := rfl

example : IsEmpty (Edge 0) :=
  ⟨fun edge => Fin.elim0 edge.source⟩

end Cslib.Algorithms.Lean.BellmanFordTests
