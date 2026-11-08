/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG.Basic
import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Correctness

/-!
# DAG predecessor extraction and validated-wrapper correctness

The reconstruction theorem is a generic statement about the existing distance
object and bounded predecessor ranks. Instantiating it with the certified
topological order proves that the actual one-pass output forms rooted shortest
paths. No Bellman-Ford execution is used to justify DAG output.

The Kahn wrapper rejects every cyclic graph, not only reachable negative cycles.
Its failure data are processed and remaining vertices, not an executable cycle.
This remains the partial integer-weight milestone of CLRS Section 22.2.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DAGShortestPaths

open BellmanFord

private theorem extraction {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    ∀ target,
      ((run edges source order horder).ret.pathTo? target = none ↔
        (run edges source order horder).ret.distance.get target = none) ∧
      ∀ path value, (run edges source order horder).ret.pathTo? target = some path →
        (run edges source order horder).ret.distance.get target = some value →
        IsWeightedPath edges source target path ∧ pathWeight path = value ∧ path.length < n := by
  have hp : order.Perm (List.finRange n) :=
    (List.perm_ext_iff_of_nodup horder.1 (List.nodup_finRange n)).mpr horder.2.1
  have hlength : order.length = n := by simpa using hp.length_eq
  have hbound (vertex : Fin n) : order.idxOf vertex < n := by
    have hm := (horder.2.1 vertex).mpr (List.mem_finRange vertex)
    simpa only [hlength] using List.idxOf_lt_length_of_mem hm
  have hroot : (run edges source order horder).ret.distance.get
      (run edges source order horder).ret.source = some 0 := by
    simpa only [run_source] using run_source_distance edges source order horder
  have hfinite (target : Fin n) (value : Int)
      (hd : (run edges source order horder).ret.distance.get target = some value)
      (hne : target ≠ (run edges source order horder).ret.source) :
      ∃ edge, (run edges source order horder).ret.predecessor.get target = some edge :=
    run_finite_predecessor edges source order horder target value hd
      (by simpa only [run_source] using hne)
  simpa only [run_source] using
    Distances.pathTo?_spec_of_rank (run edges source order horder).ret edges order.idxOf
      hbound hroot (run_infinite_predecessor edges source order horder) hfinite
      (run_predecessor_spec edges source order horder)

/-- Predecessor extraction fails exactly at infinite estimates. -/
public theorem run_pathTo?_eq_none_iff {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (target : Fin n) :
    (run edges source order horder).ret.pathTo? target = none ↔
      (run edges source order horder).ret.distance.get target = none :=
  (extraction edges source order horder target).1

/-- An extracted path is a concrete shortest input path with at most n-1 edges. -/
public theorem run_pathTo?_spec {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (target : Fin n) (path : List (Edge n))
    (hpath : (run edges source order horder).ret.pathTo? target = some path) :
    IsWeightedPath edges source target path ∧
      (run edges source order horder).ret.distance.get target = some (pathWeight path) ∧
      path.length < n ∧
      ∀ other, IsWeightedPath edges source target other → pathWeight path ≤ pathWeight other := by
  cases hd : (run edges source order horder).ret.distance.get target with
  | none =>
      have impossible := (run_pathTo?_eq_none_iff edges source order horder target).mpr hd
      rw [hpath] at impossible
      contradiction
  | some value =>
      obtain ⟨hp, hw, hl⟩ := (extraction edges source order horder target).2 path value hpath hd
      refine ⟨hp, by simp only [hw], hl, ?_⟩
      intro other ho
      rw [hw]
      exact run_distance_minimal edges source order horder target value hd other ho


/-- Every failure certifies an actual directed cycle among the remaining vertices. -/
public theorem dagShortestPaths_failure_cycle {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (processed remaining : List (Fin n))
    (hf : (dagShortestPaths edges source).ret = .error (processed, remaining)) :
    ∃ cycle, TopologicalSort.DirectedCycleIn (toDirectedAdjacency edges) remaining cycle :=
  TopologicalSort.failure_cycle _ _ _
    ((dagShortestPaths_eq_error_iff edges source processed remaining).mp hf)

/-- The total wrapper succeeds exactly on DAGs, including disconnected DAGs. -/
public theorem dagShortestPaths_returns_iff_acyclic {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (∃ result, (dagShortestPaths edges source).ret = .ok result) ↔
      TopologicalSort.IsAcyclic (toDirectedAdjacency edges) := by
  rw [← TopologicalSort.succeeds_iff_acyclic]
  constructor
  · rintro ⟨result, hr⟩
    obtain ⟨order, _, hs, _⟩ := (dagShortestPaths_eq_ok_iff edges source result).mp hr
    exact ⟨order, hs⟩
  · rintro ⟨order, hs⟩
    let horder := TopologicalSort.success_isTopologicalOrder _ _ hs
    exact ⟨(run edges source order horder).ret,
      (dagShortestPaths_eq_ok_iff edges source _).mpr ⟨order, horder, hs, rfl⟩⟩

/-- Successful wrapper distances are realized and minimal; failure is not a distance result. -/
public theorem dagShortestPaths_distance_spec {n : Nat} (edges : List (Edge n))
    (source : Fin n) (result : Distances n)
    (hr : (dagShortestPaths edges source).ret = .ok result) (target : Fin n) (value : Int)
    (hd : result.distance.get target = some value) :
    (∃ path, IsWeightedPath edges source target path ∧ pathWeight path = value) ∧
      ∀ path, IsWeightedPath edges source target path → value ≤ pathWeight path := by
  obtain ⟨order, horder, _, rfl⟩ := (dagShortestPaths_eq_ok_iff edges source result).mp hr
  exact ⟨run_distance_realized edges source order horder target value hd,
    run_distance_minimal edges source order horder target value hd⟩

/-- Successful-wrapper infinity denotes precisely canonical unreachability. -/
public theorem dagShortestPaths_distance_eq_none_iff {n : Nat} (edges : List (Edge n))
    (source : Fin n) (result : Distances n)
    (hr : (dagShortestPaths edges source).ret = .ok result) (target : Fin n) :
    result.distance.get target = none ↔ ¬(toDirectedAdjacency edges).Reachable source target := by
  obtain ⟨order, horder, _, rfl⟩ := (dagShortestPaths_eq_ok_iff edges source result).mp hr
  exact run_distance_eq_none_iff edges source order horder target

/-- A successful-wrapper predecessor path is an actual shortest path with at most n-1 edges. -/
public theorem dagShortestPaths_pathTo?_spec {n : Nat} (edges : List (Edge n))
    (source : Fin n) (result : Distances n)
    (hr : (dagShortestPaths edges source).ret = .ok result) (target : Fin n)
    (path : List (Edge n)) (hp : result.pathTo? target = some path) :
    IsWeightedPath edges source target path ∧ result.distance.get target = some (pathWeight path) ∧
      path.length < n ∧
      ∀ other, IsWeightedPath edges source target other → pathWeight path ≤ pathWeight other := by
  obtain ⟨order, horder, _, rfl⟩ := (dagShortestPaths_eq_ok_iff edges source result).mp hr
  exact run_pathTo?_spec edges source order horder target path hp

end Cslib.Algorithms.Lean.DAGShortestPaths
