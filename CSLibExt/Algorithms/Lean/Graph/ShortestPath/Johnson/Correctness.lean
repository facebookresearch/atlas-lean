/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Basic
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Basic
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Construction
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Augmentation
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Adapter
import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Dijkstra
import Mathlib.Tactic.Ring

/-!
# Correctness of integer Johnson shortest paths

The fresh-source reduction and signed potential shift are certified against the canonical
Bellman-Ford occurrence paths. The endpoint-minimum adapter preserves weighted optimality,
including unequal parallel occurrences, before applying the canonical dense Dijkstra results.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Johnson

open BellmanFord

private lemma distance_finite_of_reachable {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {result : Distances n}
    (run : (bellmanFord edges source).ret = .distances result)
    (reachable : (toDirectedAdjacency edges).Reachable source target) :
    ∃ distance, result.distance.get target = some distance := by
  cases distance_eq : result.distance.get target with
  | none =>
      exact False.elim ((bellmanFord_distance_eq_none_iff run).mp distance_eq reachable)
  | some distance => exact ⟨distance, rfl⟩

private lemma readPotentials_get {n : Nat} (result : Distances n) (vertex : Fin n) :
    (readPotentials result).ret.get vertex = (result.distance.get vertex).getD 0 := by
  simp [readPotentials, buildVector_get]

private lemma reweight_nonnegative {n : Nat} {edges : List (Edge n)}
    {source : Fin n} {result : Distances n}
    (run : (bellmanFord edges source).ret = .distances result)
    (finite : ∀ vertex, ∃ distance, result.distance.get vertex = some distance)
    {edge : Edge n} (mem : edge ∈ edges) :
    0 ≤ edge.weight + (readPotentials result).ret.get edge.source -
      (readPotentials result).ret.get edge.target := by
  obtain ⟨sourceDistance, source_eq⟩ := finite edge.source
  obtain ⟨targetDistance, target_eq⟩ := finite edge.target
  obtain ⟨path, path_valid, path_weight⟩ := bellmanFord_distance_realized run source_eq
  have extended := isWeightedPath_append_edge path_valid mem rfl rfl
  have bound := bellmanFord_distance_minimal run target_eq extended
  rw [pathWeight_append_edge, path_weight] at bound
  simp only [readPotentials_get, source_eq, target_eq, Option.getD_some]
  omega

private lemma all_augmented_reweight_nonnegative {n : Nat} {edges : List (Edge n)}
    {result : Distances (n + 1)}
    (run : (bellmanFord (augment edges).ret (Fin.last n)).ret = .distances result)
    {edge : Edge (n + 1)} (member : edge ∈ (augment edges).ret) :
    0 ≤ (shiftedEdge (readPotentials result).ret edge).weight := by
  exact reweight_nonnegative run (fun vertex =>
    distance_finite_of_reachable run (augment_reachable edges vertex)) member

private lemma augmented_reweight_nonnegative {n : Nat} {edges : List (Edge n)}
    {result : Distances (n + 1)}
    (run : (bellmanFord (augment edges).ret (Fin.last n)).ret = .distances result)
    {edge : Edge n} (member : edge ∈ edges) :
    0 ≤ (shiftedEdge (readPotentials result).ret (liftEdge edge)).weight := by
  exact all_augmented_reweight_nonnegative run (augment_lift_mem member)

private lemma fresh_potential_zero {n : Nat} {edges : List (Edge n)}
    {result : Distances (n + 1)}
    (run : (bellmanFord (augment edges).ret (Fin.last n)).ret = .distances result) :
    (readPotentials result).ret.get (Fin.last n) = 0 := by
  obtain ⟨distance, distance_eq⟩ :=
    distance_finite_of_reachable run (augment_reachable edges (Fin.last n))
  obtain ⟨path, valid, weight_eq⟩ := bellmanFord_distance_realized run distance_eq
  have empty : path = [] := by
    cases path with
    | nil => rfl
    | cons first rest =>
        obtain ⟨last, last_eq, target_eq⟩ := Option.map_eq_some_iff.mp valid.2.2.2
        obtain ⟨initial, path_eq⟩ := List.getLast?_eq_some_iff.mp last_eq
        have member : last ∈ first :: rest := by rw [path_eq]; simp
        exact False.elim (augmented_target_ne_last (valid.1 last member) target_eq)
  have zero : distance = 0 := by simpa [empty, pathWeight] using weight_eq.symm
  simp [readPotentials_get, distance_eq, zero]

private lemma runRow_get {n : Nat} (prepared : Prepared n) (potential : Vector Int (n + 1))
    (source target : Fin n) :
    (runRow prepared potential source).ret.get target =
      match (prepared.graph.dijkstra prepared.weight source).ret.distance.get target with
      | none => ⊤
      | some distance => ((distance : Int) + potential.get target.castSucc -
          potential.get source.castSucc : Int) := by
  simp only [runRow, TimeM.ret_bind, buildVector_get]
  rfl

private lemma runRow_spec {n : Nat} (edges : List (Edge n))
    (potential : Vector Int (n + 1))
    (nonnegative : ∀ edge ∈ edges, 0 ≤ (shiftedEdge potential (liftEdge edge)).weight)
    (source target : Fin n) :
    let prepared := (prepare edges (reweightEdges potential (augment edges).ret).ret).ret
    let value := (runRow prepared potential source).ret.get target
    (value = ⊤ ↔ ¬(toDirectedAdjacency edges).Reachable source target) ∧
      ∀ distance : Int, value = (distance : WithTop Int) →
        (∃ path, IsWeightedPath edges source target path ∧ pathWeight path = distance) ∧
          ∀ path, IsWeightedPath edges source target path → distance ≤ pathWeight path := by
  let prepared := (prepare edges (reweightEdges potential (augment edges).ret).ret).ret
  dsimp only
  change ((runRow prepared potential source).ret.get target = ⊤ ↔ _) ∧ _
  rw [runRow_get]
  cases distance_eq : (prepared.graph.dijkstra prepared.weight source).ret.distance.get target with
  | none =>
      have unreachable := (DirectedAdjacency.dijkstra_distance_eq_none_iff
        prepared.graph prepared.weight source target).mp distance_eq
      have old_unreachable : ¬(toDirectedAdjacency edges).Reachable source target := by
        intro reachable
        exact unreachable ((prepare_reachable_iff edges potential source target).mpr reachable)
      simp [old_unreachable]
  | some distance =>
      have realizing := DirectedAdjacency.dijkstra_distance_realized prepared.graph
        prepared.weight source target distance distance_eq
      obtain ⟨path, path_valid, path_weight⟩ :=
        weighted_path_of_prepared edges potential nonnegative realizing
      have reachable : (toDirectedAdjacency edges).Reachable source target :=
        reachable_iff_exists_isWeightedPath.mpr ⟨path, path_valid⟩
      constructor
      · simp [reachable]
      · intro value value_eq
        have decoded : (distance : Int) + potential.get target.castSucc -
            potential.get source.castSucc = value := WithTop.coe_injective value_eq
        constructor
        · exact ⟨path, path_valid, by omega⟩
        · intro other other_valid
          obtain ⟨other_distance, other_prepared, bound⟩ :=
            prepared_path_of_weighted edges potential nonnegative other_valid
          have minimal := DirectedAdjacency.dijkstra_distance_minimal prepared.graph
            prepared.weight source target distance other_distance distance_eq other_prepared
          omega

/-- Johnson reports failure exactly when an original source can reach a negative cycle. -/
public theorem johnson_eq_none_iff {n : Nat} (edges : List (Edge n)) :
    (johnson edges).ret = none ↔ ∃ source : Fin n, HasReachableNegativeCycle edges source := by
  rw [← fresh_negativeCycle_iff]
  cases run_eq : (bellmanFord (augment edges).ret (Fin.last n)).ret with
  | distances result =>
      have no_cycle := (bellmanFord_returns_distances_iff (augment edges).ret (Fin.last n)).mp
        ⟨result, run_eq⟩
      simp [johnson, run_eq, no_cycle]
  | negativeCycle witness =>
      have cycle : HasReachableNegativeCycle (augment edges).ret (Fin.last n) := ⟨witness⟩
      simp [johnson, run_eq, cycle]

/-- Every returned Johnson cell has the canonical infinity, realization and minimum semantics. -/
public theorem johnson_distance_spec {n : Nat} (edges : List (Edge n))
    (distance : Fin n → Fin n → WithTop Int) (run : (johnson edges).ret = some distance)
    (source target : Fin n) :
    (distance source target = ⊤ ↔ ¬(toDirectedAdjacency edges).Reachable source target) ∧
      ∀ value : Int, distance source target = (value : WithTop Int) →
        (∃ path, IsWeightedPath edges source target path ∧ pathWeight path = value) ∧
          ∀ path, IsWeightedPath edges source target path → value ≤ pathWeight path := by
  cases run_eq : (bellmanFord (augment edges).ret (Fin.last n)).ret with
  | negativeCycle witness => simp [johnson, run_eq] at run
  | distances result =>
      let potential := (readPotentials result).ret
      let prepared := (prepare edges (reweightEdges potential (augment edges).ret).ret).ret
      have row_eq : distance source target = (runRow prepared potential source).ret.get target := by
        have output : (johnson edges).ret = some (fun source target =>
            ((buildVector n (runRow prepared potential)).ret.get source).get target) := by
          simp [johnson, run_eq, potential, prepared]
        have functions_eq := Option.some.inj (run.symm.trans output)
        rw [functions_eq]
        change ((buildVector n (runRow prepared potential)).ret.get source).get target = _
        rw [buildVector_get]
      rw [row_eq]
      exact runRow_spec edges potential (fun edge member =>
        augmented_reweight_nonnegative run_eq member) source target

end Cslib.Algorithms.Lean.Johnson
