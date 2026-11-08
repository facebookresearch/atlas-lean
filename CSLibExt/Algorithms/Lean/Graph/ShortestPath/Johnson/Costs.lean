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
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Adapter
import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Dijkstra
import Mathlib.Tactic.Ring

/-!
# Selected-event counts for integer Johnson shortest paths

These are counts on the same executed construction, Bellman-Ford and dense Dijkstra calls.
They are not full machine, bit or sparse-heap complexity bounds.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Johnson

open BellmanFord

private lemma sourceEdges_time {n : Nat} (vertices : List (Fin n)) :
    (sourceEdges vertices).time = vertices.length := by
  induction vertices with
  | nil => rfl
  | cons vertex rest induction => simp [sourceEdges, induction, Nat.add_comm]

private lemma liftEdges_time {n : Nat} (tail : List (Edge (n + 1)))
    (edges : List (Edge n)) : (liftEdges tail edges).time = edges.length := by
  induction edges with
  | nil => rfl
  | cons edge rest induction => simp [liftEdges, induction, Nat.add_comm]

private lemma augment_time {n : Nat} (edges : List (Edge n)) :
    (augment edges).time = edges.length + n := by
  simp [augment, sourceEdges_time, liftEdges_time, Nat.add_comm]

private lemma buildVector_tick_time {α : Type} (n cost : Nat) (value : Fin n → α) :
    (buildVector n (fun vertex => do
      TimeM.tick cost
      pure (value vertex))).time = n * cost := by
  exact buildVector_time_const n _ cost (fun _ => by simp)

private lemma readPotentials_time {n : Nat} (result : Distances n) :
    (readPotentials result).time = n := by
  simpa [readPotentials] using
    buildVector_tick_time n 1 (fun vertex => (result.distance.get vertex).getD 0)

private lemma reweightEdges_time {n : Nat} (potential : Vector Int n)
    (edges : List (Edge n)) : (reweightEdges potential edges).time = edges.length := by
  induction edges with
  | nil => rfl
  | cons edge rest induction => simp [reweightEdges, induction, Nat.add_comm]

private lemma insertPrepared_time {n : Nat} (prepared : Prepared n)
    (entry : Edge n × Edge (n + 1)) : (insertPrepared prepared entry).time = 1 := by
  simp [insertPrepared]

private lemma insertEntries_time {n : Nat} (entries : List (Edge n × Edge (n + 1)))
    (prepared : Prepared n) : (insertEntries entries prepared).time = entries.length := by
  induction entries generalizing prepared with
  | nil => rfl
  | cons entry rest induction => simp [insertEntries, insertPrepared_time, induction, Nat.add_comm]

private lemma reverseBucket_time {n : Nat} (vertices accumulator : List (Fin n)) :
    (reverseBucket vertices accumulator).time = vertices.length := by
  induction vertices generalizing accumulator with
  | nil => rfl
  | cons vertex rest induction => simp [reverseBucket, induction, Nat.add_comm]

private lemma emptyPrepared_time (n : Nat) : (emptyPrepared n).time = n^2 + n := by
  have row_time : (buildVector n (fun _ => do
      TimeM.tick 1
      pure (none : Option Nat))).time = n := by
    simpa using buildVector_tick_time n 1 (fun _ => (none : Option Nat))
  have table_time := buildVector_time_const n
    (fun _ => buildVector n (fun _ => do TimeM.tick 1; pure (none : Option Nat))) n
    (fun _ => row_time)
  have buckets_time : (buildVector n (fun _ => do
      TimeM.tick 1
      pure ([] : List (Fin n)))).time = n := by
    simpa using buildVector_tick_time n 1 (fun _ => ([] : List (Fin n)))
  simp only [emptyPrepared, TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
  rw [table_time, buckets_time]
  simp [pow_two]

private lemma runRow_time {n : Nat} (prepared : Prepared n) (potential : Vector Int (n + 1))
    (source : Fin n) :
    (runRow prepared potential source).time =
      1 + n*n + prepared.graph.adjacencyEntryCount + n := by
  simp only [runRow, TimeM.time_bind, TimeM.time_tick, DirectedAdjacency.dijkstra_time]
  rw [buildVector_time_const (cost := 1)]
  · simp [Nat.add_assoc]
  · intro target
    simp

private lemma buildVector_time_sum {α : Type} (n : Nat) (action : Fin n → TimeM Nat α) :
    (buildVector n action).time = ((List.finRange n).map (fun vertex =>
      (action vertex).time)).sum := by
  induction n with
  | zero => simp [buildVector]
  | succ n induction =>
      simp [buildVector, induction, List.finRange_succ_last, List.map_map, Function.comp_def]

private lemma occurrenceTargets_count {n : Nat} (entries : List (Edge n × Edge (n + 1))) :
    ((List.finRange n).map (fun source => (occurrenceTargets entries source).length)).sum =
      entries.length := by
  induction entries with
  | nil => simp [occurrenceTargets]
  | cons entry rest induction =>
      have indicator : ((List.finRange n).map (fun source =>
          if entry.1.source = source then 1 else 0)).sum = 1 := by
        have single := List.sum_map_eq_nsmul_single (l := List.finRange n) entry.1.source
          (fun source : Fin n => if entry.1.source = source then (1 : Nat) else 0)
          (fun other different _ => by simp [Ne.symm different])
        simpa [List.count_eq_one_of_mem (List.nodup_finRange n)
          (List.mem_finRange entry.1.source)] using single
      have expanded : ∀ source : Fin n,
          (occurrenceTargets (entry :: rest) source).length =
            (if entry.1.source = source then 1 else 0) +
              (occurrenceTargets rest source).length := by
        intro source
        by_cases equal : entry.1.source = source
        · simp [occurrenceTargets, equal, Nat.add_comm]
        · simp [occurrenceTargets, equal]
      simp_rw [expanded]
      rw [List.sum_map_add, indicator, induction]
      simp [Nat.add_comm]

private lemma prepared_adjacency_count {n : Nat} (edges : List (Edge n))
    (potential : Vector Int (n + 1)) :
    (prepare edges (reweightEdges potential (augment edges).ret).ret).ret.graph.adjacencyEntryCount
      = edges.length := by
  simp only [DirectedAdjacency.adjacencyEntryCount, Prepared.graph, prepare_bucket]
  rw [occurrenceTargets_count, zip_reweighted_augment, List.length_map]

private lemma prepare_time {n : Nat} (edges : List (Edge n))
    (potential : Vector Int (n + 1)) :
    (prepare edges (reweightEdges potential (augment edges).ret).ret).time =
      n^2 + n + 2 * edges.length := by
  simp only [prepare, TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
  rw [emptyPrepared_time, insertEntries_time, buildVector_time_sum]
  have bucket_time :
      ((List.finRange n).map (fun vertex =>
        (reverseBucket ((insertEntries (edges.zip
          (reweightEdges potential (augment edges).ret).ret) (emptyPrepared n).ret).ret.buckets.get
            vertex) []).time)).sum = edges.length := by
    have bucket_length (vertex : Fin n) :
        ((insertEntries (edges.zip (reweightEdges potential (augment edges).ret).ret)
          (emptyPrepared n).ret).ret.buckets.get vertex).length =
          (occurrenceTargets (edges.zip
            (reweightEdges potential (augment edges).ret).ret) vertex).length := by
      calc
        _ = (((insertEntries (edges.zip
            (reweightEdges potential (augment edges).ret).ret)
              (emptyPrepared n).ret).ret.buckets.get vertex).reverse).length :=
                List.length_reverse.symm
        _ = _ := by rw [inserted_entries_buckets_reverse, empty_bucket]; simp
    simp_rw [reverseBucket_time, bucket_length]
    rw [occurrenceTargets_count, zip_reweighted_augment, List.length_map]
  rw [bucket_time, zip_reweighted_augment, List.length_map]
  omega

private lemma augmented_length {n : Nat} (edges : List (Edge n)) :
    (augment edges).ret.length = edges.length + n := by
  simp [augment_ret]

private lemma runRows_time {n : Nat} (edges : List (Edge n))
    (potential : Vector Int (n + 1)) :
    (buildVector n (runRow
      (prepare edges (reweightEdges potential (augment edges).ret).ret).ret potential)).time =
        n * (1 + n*n + edges.length + n) := by
  apply buildVector_time_const
  intro source
  rw [runRow_time, prepared_adjacency_count]

private lemma johnson_time_of_distances {n : Nat} (edges : List (Edge n))
    (result : Distances (n + 1))
    (run : (bellmanFord (augment edges).ret (Fin.last n)).ret = .distances result) :
    (johnson edges).time = n^3 + n*edges.length + (n+1)*(edges.length+n) +
      2*n^2 + 4*edges.length + 5*n + 1 := by
  have bf_time : (bellmanFord (augment edges).ret (Fin.last n)).time.total =
      (n+1)*(edges.length+n) := by
    change (bellmanFord (augment edges).ret (Fin.last n)).time.relaxationChecks +
      (bellmanFord (augment edges).ret (Fin.last n)).time.cycleWitnessSteps = _
    rw [bellmanFord_relaxationChecks_eq_mul,
      bellmanFord_cycleWitnessSteps_eq_zero _ _ _ run, Nat.add_zero, augmented_length]
  simp only [johnson, TimeM.time_bind, run, TimeM.time_pure, Nat.add_zero]
  rw [augment_time, bf_time, readPotentials_time, reweightEdges_time,
    prepare_time, runRows_time, augmented_length]
  ring

/-- Successful Johnson executions have exactly the selected construction, scan and decode cost. -/
public theorem johnson_time_of_success {n : Nat} (edges : List (Edge n))
    (distance : Fin n → Fin n → WithTop Int) (run : (johnson edges).ret = some distance) :
    (johnson edges).time = n^3 + n*edges.length + (n+1)*(edges.length+n) +
      2*n^2 + 4*edges.length + 5*n + 1 := by
  cases bf_run : (bellmanFord (augment edges).ret (Fin.last n)).ret with
  | distances result => exact johnson_time_of_distances edges result bf_run
  | negativeCycle witness => simp [johnson, bf_run] at run

/-- All Johnson executions obey the selected-event bound, including negative-cycle extraction. -/
public theorem johnson_time_le {n : Nat} (edges : List (Edge n)) :
    (johnson edges).time ≤ n^3 + n*edges.length + (n+1)*(edges.length+n) +
      2*n^2 + 4*edges.length + 5*n + 1 + 3*(n+1) := by
  cases bf_run : (bellmanFord (augment edges).ret (Fin.last n)).ret with
  | distances result =>
      rw [johnson_time_of_distances edges result bf_run]
      omega
  | negativeCycle witness =>
      have witness_bound := bellmanFord_cycleWitnessSteps_le (augment edges).ret (Fin.last n)
      have relax_eq := bellmanFord_relaxationChecks_eq_mul (augment edges).ret (Fin.last n)
      rw [augmented_length] at relax_eq
      simp only [johnson, TimeM.time_bind, bf_run, TimeM.time_pure,
        Nat.add_zero, augment_time]
      change edges.length + n +
        ((bellmanFord (augment edges).ret (Fin.last n)).time.relaxationChecks +
          (bellmanFord (augment edges).ret (Fin.last n)).time.cycleWitnessSteps) ≤ _
      rw [relax_eq]
      omega

end Cslib.Algorithms.Lean.Johnson
