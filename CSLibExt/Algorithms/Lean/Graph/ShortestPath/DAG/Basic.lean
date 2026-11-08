/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Basic
public import CSLibExt.Algorithms.Lean.Graph.TopologicalSort
public import Cslib.Algorithms.Lean.TimeM
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Integer shortest paths in topological order

This is the integer-weight milestone of CLRS, fourth edition, Section 22.2,
pages 616-619. It reuses the weighted edge occurrences, paths, and distance
output of Bellman-Ford, but relaxes outgoing edges in one topological pass.
Negative weights and different-weight parallel edges are supported.

The public core requires a complete certified topological order. The total
wrapper uses the existing Kahn sorter and returns its processed/remainder
failure data when the graph contains any cycle, including an unreachable one.

The cost records actual vertex visits, edge-relaxation attempts, and successful
distance installations. Topology, initialization, stable bucketization, vector
access/update, arithmetic and predecessor extraction are uncharged. This is
not the source's full linear running-time theorem. Generic real weights,
deterministic full cost, and longest paths remain separate milestones.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DAGShortestPaths

open BellmanFord

/-- Actual events in the one-pass relaxation, excluding preparation and topology. -/
public structure Cost where
  /-- Vertices taken from the certified order. -/
  vertexVisits : Nat
  /-- Original weighted edge occurrences checked for relaxation. -/
  edgeRelaxations : Nat
  /-- Strict improvements or first finite distances installed. -/
  distanceUpdates : Nat
  deriving DecidableEq, Repr

public instance : Zero Cost := ⟨⟨0, 0, 0⟩⟩

public instance : Add Cost :=
  ⟨fun left right =>
    ⟨left.vertexVisits + right.vertexVisits,
      left.edgeRelaxations + right.edgeRelaxations,
      left.distanceUpdates + right.distanceUpdates⟩⟩

@[simp] private theorem vertexVisits_zero : (0 : Cost).vertexVisits = 0 := rfl
@[simp] private theorem edgeRelaxations_zero : (0 : Cost).edgeRelaxations = 0 := rfl
@[simp] private theorem distanceUpdates_zero : (0 : Cost).distanceUpdates = 0 := rfl
@[simp] private theorem vertexVisits_add (left right : Cost) :
    (left + right).vertexVisits = left.vertexVisits + right.vertexVisits := rfl
@[simp] private theorem edgeRelaxations_add (left right : Cost) :
    (left + right).edgeRelaxations = left.edgeRelaxations + right.edgeRelaxations := rfl
@[simp] private theorem distanceUpdates_add (left right : Cost) :
    (left + right).distanceUpdates = left.distanceUpdates + right.distanceUpdates := rfl

@[no_expose] private def install {n : Nat} (state : Distances n) (edge : Edge n)
    (value : Int) : TimeM Cost (Distances n) := do
  TimeM.tick ⟨0, 0, 1⟩
  pure { state with
    distance := state.distance.set edge.target.val (some value)
    predecessor := state.predecessor.set edge.target.val (some edge) }

@[no_expose] private def relaxEdge {n : Nat} (state : Distances n) (edge : Edge n) :
    TimeM Cost (Distances n) := do
  TimeM.tick ⟨0, 1, 0⟩
  match state.distance.get edge.source with
  | none => pure state
  | some sourceDistance =>
      let value := sourceDistance + edge.weight
      match state.distance.get edge.target with
      | none => install state edge value
      | some previous =>
          if value < previous then install state edge value else pure state

@[no_expose] private def relaxOutgoing {n : Nat} :
    List (Edge n) → Distances n → TimeM Cost (Distances n)
  | [], state => pure state
  | edge :: rest, state => do
      let state ← relaxEdge state edge
      relaxOutgoing rest state

/-- Bucket the original edge occurrences by source in one cons fold followed
by one reverse per bucket, preserving source occurrence order and multiplicity. -/
@[no_expose] private def bucketize {n : Nat} (edges : List (Edge n)) :
    Vector (List (Edge n)) n :=
  (edges.foldl (fun acc edge => acc.set edge.source (edge :: acc.get edge.source))
    (Vector.replicate n [])).map List.reverse

private theorem bucketize_apply {n : Nat} (edges : List (Edge n))
    (acc : Vector (List (Edge n)) n) (vertex : Fin n) :
    (edges.foldl (fun acc edge => acc.set edge.source (edge :: acc.get edge.source))
      acc).get vertex =
      (edges.filter (fun edge => edge.source = vertex)).reverse ++ acc.get vertex := by
  induction edges generalizing acc with
  | nil => simp
  | cons edge rest ih =>
      rw [List.foldl_cons, ih]
      by_cases h : edge.source = vertex
      · subst h
        have hget : (acc.set edge.source (edge :: acc.get edge.source)).get edge.source =
            edge :: acc.get edge.source := by
          show (acc.toArray.set (edge.source : Nat) (edge :: acc.get edge.source)
            (by simpa using edge.source.isLt))[edge.source] = _
          simp [Array.getElem_set_self, Vector.get]
        rw [hget]
        simp [List.filter_cons, List.reverse_cons]
      · have h2 : (edge.source : Nat) ≠ (vertex : Nat) := Fin.val_ne_of_ne h
        have hget : (acc.set edge.source (edge :: acc.get edge.source)).get vertex =
            acc.get vertex := by
          show (acc.toArray.set (edge.source : Nat) (edge :: acc.get edge.source)
            (by simpa using edge.source.isLt))[vertex] = _
          simp [Array.getElem_set, h2, Vector.get]
        rw [hget]
        simp [List.filter_cons, h]

/-- The outgoing bucket preserves the original filtered occurrence list exactly. -/
private theorem bucketize_eq {n : Nat} (edges : List (Edge n)) (vertex : Fin n) :
    (bucketize edges).get vertex =
      (edges.filter (fun edge => edge.source = vertex)) := by
  let raw : Vector (List (Edge n)) n :=
    edges.foldl (fun acc edge => acc.set edge.source (edge :: acc.get edge.source))
      (Vector.replicate n [])
  have hm : (raw.map List.reverse).get vertex = (raw.get vertex).reverse := by
    simp [Vector.get]
  change (raw.map List.reverse).get vertex = _
  rw [hm]
  have h := bucketize_apply edges (Vector.replicate n []) vertex
  change raw.get vertex = _ at h
  rw [h]
  simp [Vector.get]

/-- Adapt completed stable buckets to the canonical directed adjacency API. -/
@[no_expose] private def bucketGraph {n : Nat}
    (buckets : Vector (List (Edge n)) n) : DirectedAdjacency (Fin n) where
  vertices := List.finRange n
  vertices_nodup := List.nodup_finRange n
  vertices_complete := List.mem_finRange
  adjacency vertex := (buckets.get vertex).map Edge.target

/-- Stable buckets retain the canonical adjacency list's order and multiplicity. -/
private theorem bucketGraph_eq {n : Nat} (edges : List (Edge n)) :
    bucketGraph (bucketize edges) = toDirectedAdjacency edges := by
  unfold bucketGraph toDirectedAdjacency
  congr 1
  funext vertex
  rw [bucketize_eq]

private theorem bucketize_subset {n : Nat} (edges : List (Edge n)) (vertex : Fin n) :
    (bucketize edges).get vertex ⊆ edges := by
  rw [bucketize_eq]
  exact fun edge he => List.mem_filter.mp he |>.1

private theorem bucketize_source {n : Nat} (edges : List (Edge n)) (vertex : Fin n)
    (edge : Edge n) (he : edge ∈ (bucketize edges).get vertex) :
    edge.source = vertex := by
  rw [bucketize_eq] at he
  exact of_decide_eq_true (List.mem_filter.mp he).2

private theorem bucketize_length {n : Nat} (edges : List (Edge n)) (vertex : Fin n) :
    ((bucketize edges).get vertex).length =
      (edges.filter (fun edge => edge.source = vertex)).length := by
  rw [bucketize_eq]

private theorem bucketize_mem {n : Nat} (edges : List (Edge n)) (vertex : Fin n)
    (edge : Edge n) (he : edge ∈ edges) (hs : edge.source = vertex) :
    edge ∈ (bucketize edges).get vertex := by
  rw [bucketize_eq]
  exact List.mem_filter.mpr ⟨he, by simp [hs]⟩

@[no_expose] private def pass {n : Nat} (buckets : Fin n → List (Edge n)) :
    List (Fin n) → Distances n → TimeM Cost (Distances n)
  | [], state => pure state
  | vertex :: rest, state => do
      TimeM.tick ⟨1, 0, 0⟩
      let state ← relaxOutgoing (buckets vertex) state
      pass buckets rest state

@[no_expose] private def initialState {n : Nat} (source : Fin n) : Distances n where
  source := source
  distance := Vector.ofFn fun vertex => if vertex = source then some 0 else none
  predecessor := Vector.replicate n none

/-- Execute one outgoing-edge relaxation pass in a certified topological order.
The original edge occurrences are retained, so every parallel occurrence is checked. -/
public def run {n : Nat} (edges : List (Edge n)) (source : Fin n) (order : List (Fin n))
    (_horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    TimeM Cost (Distances n) :=
  let buckets := bucketize edges
  pass (fun vertex => buckets.get vertex) order (initialState source)

/-- Validate topology with Kahn, then run the one-pass integer solver.
Failure preserves the sorter's processed and remaining lists; it does not return a cycle list. -/
public def dagShortestPaths {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    TimeM Cost (Except (List (Fin n) × List (Fin n)) (Distances n)) :=
  let buckets := bucketize edges
  match TopologicalSort.sort (bucketGraph buckets) with
  | .success order => do
      let result ← pass (fun vertex => buckets.get vertex) order (initialState source)
      pure (.ok result)
  | .failure processed remaining => pure (.error (processed, remaining))

private theorem relaxEdge_cost {n : Nat} (state : Distances n) (edge : Edge n) :
    (relaxEdge state edge).time.vertexVisits = 0 ∧
      (relaxEdge state edge).time.edgeRelaxations = 1 ∧
      (relaxEdge state edge).time.distanceUpdates ≤ 1 := by
  cases hs : state.distance.get edge.source with
  | none => simp [relaxEdge, hs]
  | some value =>
      cases ht : state.distance.get edge.target with
      | none => simp [relaxEdge, install, hs, ht]
      | some previous =>
          by_cases hi : value + edge.weight < previous <;>
            simp [relaxEdge, install, hs, ht, hi]

private theorem relaxOutgoing_cost {n : Nat} (outgoing : List (Edge n)) (state : Distances n) :
    (relaxOutgoing outgoing state).time.vertexVisits = 0 ∧
      (relaxOutgoing outgoing state).time.edgeRelaxations = outgoing.length ∧
      (relaxOutgoing outgoing state).time.distanceUpdates ≤ outgoing.length := by
  induction outgoing generalizing state with
  | nil => simp [relaxOutgoing]
  | cons edge rest ih =>
      obtain ⟨hv, he, hu⟩ := relaxEdge_cost state edge
      obtain ⟨hrv, hre, hru⟩ := ih (relaxEdge state edge).ret
      simp only [relaxOutgoing, TimeM.time_bind]
      change (relaxEdge state edge).time.vertexVisits +
            (relaxOutgoing rest (relaxEdge state edge).ret).time.vertexVisits = 0 ∧
          (relaxEdge state edge).time.edgeRelaxations +
            (relaxOutgoing rest (relaxEdge state edge).ret).time.edgeRelaxations =
              (edge :: rest).length ∧
          (relaxEdge state edge).time.distanceUpdates +
            (relaxOutgoing rest (relaxEdge state edge).ret).time.distanceUpdates ≤
              (edge :: rest).length
      simp only [List.length_cons]
      omega

private theorem pass_cost {n : Nat} (buckets : Fin n → List (Edge n)) (order : List (Fin n))
    (state : Distances n) :
    (pass buckets order state).time.vertexVisits = order.length ∧
      (pass buckets order state).time.edgeRelaxations =
        (order.map fun vertex => (buckets vertex).length).sum ∧
      (pass buckets order state).time.distanceUpdates ≤
        (pass buckets order state).time.edgeRelaxations := by
  induction order generalizing state with
  | nil => simp [pass]
  | cons vertex rest ih =>
      let outgoing := buckets vertex
      obtain ⟨hv, he, hu⟩ := relaxOutgoing_cost outgoing state
      obtain ⟨hrv, hre, hru⟩ := ih (relaxOutgoing outgoing state).ret
      simp only [pass, TimeM.time_bind, TimeM.time_tick]
      change 1 + ((relaxOutgoing outgoing state).time.vertexVisits +
            (pass buckets rest (relaxOutgoing outgoing state).ret).time.vertexVisits) =
              (vertex :: rest).length ∧
          0 + ((relaxOutgoing outgoing state).time.edgeRelaxations +
            (pass buckets rest (relaxOutgoing outgoing state).ret).time.edgeRelaxations) =
              ((vertex :: rest).map fun vertex => (buckets vertex).length).sum ∧
          0 + ((relaxOutgoing outgoing state).time.distanceUpdates +
            (pass buckets rest (relaxOutgoing outgoing state).ret).time.distanceUpdates) ≤
          0 + ((relaxOutgoing outgoing state).time.edgeRelaxations +
            (pass buckets rest (relaxOutgoing outgoing state).ret).time.edgeRelaxations)
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      change _ ∧ _ = outgoing.length + _ ∧ _
      omega

/-- The actual outer pass takes each certified vertex once. -/
public theorem run_vertexVisits {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    (run edges source order horder).time.vertexVisits = n := by
  have hp : order.Perm (List.finRange n) :=
    (List.perm_ext_iff_of_nodup horder.1 (List.nodup_finRange n)).mpr horder.2.1
  have hc := (pass_cost (fun vertex => (bucketize edges).get vertex) order
    (initialState source)).1
  simpa [run, hp.length_eq] using hc

private theorem indicator_count {n : Nat} (order : List (Fin n)) (vertex : Fin n) :
    (order.map fun other => if vertex = other then 1 else 0).sum = order.count vertex := by
  induction order with
  | nil => simp
  | cons other rest ih =>
      by_cases hv : other = vertex
      · subst other
        simp [ih, Nat.add_comm]
      · simp [ih, hv, Ne.symm hv]

private theorem outgoing_count {n : Nat} (edges : List (Edge n)) (order : List (Fin n))
    (hn : order.Nodup) (hc : ∀ vertex : Fin n, vertex ∈ order) :
    (order.map fun vertex => (edges.filter fun edge => edge.source = vertex).length).sum =
      edges.length := by
  induction edges with
  | nil => simp
  | cons edge rest ih =>
      have hone : (order.map fun other => if edge.source = other then 1 else 0).sum = 1 := by
        rw [indicator_count]
        simp [hn.count, hc]
      calc
        (order.map fun vertex =>
            ((edge :: rest).filter fun edge => edge.source = vertex).length).sum =
            (order.map fun other => if edge.source = other then 1 else 0).sum +
              (order.map fun vertex =>
                (rest.filter fun edge => edge.source = vertex).length).sum := by
          rw [← List.sum_map_add]
          congr 1
          apply List.map_congr_left
          intro vertex _
          by_cases he : edge.source = vertex <;> simp [he, Nat.add_comm]
        _ = (edge :: rest).length := by rw [hone, ih]; simp [Nat.add_comm]

/-- The executed pass checks every original edge occurrence once, including identical duplicates. -/
public theorem run_edgeRelaxations {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    (run edges source order horder).time.edgeRelaxations = edges.length := by
  change (pass (fun vertex => (bucketize edges).get vertex) order
    (initialState source)).time.edgeRelaxations = edges.length
  rw [(pass_cost (fun vertex => (bucketize edges).get vertex) order
    (initialState source)).2.1]
  have hmap : (order.map fun vertex => ((bucketize edges).get vertex).length) =
      (order.map fun vertex => (edges.filter fun edge => edge.source = vertex).length) :=
    List.map_congr_left fun vertex _ => bucketize_length edges vertex
  rw [hmap]
  exact outgoing_count edges order horder.1
    (fun vertex => (horder.2.1 vertex).mpr (List.mem_finRange vertex))

/-- Only actual strict improvements or first finite estimates install a predecessor. -/
public theorem run_distanceUpdates_le {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    (run edges source order horder).time.distanceUpdates ≤
      (run edges source order horder).time.edgeRelaxations :=
  (pass_cost (fun vertex => (bucketize edges).get vertex) order (initialState source)).2.2

@[simp] private theorem install_distance {n : Nat} (state : Distances n) (edge : Edge n)
    (value : Int) (vertex : Fin n) :
    (install state edge value).ret.distance.get vertex =
      if vertex = edge.target then some value else state.distance.get vertex := by
  change (state.distance.set edge.target.val (some value) edge.target.isLt)[vertex.val] =
    if vertex = edge.target then some value else state.distance[vertex.val]
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff, eq_comm]

@[simp] private theorem install_predecessor {n : Nat} (state : Distances n) (edge : Edge n)
    (value : Int) (vertex : Fin n) :
    (install state edge value).ret.predecessor.get vertex =
      if vertex = edge.target then some edge else state.predecessor.get vertex := by
  change (state.predecessor.set edge.target.val (some edge) edge.target.isLt)[vertex.val] =
    if vertex = edge.target then some edge else state.predecessor[vertex.val]
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff, eq_comm]

@[simp] private theorem initial_distance {n : Nat} (source vertex : Fin n) :
    (initialState source).distance.get vertex = if vertex = source then some 0 else none := by
  change (Vector.ofFn fun v : Fin n => if v = source then some (0 : Int) else none)[vertex.val] = _
  simp

private def Realizes {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (state : Distances n) : Prop :=
  ∀ vertex value, state.distance.get vertex = some value →
    ∃ path, IsWeightedPath edges source vertex path ∧ pathWeight path = value

private theorem initial_realizes {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    Realizes edges source (initialState source) := by
  intro vertex value hd
  by_cases hv : vertex = source
  · subst vertex
    have hd' : (0 : Int) = value := by simpa using hd
    subst value
    exact ⟨[], by simp [IsWeightedPath], by simp [pathWeight]⟩
  · simp [hv] at hd

private theorem install_realizes {n : Nat} {edges : List (Edge n)} {source : Fin n}
    {state : Distances n} (hstate : Realizes edges source state) {edge : Edge n}
    (he : edge ∈ edges) {value : Int} (hd : state.distance.get edge.source = some value) :
    Realizes edges source (install state edge (value + edge.weight)).ret := by
  intro vertex estimate hestimate
  by_cases hv : vertex = edge.target
  · subst vertex
    have hh : value + edge.weight = estimate := by simpa using hestimate
    obtain ⟨path, hp, hw⟩ := hstate edge.source value hd
    refine ⟨path ++ [edge], isWeightedPath_append_edge hp he rfl rfl, ?_⟩
    simpa [pathWeight_append_edge, hw] using hh
  · exact hstate vertex estimate (by simpa [hv] using hestimate)

private theorem relaxEdge_realizes {n : Nat} {edges : List (Edge n)} {source : Fin n}
    {state : Distances n} (hstate : Realizes edges source state) {edge : Edge n}
    (he : edge ∈ edges) : Realizes edges source (relaxEdge state edge).ret := by
  cases hs : state.distance.get edge.source with
  | none => simpa [relaxEdge, hs] using hstate
  | some value =>
      have hi := install_realizes hstate he hs
      cases ht : state.distance.get edge.target with
      | none => simpa [relaxEdge, hs, ht] using hi
      | some previous =>
          by_cases hc : value + edge.weight < previous
          · simpa [relaxEdge, hs, ht, hc] using hi
          · simpa [relaxEdge, hs, ht, hc] using hstate

private theorem relaxOutgoing_realizes {n : Nat} {edges outgoing : List (Edge n)}
    {source : Fin n} {state : Distances n} (hstate : Realizes edges source state)
    (hout : ∀ edge ∈ outgoing, edge ∈ edges) :
    Realizes edges source (relaxOutgoing outgoing state).ret := by
  induction outgoing generalizing state with
  | nil => simpa [relaxOutgoing] using hstate
  | cons edge rest ih =>
      exact ih (relaxEdge_realizes hstate (hout edge (by simp)))
        (fun edge he => hout edge (by simp [he]))

private theorem pass_realizes {n : Nat} {edges : List (Edge n)} {source : Fin n}
    {state : Distances n} (hstate : Realizes edges source state)
    (buckets : Fin n → List (Edge n)) (hbuck : ∀ vertex, buckets vertex ⊆ edges)
    (order : List (Fin n)) :
    Realizes edges source (pass buckets order state).ret := by
  induction order generalizing state with
  | nil => simpa [pass] using hstate
  | cons vertex rest ih =>
      simpa only [pass, TimeM.ret_bind] using
        ih (relaxOutgoing_realizes hstate (fun edge he => hbuck vertex he))

/-- Each finite estimate returned by the executed one-pass solver is realized by an input path. -/
public theorem run_distance_realized {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (target : Fin n) (value : Int)
    (hd : (run edges source order horder).ret.distance.get target = some value) :
    ∃ path, IsWeightedPath edges source target path ∧ pathWeight path = value :=
  pass_realizes (initial_realizes edges source)
    (fun vertex => (bucketize edges).get vertex) (bucketize_subset edges) order target value hd

private theorem edge_forward {n : Nat} {edges : List (Edge n)} {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    {edge : Edge n} (he : edge ∈ edges) : order.idxOf edge.source < order.idxOf edge.target :=
  horder.2.2 _ _ (edge_toDirectedAdjacency_iff.mpr ⟨edge, he, rfl, rfl⟩)

private theorem walk_rank {n : Nat} {edges : List (Edge n)} {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    {length : Nat} {source target : Fin n}
    (hw : (toDirectedAdjacency edges).Walk length source target) :
    order.idxOf source + length ≤ order.idxOf target := by
  induction hw using Relation.RelatesInSteps.head_induction_on with
  | hrefl => simp
  | hhead head _ ih =>
      have hf := horder.2.2 _ _ head
      omega

private theorem finite_edge_target_ne_source {n : Nat} {edges : List (Edge n)}
    {source : Fin n} {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    {state : Distances n} (hstate : Realizes edges source state) {edge : Edge n}
    (he : edge ∈ edges) {value : Int} (hs : state.distance.get edge.source = some value) :
    edge.target ≠ source := by
  obtain ⟨path, hp, _⟩ := hstate edge.source value hs
  have hr := walk_rank horder (isWeightedPath_walk hp)
  have hf := edge_forward horder he
  intro equality
  rw [equality] at hf
  omega

@[simp] private theorem initial_predecessor {n : Nat} (source vertex : Fin n) :
    (initialState source).predecessor.get vertex = none := by
  change (Vector.replicate n (none : Option (Edge n)))[vertex.val] = none
  simp

private structure BasicInvariant {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (state : Distances n) : Prop where
  realizes : Realizes edges source state
  source_field : state.source = source
  source_zero : state.distance.get source = some 0
  source_pred_none : state.predecessor.get source = none
  infinite_pred_none : ∀ vertex, state.distance.get vertex = none →
    state.predecessor.get vertex = none
  finite_pred : ∀ vertex value, state.distance.get vertex = some value → vertex ≠ source →
    ∃ edge, state.predecessor.get vertex = some edge

private theorem initial_basic {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    BasicInvariant edges source (initialState source) where
  realizes := initial_realizes edges source
  source_field := rfl
  source_zero := by simp
  source_pred_none := by simp
  infinite_pred_none := by simp
  finite_pred := by
    intro vertex value hd hv
    simp [hv] at hd

private theorem install_basic {n : Nat} {edges : List (Edge n)} {source : Fin n}
    {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    {state : Distances n} (hstate : BasicInvariant edges source state) {edge : Edge n}
    (he : edge ∈ edges) {value : Int} (hs : state.distance.get edge.source = some value) :
    BasicInvariant edges source (install state edge (value + edge.weight)).ret := by
  have ht := finite_edge_target_ne_source horder hstate.realizes he hs
  refine ⟨install_realizes hstate.realizes he hs, hstate.source_field,
    ?_, ?_, ?_, ?_⟩
  · simpa [Ne.symm ht] using hstate.source_zero
  · simpa [Ne.symm ht] using hstate.source_pred_none
  · intro vertex hd
    by_cases hv : vertex = edge.target
    · simp [hv] at hd
    · have hd' : state.distance.get vertex = none := by simpa [hv] using hd
      simpa [hv] using hstate.infinite_pred_none vertex hd'
  · intro vertex estimate hd hvsource
    by_cases hv : vertex = edge.target
    · exact ⟨edge, by simp [hv]⟩
    · obtain ⟨previous, hp⟩ := hstate.finite_pred vertex estimate
        (by simpa [hv] using hd) hvsource
      exact ⟨previous, by simpa [hv] using hp⟩

private theorem relaxEdge_basic {n : Nat} {edges : List (Edge n)} {source : Fin n}
    {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    {state : Distances n} (hstate : BasicInvariant edges source state) {edge : Edge n}
    (he : edge ∈ edges) : BasicInvariant edges source (relaxEdge state edge).ret := by
  cases hs : state.distance.get edge.source with
  | none => simpa [relaxEdge, hs] using hstate
  | some value =>
      have hi := install_basic horder hstate he hs
      cases ht : state.distance.get edge.target with
      | none => simpa [relaxEdge, hs, ht] using hi
      | some previous =>
          by_cases hc : value + edge.weight < previous
          · simpa [relaxEdge, hs, ht, hc] using hi
          · simpa [relaxEdge, hs, ht, hc] using hstate

private theorem relaxOutgoing_basic {n : Nat} {edges outgoing : List (Edge n)}
    {source : Fin n} {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    {state : Distances n} (hstate : BasicInvariant edges source state)
    (hout : ∀ edge ∈ outgoing, edge ∈ edges) :
    BasicInvariant edges source (relaxOutgoing outgoing state).ret := by
  induction outgoing generalizing state with
  | nil => simpa [relaxOutgoing] using hstate
  | cons edge rest ih =>
      exact ih (relaxEdge_basic horder hstate (hout edge (by simp)))
        (fun edge he => hout edge (by simp [he]))

private theorem pass_basic {n : Nat} {edges : List (Edge n)} {source : Fin n}
    {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    {state : Distances n} (hstate : BasicInvariant edges source state)
    (buckets : Fin n → List (Edge n)) (hbuck : ∀ vertex, buckets vertex ⊆ edges)
    (remaining : List (Fin n)) :
    BasicInvariant edges source (pass buckets remaining state).ret := by
  induction remaining generalizing state with
  | nil => simpa [pass] using hstate
  | cons vertex rest ih =>
      simpa only [pass, TimeM.ret_bind] using
        ih (relaxOutgoing_basic horder hstate (fun edge he => hbuck vertex he))

private theorem run_basic {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    BasicInvariant edges source (run edges source order horder).ret :=
  pass_basic horder (initial_basic edges source)
    (fun vertex => (bucketize edges).get vertex) (bucketize_subset edges) order

/-- The executed result retains the selected source. -/
public theorem run_source {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    (run edges source order horder).ret.source = source :=
  (run_basic edges source order horder).source_field

/-- In a DAG the empty source path stays at zero, even with incoming negative edges. -/
public theorem run_source_distance {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    (run edges source order horder).ret.distance.get source = some 0 :=
  (run_basic edges source order horder).source_zero

/-- The source is the root of the resulting predecessor structure. -/
public theorem run_source_predecessor {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    (run edges source order horder).ret.predecessor.get source = none :=
  (run_basic edges source order horder).source_pred_none

private theorem relaxEdge_cases {n : Nat} (state : Distances n) (edge : Edge n) :
    (relaxEdge state edge).ret = state ∨
      ∃ value, state.distance.get edge.source = some value ∧
        (∀ previous, state.distance.get edge.target = some previous →
          value + edge.weight < previous) ∧
        (relaxEdge state edge).ret = (install state edge (value + edge.weight)).ret := by
  cases hs : state.distance.get edge.source with
  | none => exact Or.inl (by simp [relaxEdge, hs])
  | some value =>
      cases ht : state.distance.get edge.target with
      | none =>
          exact Or.inr ⟨value, rfl, by simp, by simp [relaxEdge, hs, ht]⟩
      | some previous =>
          by_cases hi : value + edge.weight < previous
          · refine Or.inr ⟨value, rfl, ?_, by simp [relaxEdge, hs, ht, hi]⟩
            intro other ho
            have equality : previous = other := by simpa [ht] using ho
            simpa [← equality] using hi
          · exact Or.inl (by simp [relaxEdge, hs, ht, hi])

private theorem relaxEdge_distance_fixed {n : Nat} (state : Distances n) (edge : Edge n)
    (vertex : Fin n) (hv : vertex ≠ edge.target) :
    (relaxEdge state edge).ret.distance.get vertex = state.distance.get vertex := by
  rcases relaxEdge_cases state edge with unchanged | ⟨value, _, _, installed⟩
  · rw [unchanged]
  · rw [installed]
    simp [hv]

private theorem relaxEdge_nonincreasing {n : Nat} (state : Distances n) (edge : Edge n)
    (vertex : Fin n) (previous : Int) (hp : state.distance.get vertex = some previous) :
    ∃ value, (relaxEdge state edge).ret.distance.get vertex = some value ∧ value ≤ previous := by
  rcases relaxEdge_cases state edge with unchanged | ⟨value, _, better, installed⟩
  · exact ⟨previous, by simpa [unchanged] using hp, le_rfl⟩
  · by_cases hv : vertex = edge.target
    · subst vertex
      exact ⟨value + edge.weight, by simp [installed], le_of_lt (better previous hp)⟩
    · exact ⟨previous, by simpa [installed, hv] using hp, le_rfl⟩

private def EdgeBound {n : Nat} (state : Distances n) (edge : Edge n) : Prop :=
  ∀ sourceValue, state.distance.get edge.source = some sourceValue →
    ∃ targetValue, state.distance.get edge.target = some targetValue ∧
      targetValue ≤ sourceValue + edge.weight

private theorem relaxEdge_bound {n : Nat} (state : Distances n) (edge : Edge n)
    (hne : edge.source ≠ edge.target) : EdgeBound (relaxEdge state edge).ret edge := by
  intro value hv
  have hs : state.distance.get edge.source = some value := by
    simpa [relaxEdge_distance_fixed state edge edge.source hne] using hv
  cases ht : state.distance.get edge.target with
  | none => exact ⟨value + edge.weight, by simp [relaxEdge, hs, ht], le_rfl⟩
  | some previous =>
      by_cases hi : value + edge.weight < previous
      · exact ⟨value + edge.weight, by simp [relaxEdge, hs, ht, hi], le_rfl⟩
      · exact ⟨previous, by simp [relaxEdge, hs, ht, hi], by omega⟩

private theorem relaxEdge_preserves_bound {n : Nat} (state : Distances n)
    (edge checked : Edge n) (hne : checked.source ≠ edge.target)
    (hb : EdgeBound state checked) : EdgeBound (relaxEdge state edge).ret checked := by
  intro value hs
  have hs' : state.distance.get checked.source = some value := by
    simpa [relaxEdge_distance_fixed state edge checked.source hne] using hs
  obtain ⟨old, hold, hbound⟩ := hb value hs'
  obtain ⟨new, hnew, hle⟩ := relaxEdge_nonincreasing state edge checked.target old hold
  exact ⟨new, hnew, le_trans hle hbound⟩

private theorem relaxOutgoing_preserves_bound {n : Nat} (outgoing : List (Edge n))
    (state : Distances n) (checked : Edge n)
    (hne : ∀ edge ∈ outgoing, checked.source ≠ edge.target)
    (hb : EdgeBound state checked) : EdgeBound (relaxOutgoing outgoing state).ret checked := by
  induction outgoing generalizing state with
  | nil => simpa [relaxOutgoing] using hb
  | cons edge rest ih =>
      exact ih (relaxEdge state edge).ret
        (fun edge he => hne edge (by simp [he]))
        (relaxEdge_preserves_bound state edge checked (hne edge (by simp)) hb)

private theorem relaxOutgoing_checked {n : Nat} (outgoing : List (Edge n))
    (state : Distances n)
    (hne : ∀ left ∈ outgoing, ∀ right ∈ outgoing, left.source ≠ right.target) :
    ∀ checked ∈ outgoing, EdgeBound (relaxOutgoing outgoing state).ret checked := by
  induction outgoing generalizing state with
  | nil => simp
  | cons edge rest ih =>
      intro checked hc
      rcases List.mem_cons.mp hc with equal | later
      · subst checked
        exact relaxOutgoing_preserves_bound rest (relaxEdge state edge).ret edge
          (fun other ho => hne edge (by simp) other (by simp [ho]))
          (relaxEdge_bound state edge (hne edge (by simp) edge (by simp)))
      · exact ih (relaxEdge state edge).ret
          (fun left hl right hr => hne left (by simp [hl]) right (by simp [hr])) checked later

private def Predecessors {n : Nat} (edges : List (Edge n)) (order : List (Fin n))
    (cutoff : Nat) (state : Distances n) : Prop :=
  ∀ vertex edge, state.predecessor.get vertex = some edge →
    edge ∈ edges ∧ edge.target = vertex ∧
      ∃ value, state.distance.get edge.source = some value ∧
        state.distance.get vertex = some (value + edge.weight) ∧
        order.idxOf edge.source < cutoff

private theorem predecessors_weaken {n : Nat} {edges : List (Edge n)}
    {order : List (Fin n)} {old new : Nat} {state : Distances n}
    (hstate : Predecessors edges order old state) (hle : old ≤ new) :
    Predecessors edges order new state := by
  intro vertex edge hp
  obtain ⟨he, ht, value, hs, hd, hr⟩ := hstate vertex edge hp
  exact ⟨he, ht, value, hs, hd, lt_of_lt_of_le hr hle⟩

private theorem install_predecessors {n : Nat} {edges : List (Edge n)}
    {order : List (Fin n)} {cutoff : Nat} {state : Distances n}
    (hstate : Predecessors edges order cutoff state) {edge : Edge n}
    (he : edge ∈ edges) (hsr : order.idxOf edge.source < cutoff)
    (htr : cutoff ≤ order.idxOf edge.target) {value : Int}
    (hs : state.distance.get edge.source = some value) :
    Predecessors edges order cutoff (install state edge (value + edge.weight)).ret := by
  intro vertex predecessor hp
  by_cases hv : vertex = edge.target
  · subst vertex
    have equality : edge = predecessor := by simpa using hp
    subst predecessor
    have hne : edge.source ≠ edge.target := by
      intro equality
      rw [equality] at hsr
      omega
    exact ⟨he, rfl, value, by simpa [hne] using hs, by simp, hsr⟩
  · have hp' : state.predecessor.get vertex = some predecessor := by simpa [hv] using hp
    obtain ⟨hm, ht, previous, hsource, hd, hr⟩ := hstate vertex predecessor hp'
    have hne : predecessor.source ≠ edge.target := by
      intro equality
      rw [equality] at hr
      omega
    exact ⟨hm, ht, previous, by simpa [hne] using hsource, by simpa [hv] using hd, hr⟩

private theorem relaxEdge_predecessors {n : Nat} {edges : List (Edge n)}
    {order : List (Fin n)} {cutoff : Nat} {state : Distances n}
    (hstate : Predecessors edges order cutoff state) {edge : Edge n}
    (he : edge ∈ edges) (hsr : order.idxOf edge.source < cutoff)
    (htr : cutoff ≤ order.idxOf edge.target) :
    Predecessors edges order cutoff (relaxEdge state edge).ret := by
  rcases relaxEdge_cases state edge with unchanged | ⟨value, hs, _, installed⟩
  · simpa [unchanged] using hstate
  · simpa [installed] using install_predecessors hstate he hsr htr hs

private theorem relaxOutgoing_predecessors {n : Nat} {edges outgoing : List (Edge n)}
    {order : List (Fin n)} {cutoff : Nat} {state : Distances n}
    (hstate : Predecessors edges order cutoff state)
    (hout : ∀ edge ∈ outgoing,
      edge ∈ edges ∧ order.idxOf edge.source < cutoff ∧ cutoff ≤ order.idxOf edge.target) :
    Predecessors edges order cutoff (relaxOutgoing outgoing state).ret := by
  induction outgoing generalizing state with
  | nil => simpa [relaxOutgoing] using hstate
  | cons edge rest ih =>
      obtain ⟨he, hsr, htr⟩ := hout edge (by simp)
      exact ih (relaxEdge_predecessors hstate he hsr htr)
        (fun edge he => hout edge (by simp [he]))

private theorem order_mem {n : Nat} {edges : List (Edge n)} {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (vertex : Fin n) : vertex ∈ order :=
  (horder.2.1 vertex).mpr (List.mem_finRange vertex)

private theorem order_length {n : Nat} {edges : List (Edge n)} {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    order.length = n := by
  have hp : order.Perm (List.finRange n) :=
    (List.perm_ext_iff_of_nodup horder.1 (List.nodup_finRange n)).mpr horder.2.1
  simpa using hp.length_eq

private theorem order_rank_injective {n : Nat} {edges : List (Edge n)} {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    {left right : Fin n} (heq : order.idxOf left = order.idxOf right) : left = right := by
  have hleft := List.idxOf_lt_length_of_mem (order_mem horder left)
  have hright := List.idxOf_lt_length_of_mem (order_mem horder right)
  have hl := List.getElem_idxOf hleft
  have hr := List.getElem_idxOf hright
  calc
    left = order[order.idxOf left] := hl.symm
    _ = order[order.idxOf right] := by simp only [heq]
    _ = right := hr

private theorem head_rank {n : Nat} {edges : List (Edge n)} {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (processed : List (Fin n)) (vertex : Fin n) (rest : List (Fin n))
    (hsplit : order = processed ++ vertex :: rest) : order.idxOf vertex = processed.length := by
  have hn : (processed ++ vertex :: rest).Nodup := by simpa [hsplit] using horder.1
  have hv : vertex ∉ processed := fun hm =>
    (List.nodup_append.mp hn).2.2 vertex hm vertex (by simp) rfl
  rw [hsplit, List.idxOf_append]
  simp [hv]

private structure LoopInvariant {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n)) (cutoff : Nat) (state : Distances n) : Prop where
  basic : BasicInvariant edges source state
  predecessors : Predecessors edges order cutoff state
  bounded : ∀ edge ∈ edges, order.idxOf edge.source < cutoff → EdgeBound state edge

private theorem initial_loop {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n)) : LoopInvariant edges source order 0 (initialState source) where
  basic := initial_basic edges source
  predecessors := by intro vertex edge hp; simp at hp
  bounded := by intro edge _ hr; omega

private theorem advance_loop {n : Nat} {edges : List (Edge n)} {source : Fin n}
    {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (processed : List (Fin n)) (vertex : Fin n) (rest : List (Fin n))
    (hsplit : order = processed ++ vertex :: rest) {state : Distances n}
    (hstate : LoopInvariant edges source order processed.length state)
    (outgoing : List (Edge n))
    (hout : ∀ edge ∈ outgoing, edge ∈ edges ∧ edge.source = vertex)
    (houteq : ∀ edge ∈ edges, edge.source = vertex → edge ∈ outgoing) :
    LoopInvariant edges source order (processed.length + 1)
      (relaxOutgoing outgoing state).ret := by
  have hpos := head_rank horder processed vertex rest hsplit
  have htargets : ∀ edge ∈ outgoing, processed.length < order.idxOf edge.target := by
    intro edge he
    have hf := edge_forward horder (hout edge he).1
    simpa [(hout edge he).2, hpos] using hf
  have hcross : ∀ left ∈ outgoing, ∀ right ∈ outgoing, left.source ≠ right.target := by
    intro left hl right hr equality
    have hleft : order.idxOf left.source = processed.length := by rw [(hout left hl).2, hpos]
    have hright := htargets right hr
    rw [equality] at hleft
    omega
  refine ⟨relaxOutgoing_basic horder hstate.basic (fun edge he => (hout edge he).1), ?_, ?_⟩
  · apply relaxOutgoing_predecessors (predecessors_weaken hstate.predecessors (by omega))
    intro edge he
    have hsource : order.idxOf edge.source = processed.length := by rw [(hout edge he).2, hpos]
    have htarget := htargets edge he
    exact ⟨(hout edge he).1, by omega, by omega⟩
  · intro edge he hr
    by_cases hearlier : order.idxOf edge.source < processed.length
    · apply relaxOutgoing_preserves_bound outgoing state edge
        ?_ (hstate.bounded edge he hearlier)
      intro other ho equality
      have ht := htargets other ho
      rw [equality] at hearlier
      omega
    · have heq : order.idxOf edge.source = order.idxOf vertex := by omega
      have hsource := order_rank_injective horder heq
      apply relaxOutgoing_checked outgoing state hcross edge
        (houteq edge he hsource)

private theorem pass_loop {n : Nat} {edges : List (Edge n)} {source : Fin n}
    {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (buckets : Fin n → List (Edge n))
    (hbuck : ∀ vertex edge, edge ∈ buckets vertex → edge ∈ edges ∧ edge.source = vertex)
    (hbuckmem : ∀ vertex edge, edge ∈ edges → edge.source = vertex → edge ∈ buckets vertex)
    (processed remaining : List (Fin n)) (hsplit : order = processed ++ remaining)
    (state : Distances n) (hstate : LoopInvariant edges source order processed.length state) :
    LoopInvariant edges source order order.length (pass buckets remaining state).ret := by
  induction remaining generalizing processed state with
  | nil => simpa [pass, hsplit] using hstate
  | cons vertex rest ih =>
      have hs : order = (processed ++ [vertex]) ++ rest := by simpa [List.append_assoc] using hsplit
      have hn := advance_loop horder processed vertex rest hsplit hstate (buckets vertex)
        (hbuck vertex) (hbuckmem vertex)
      have hlen : (processed ++ [vertex]).length = processed.length + 1 := by
        simp
      simpa only [pass, TimeM.ret_bind] using
        ih (processed ++ [vertex]) hs _ (hlen ▸ hn)

private theorem run_loop {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    LoopInvariant edges source order order.length (run edges source order horder).ret :=
  pass_loop horder (fun vertex => (bucketize edges).get vertex)
    (fun vertex edge he =>
      ⟨bucketize_subset edges vertex he, bucketize_source edges vertex edge he⟩)
    (fun vertex edge he hs => bucketize_mem edges vertex edge he hs)
    [] order (by simp) (initialState source)
    (initial_loop edges source order)

private theorem path_bound {n : Nat} {edges : List (Edge n)} {state : Distances n}
    (hb : ∀ edge ∈ edges, EdgeBound state edge) {source target : Fin n}
    {path : List (Edge n)} (hp : IsWeightedPath edges source target path)
    {value : Int} (hs : state.distance.get source = some value) :
    ∃ estimate, state.distance.get target = some estimate ∧ estimate ≤ value + pathWeight path := by
  induction path generalizing source value with
  | nil =>
      have heq : source = target := hp.2.2
      exact ⟨value, by simpa [heq] using hs, by simp [pathWeight]⟩
  | cons first rest ih =>
      have he := hp.1 first (by simp)
      have hsource : first.source = source := hp.2.2.1
      obtain ⟨middle, hm, hmiddle⟩ := hb first he value (by simpa [hsource] using hs)
      obtain ⟨estimate, ht, hrest⟩ := ih (isWeightedPath_tail hp) hm
      refine ⟨estimate, ht, ?_⟩
      have hw : pathWeight (first :: rest) = first.weight + pathWeight rest := by simp [pathWeight]
      rw [hw]
      omega

private theorem run_edges_bounded {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    ∀ edge ∈ edges, EdgeBound (run edges source order horder).ret edge := by
  intro edge he
  exact (run_loop edges source order horder).bounded edge he
    (List.idxOf_lt_length_of_mem (order_mem horder edge.source))

private theorem run_path_bound {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (target : Fin n) (path : List (Edge n)) (hp : IsWeightedPath edges source target path) :
    ∃ value, (run edges source order horder).ret.distance.get target = some value ∧
      value ≤ pathWeight path := by
  simpa using path_bound (run_edges_bounded edges source order horder) hp
    (run_source_distance edges source order horder)

/-- The computed estimate is no greater than the weight of any concrete input path. -/
public theorem run_distance_minimal {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (target : Fin n) (value : Int)
    (hd : (run edges source order horder).ret.distance.get target = some value)
    (path : List (Edge n)) (hp : IsWeightedPath edges source target path) :
    value ≤ pathWeight path := by
  obtain ⟨estimate, he, hbound⟩ := run_path_bound edges source order horder target path hp
  have equality : estimate = value := Option.some.inj (he.symm.trans hd)
  simpa [equality] using hbound

/-- Infinity is exactly absence of a path in the canonical weight-forgetting graph. -/
public theorem run_distance_eq_none_iff {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (target : Fin n) :
    (run edges source order horder).ret.distance.get target = none ↔
      ¬(toDirectedAdjacency edges).Reachable source target := by
  constructor
  · intro infinite reachable
    obtain ⟨path, hp⟩ := reachable_iff_exists_isWeightedPath.mp reachable
    obtain ⟨value, hd, _⟩ := run_path_bound edges source order horder target path hp
    rw [infinite] at hd
    contradiction
  · intro unreachable
    cases hd : (run edges source order horder).ret.distance.get target with
    | none => rfl
    | some value =>
        obtain ⟨path, hp, _⟩ := run_distance_realized edges source order horder target value hd
        exact False.elim (unreachable (reachable_iff_exists_isWeightedPath.mpr ⟨path, hp⟩))

/-- Every final predecessor is an input edge with a settled source and its exact weight equation. -/
public theorem run_predecessor_spec {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (target : Fin n) (edge : Edge n)
    (hp : (run edges source order horder).ret.predecessor.get target = some edge) :
    edge ∈ edges ∧ edge.target = target ∧
      ∃ value, (run edges source order horder).ret.distance.get edge.source = some value ∧
        (run edges source order horder).ret.distance.get target = some (value + edge.weight) ∧
        order.idxOf edge.source < order.idxOf target := by
  obtain ⟨he, ht, value, hs, hd, _⟩ :=
    (run_loop edges source order horder).predecessors target edge hp
  exact ⟨he, ht, value, hs, hd, by simpa [ht] using edge_forward horder he⟩

/-- An infinite estimate has no installed predecessor. -/
public theorem run_infinite_predecessor {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (target : Fin n) (hd : (run edges source order horder).ret.distance.get target = none) :
    (run edges source order horder).ret.predecessor.get target = none :=
  (run_basic edges source order horder).infinite_pred_none target hd

/-- Each finite non-source vertex has an installed predecessor edge. -/
public theorem run_finite_predecessor {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order)
    (target : Fin n) (value : Int)
    (hd : (run edges source order horder).ret.distance.get target = some value)
    (hne : target ≠ source) : ∃ edge, (run edges source order horder).ret.predecessor.get target =
      some edge := (run_basic edges source order horder).finite_pred target value hd hne

/-- A successful validated-wrapper output is exactly the actual pass in its certified order. -/
public theorem dagShortestPaths_eq_ok_iff {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (result : Distances n) :
    (dagShortestPaths edges source).ret = .ok result ↔
      ∃ order, ∃ horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order,
        TopologicalSort.sort (toDirectedAdjacency edges) = .success order ∧
        result = (run edges source order horder).ret := by
  unfold dagShortestPaths
  dsimp only
  rw [bucketGraph_eq]
  split
  · rename_i order hs
    constructor
    · intro returns
      refine ⟨order, TopologicalSort.success_isTopologicalOrder _ _ hs, hs, ?_⟩
      exact (Except.ok.inj returns).symm
    · rintro ⟨other, horder, ho, rfl⟩
      have equality : other = order := TopologicalSort.Result.success.inj (ho.symm.trans hs)
      subst other
      rfl
  · rename_i processed remaining hs
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨order, _, ho, _⟩
      have impossible := hs.symm.trans ho
      cases impossible

/-- The wrapper relays exactly the sorter's processed/remainder failure data. -/
public theorem dagShortestPaths_eq_error_iff {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (processed remaining : List (Fin n)) :
    (dagShortestPaths edges source).ret = .error (processed, remaining) ↔
      TopologicalSort.sort (toDirectedAdjacency edges) = .failure processed remaining := by
  unfold dagShortestPaths
  dsimp only
  rw [bucketGraph_eq]
  split
  · rename_i order hs
    simp [hs]
  · rename_i processed' remaining' hs
    simp [hs]

end Cslib.Algorithms.Lean.DAGShortestPaths
