/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Pigeonhole
public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Range
public import Mathlib.Data.Vector.Basic

/-!
# Bellman-Ford shortest paths

This module implements Bellman-Ford over an ordered list of integer-weighted directed edge
occurrences. It returns either exact shortest-path data or a concrete reachable negative cycle.

The algorithm and its correctness specification follow Cormen, Leiserson, Rivest, and Stein,
*Introduction to Algorithms*, fourth edition, Section 22.1 and Exercise 22.1-7.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BellmanFord

namespace Internal

theorem iterate_fin_has_earlier {n : Nat} (f : Fin n → Fin n) (x : Fin n) :
    ∃ step, step < n ∧ (f^[step]) x = (f^[n]) x := by
  obtain ⟨i, j, different, equal⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (n + 1) ↦ (f^[i.val]) x) (by simp)
  have values_different : i.val ≠ j.val := by
    intro values_equal
    exact different (Fin.ext values_equal)
  rcases lt_or_gt_of_ne values_different with before | before
  · refine ⟨i.val + n - j.val, by omega, ?_⟩
    have mapped := congrArg (fun value ↦ (f^[n - j.val]) value) equal
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at mapped
    have exponent_left : n - j.val + i.val = i.val + n - j.val := by omega
    have exponent_right : n - j.val + j.val = n := by omega
    rwa [exponent_left, exponent_right] at mapped
  · refine ⟨j.val + n - i.val, by omega, ?_⟩
    have mapped := congrArg (fun value ↦ (f^[n - i.val]) value) equal.symm
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at mapped
    have exponent_left : n - i.val + j.val = j.val + n - i.val := by omega
    have exponent_right : n - i.val + i.val = n := by omega
    rwa [exponent_left, exponent_right] at mapped

end Internal

/-- One occurrence in a weighted directed edge list. -/
public structure Edge (n : Nat) where
  /-- The source vertex. -/
  source : Fin n
  /-- The target vertex. -/
  target : Fin n
  /-- The integer edge weight. -/
  weight : Int
deriving DecidableEq

/-- Forget weights while preserving edge-list order and multiplicity. -/
@[expose] public def toDirectedAdjacency {n : Nat}
    (edges : List (Edge n)) : DirectedAdjacency (Fin n) where
  vertices := List.finRange n
  vertices_nodup := List.nodup_finRange n
  vertices_complete := List.mem_finRange
  adjacency source :=
    (edges.filter fun edge => decide (edge.source = source)).map Edge.target

/-- The vertices visited by a path represented by forward edge occurrences. -/
@[expose] public def pathVertices {n : Nat}
    (source : Fin n) (path : List (Edge n)) : List (Fin n) :=
  source :: path.map Edge.target

/-- Sum the integer weights of concrete edge occurrences. -/
@[expose] public def pathWeight {n : Nat} (path : List (Edge n)) : Int :=
  (path.map Edge.weight).sum

/-- A concrete edge list is a source-to-target path in the input edge list. -/
@[expose] public def IsWeightedPath {n : Nat} (edges : List (Edge n)) (source target : Fin n)
    (path : List (Edge n)) : Prop :=
  (∀ edge ∈ path, edge ∈ edges) ∧
    path.IsChain (fun left right => left.target = right.source) ∧
    match path with
    | [] => source = target
    | first :: rest =>
        first.source = source ∧ (first :: rest).getLast?.map Edge.target = some target

/-- The weight-forgetting graph contains exactly the endpoint pairs of input edges. -/
public theorem edge_toDirectedAdjacency_iff {n : Nat} {edges : List (Edge n)} {u v : Fin n} :
    (toDirectedAdjacency edges).Edge u v ↔
      ∃ edge, edge ∈ edges ∧ edge.source = u ∧ edge.target = v := by
  simp only [toDirectedAdjacency, DirectedAdjacency.Edge, List.mem_map, List.mem_filter,
    decide_eq_true_eq, and_assoc]

namespace Internal

theorem isWeightedPath_cons {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {first : Edge n} {rest : List (Edge n)}
    (first_mem : first ∈ edges) (first_source : first.source = source)
    (rest_path : IsWeightedPath edges first.target target rest) :
    IsWeightedPath edges source target (first :: rest) := by
  cases rest <;> simp_all [IsWeightedPath]

theorem isWeightedPath_tail {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {first : Edge n} {rest : List (Edge n)}
    (path : IsWeightedPath edges source target (first :: rest)) :
    IsWeightedPath edges first.target target rest := by
  cases rest <;> simp_all [IsWeightedPath]

theorem walk_exists_isWeightedPath {n length : Nat} {edges : List (Edge n)}
    {source target : Fin n}
    (walk : (toDirectedAdjacency edges).Walk length source target) :
    ∃ path, IsWeightedPath edges source target path := by
  induction walk using Relation.RelatesInSteps.head_induction_on with
  | hrefl =>
      exact ⟨[], by simp [IsWeightedPath]⟩
  | hhead head _ induction =>
      obtain ⟨edge, edge_mem, edge_source, edge_target⟩ :=
        edge_toDirectedAdjacency_iff.mp head
      obtain ⟨path, path_valid⟩ := induction
      have rest_valid : IsWeightedPath edges edge.target target path := by
        simpa [edge_target] using path_valid
      exact ⟨edge :: path, isWeightedPath_cons edge_mem edge_source rest_valid⟩

theorem isWeightedPath_walk {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {path : List (Edge n)}
    (path_valid : IsWeightedPath edges source target path) :
    (toDirectedAdjacency edges).Walk path.length source target := by
  induction path generalizing source with
  | nil =>
      simp [path_valid.2.2]
  | cons first rest induction =>
      have first_mem : first ∈ edges := path_valid.1 first (by simp)
      have first_source : first.source = source := path_valid.2.2.1
      have first_edge : (toDirectedAdjacency edges).Edge source first.target :=
        edge_toDirectedAdjacency_iff.mpr ⟨first, first_mem, first_source, rfl⟩
      exact Relation.RelatesInSteps.head source first.target target rest.length first_edge
        (induction (isWeightedPath_tail path_valid))

theorem isWeightedPath_append_edge {n : Nat} {edges : List (Edge n)}
    {source middle target : Fin n} {path : List (Edge n)} {edge : Edge n}
    (path_valid : IsWeightedPath edges source middle path)
    (edge_mem : edge ∈ edges) (edge_source : edge.source = middle)
    (edge_target : edge.target = target) :
    IsWeightedPath edges source target (path ++ [edge]) := by
  induction path generalizing source with
  | nil =>
      have source_middle : source = middle := path_valid.2.2
      exact isWeightedPath_cons edge_mem (edge_source.trans source_middle.symm)
        (by simp [IsWeightedPath, edge_target])
  | cons first rest induction =>
      have first_mem : first ∈ edges := path_valid.1 first (by simp)
      have first_source : first.source = source := path_valid.2.2.1
      exact isWeightedPath_cons first_mem first_source
        (induction (isWeightedPath_tail path_valid))

theorem isWeightedPath_append_edge_iff {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {path : List (Edge n)} {edge : Edge n} :
    IsWeightedPath edges source target (path ++ [edge]) ↔
      IsWeightedPath edges source edge.source path ∧ edge ∈ edges ∧
        edge.target = target := by
  induction path generalizing source with
  | nil =>
      constructor
      · intro valid
        have fields : edge ∈ edges ∧ edge.source = source ∧ edge.target = target := by
          simpa [IsWeightedPath] using valid
        exact ⟨by simpa [IsWeightedPath] using fields.2.1.symm, fields.1, fields.2.2⟩
      · rintro ⟨empty_valid, edge_mem, edge_target⟩
        have source_eq : source = edge.source := by
          simpa [IsWeightedPath] using empty_valid
        simpa [IsWeightedPath] using And.intro edge_mem (And.intro source_eq.symm edge_target)
  | cons first rest induction =>
      constructor
      · intro valid
        obtain ⟨rest_valid, edge_mem, edge_target⟩ :=
          induction.mp (isWeightedPath_tail valid)
        exact ⟨isWeightedPath_cons (valid.1 first (by simp)) valid.2.2.1 rest_valid,
          edge_mem, edge_target⟩
      · rintro ⟨prefix_valid, edge_mem, edge_target⟩
        apply isWeightedPath_cons (prefix_valid.1 first (by simp)) prefix_valid.2.2.1
        exact induction.mpr ⟨isWeightedPath_tail prefix_valid, edge_mem, edge_target⟩

theorem pathWeight_append_edge {n : Nat} (path : List (Edge n)) (edge : Edge n) :
    pathWeight (path ++ [edge]) = pathWeight path + edge.weight := by
  simp [pathWeight]

end Internal

open Internal

/-- Removing the first edge leaves a weighted path from that edge's target. -/
public theorem isWeightedPath_tail {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {first : Edge n} {rest : List (Edge n)}
    (path : IsWeightedPath edges source target (first :: rest)) :
    IsWeightedPath edges first.target target rest :=
  Internal.isWeightedPath_tail path

/-- Append an input edge whose source is the endpoint of a weighted path. -/
public theorem isWeightedPath_append_edge {n : Nat} {edges : List (Edge n)}
    {source middle target : Fin n} {path : List (Edge n)} {edge : Edge n}
    (path_valid : IsWeightedPath edges source middle path)
    (edge_mem : edge ∈ edges) (edge_source : edge.source = middle)
    (edge_target : edge.target = target) :
    IsWeightedPath edges source target (path ++ [edge]) :=
  Internal.isWeightedPath_append_edge path_valid edge_mem edge_source edge_target

/-- Appending one edge adds exactly its integer weight. -/
public theorem pathWeight_append_edge {n : Nat} (path : List (Edge n)) (edge : Edge n) :
    pathWeight (path ++ [edge]) = pathWeight path + edge.weight :=
  Internal.pathWeight_append_edge path edge

/-- A concrete weighted path gives the canonical walk of the same edge length. -/
public theorem isWeightedPath_walk {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {path : List (Edge n)}
    (path_valid : IsWeightedPath edges source target path) :
    (toDirectedAdjacency edges).Walk path.length source target :=
  Internal.isWeightedPath_walk path_valid

/-- Weighted edge-list paths characterize reachability in the weight-forgetting graph. -/
public theorem reachable_iff_exists_isWeightedPath {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} :
    (toDirectedAdjacency edges).Reachable source target ↔
      ∃ path, IsWeightedPath edges source target path := by
  constructor
  · intro reachable
    obtain ⟨_, walk⟩ := DirectedAdjacency.reachable_iff_exists_walk.mp reachable
    exact walk_exists_isWeightedPath walk
  · rintro ⟨path, path_valid⟩
    rw [DirectedAdjacency.reachable_iff_exists_walk]
    exact ⟨path.length, isWeightedPath_walk path_valid⟩

/-- A concrete simple negative cycle plus a concrete path from the source to its base. -/
public structure ReachableNegativeCycle {n : Nat} (edges : List (Edge n)) (source : Fin n) where
  /-- The distinguished cycle vertex reached by the prefix. -/
  base : Fin n
  /-- A source-to-base path. -/
  «prefix» : List (Edge n)
  /-- A nonempty closed path based at `base`. -/
  cycle : List (Edge n)
  /-- The prefix uses input edges and has the declared endpoints. -/
  prefix_valid : IsWeightedPath edges source base «prefix»
  /-- The prefix visits no vertex twice. -/
  prefix_simple : (pathVertices source «prefix»).Nodup
  /-- The cycle uses input edges and closes at `base`. -/
  cycle_valid : IsWeightedPath edges base base cycle
  /-- The cycle has at least one edge. -/
  cycle_nonempty : cycle ≠ []
  /-- The edge sources around the cycle are pairwise distinct. -/
  cycle_simple : (cycle.map Edge.source).Nodup
  /-- The cycle has negative total weight. -/
  cycle_negative : pathWeight cycle < 0

/-- There is a negative cycle reachable from the chosen source. -/
@[expose] public def HasReachableNegativeCycle {n : Nat}
    (edges : List (Edge n)) (source : Fin n) : Prop :=
  Nonempty (ReachableNegativeCycle edges source)

/-- Successful Bellman-Ford output. -/
public structure Distances (n : Nat) where
  /-- The source used for the run. -/
  source : Fin n
  /-- Finite shortest weights, with `none` denoting infinity. -/
  distance : Vector (Option Int) n
  /-- The final predecessor edge for every vertex. -/
  predecessor : Vector (Option (Edge n)) n

/-- Follow successful predecessors for at most `n` edges. -/
public def Distances.pathTo? {n : Nat} (result : Distances n) (target : Fin n) :
    Option (List (Edge n)) := by
  let rec follow (current : Fin n) : Nat → List (Edge n) → Option (List (Edge n))
    | 0, suffix => if current = result.source then some suffix else none
    | fuel + 1, suffix =>
        if current = result.source then
          some suffix
        else
          match result.predecessor.get current with
          | none => none
          | some edge => follow edge.source fuel (edge :: suffix)
  exact follow target n []

/-- Separate counts for edge checks and negative-cycle witness reconstruction. -/
public structure Cost where
  /-- Edge occurrences checked by relaxation passes. -/
  relaxationChecks : Nat
  /-- Predecessor edges read or emitted while reconstructing a failure witness. -/
  cycleWitnessSteps : Nat
deriving DecidableEq

public instance : Zero Cost :=
  ⟨⟨0, 0⟩⟩

public instance : Add Cost :=
  ⟨fun left right =>
    ⟨left.relaxationChecks + right.relaxationChecks,
      left.cycleWitnessSteps + right.cycleWitnessSteps⟩⟩

namespace Internal

@[simp]
theorem Cost.add_relaxationChecks (left right : Cost) :
    (left + right).relaxationChecks = left.relaxationChecks + right.relaxationChecks := rfl

@[simp]
theorem Cost.add_cycleWitnessSteps (left right : Cost) :
    (left + right).cycleWitnessSteps = left.cycleWitnessSteps + right.cycleWitnessSteps := rfl

@[simp]
theorem Cost.zero_relaxationChecks : (0 : Cost).relaxationChecks = 0 := rfl

@[simp]
theorem Cost.zero_cycleWitnessSteps : (0 : Cost).cycleWitnessSteps = 0 := rfl

end Internal

/-- Total abstract events charged by the Bellman-Ford cost model. -/
@[expose] public def Cost.total (cost : Cost) : Nat :=
  cost.relaxationChecks + cost.cycleWitnessSteps

/-- Distances when no reachable negative cycle exists, otherwise a validated witness. -/
public inductive Result {n : Nat} (edges : List (Edge n)) (source : Fin n) where
  /-- Exact shortest distances and predecessor edges. -/
  | distances (result : Distances n)
  /-- A concrete reachable negative cycle. -/
  | negativeCycle (witness : ReachableNegativeCycle edges source)
namespace Internal

structure State (n : Nat) where
  distance : Vector (Option Int) n
  predecessor : Vector (Option (Edge n)) n
  predecessorSourceDistance : Vector (Option Int) n
  predecessorTargetDistance : Vector (Option Int) n
  predecessorUpdateOrdinal : Vector (Option Nat) n
  predecessorSourceOrdinal : Vector (Option (Option Nat)) n
  discoveryPredecessor : Vector (Option (Edge n)) n
  discoveryRank : Vector (Option Nat) n
  nextRank : Nat
  nextUpdateOrdinal : Nat
  lastUpdated : Option (Fin n)

structure State.DiscoveryValid {n : Nat} (edges : List (Edge n))
    (source : Fin n) (state : State n) : Prop where
  source_finite : ∃ distance, state.distance.get source = some distance
  source_rank : state.discoveryRank.get source = some 0
  source_predecessor : state.discoveryPredecessor.get source = none
  finite_rank : ∀ vertex distance,
    state.distance.get vertex = some distance →
      ∃ rank, state.discoveryRank.get vertex = some rank
  finite_predecessor : ∀ vertex distance,
    state.distance.get vertex = some distance → vertex ≠ source →
      ∃ edge, state.discoveryPredecessor.get vertex = some edge
  predecessor_spec : ∀ vertex edge,
    state.discoveryPredecessor.get vertex = some edge →
      edge ∈ edges ∧ edge.target = vertex ∧
        ∃ sourceRank targetRank,
          state.discoveryRank.get edge.source = some sourceRank ∧
            state.discoveryRank.get vertex = some targetRank ∧ sourceRank < targetRank
  rank_finite : ∀ vertex rank,
    state.discoveryRank.get vertex = some rank →
      ∃ distance, state.distance.get vertex = some distance
  rank_lt_next : ∀ vertex rank,
    state.discoveryRank.get vertex = some rank → rank < state.nextRank

theorem State.DiscoveryValid.resetLastUpdated {n : Nat}
    {edges : List (Edge n)} {source : Fin n} {state : State n}
    (valid : state.DiscoveryValid edges source) :
    ({ state with lastUpdated := none }).DiscoveryValid edges source := by
  rcases valid with ⟨source_finite, source_rank, source_predecessor, finite_rank,
    finite_predecessor, predecessor_spec, rank_finite, rank_lt_next⟩
  exact ⟨source_finite, source_rank, source_predecessor, finite_rank,
    finite_predecessor, predecessor_spec, rank_finite, rank_lt_next⟩

def initialState {n : Nat} (source : Fin n) : State n where
  distance := Vector.ofFn fun vertex => if vertex = source then some 0 else none
  predecessor := Vector.replicate n none
  predecessorSourceDistance := Vector.replicate n none
  predecessorTargetDistance := Vector.replicate n none
  predecessorUpdateOrdinal := Vector.replicate n none
  predecessorSourceOrdinal := Vector.replicate n none
  discoveryPredecessor := Vector.replicate n none
  discoveryRank := Vector.ofFn fun vertex => if vertex = source then some 0 else none
  nextRank := 1
  nextUpdateOrdinal := 0
  lastUpdated := none

def State.Realizes {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (state : State n) : Prop :=
  ∀ target distance, state.distance.get target = some distance →
    ∃ path, IsWeightedPath edges source target path ∧ pathWeight path = distance

def State.BoundsPaths {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (steps : Nat) (state : State n) : Prop :=
  ∀ target path, IsWeightedPath edges source target path → path.length ≤ steps →
    ∃ distance,
      state.distance.get target = some distance ∧ distance ≤ pathWeight path

def State.Rooted {n : Nat} (source : Fin n) (state : State n) : Prop :=
  ∀ target distance,
    state.distance.get target = some distance →
      state.predecessor.get target = none → target = source ∧ distance = 0

def State.PredecessorsFrom {n : Nat} (edges : List (Edge n))
    (state : State n) : Prop :=
  ∀ target edge, state.predecessor.get target = some edge → edge ∈ edges

theorem initialState_realizes {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    (initialState source).Realizes edges source := by
  intro target distance distance_eq
  by_cases target_source : target = source
  · subst target
    simp [initialState, Vector.get] at distance_eq
    rcases distance_eq with ⟨_, rfl⟩
    exact ⟨[], by simp [IsWeightedPath], by simp [pathWeight]⟩
  · simp [initialState, Vector.get] at distance_eq
    exfalso
    apply target_source
    apply Fin.ext
    exact congrArg Fin.val distance_eq.1

theorem initialState_boundsPaths {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (initialState source).BoundsPaths edges source 0 := by
  intro target path path_valid length_le
  have path_nil : path = [] := List.length_eq_zero_iff.mp
    (Nat.eq_zero_of_le_zero length_le)
  subst path
  have target_eq : target = source := path_valid.2.2.symm
  subst target
  refine ⟨0, ?_, by simp [pathWeight]⟩
  simp [initialState, Vector.get]
  apply Fin.ext
  rfl

theorem initialState_rooted {n : Nat} (source : Fin n) :
    (initialState source).Rooted source := by
  intro target distance distance_eq _
  by_cases target_source : target = source
  · subst target
    simp [initialState, Vector.get] at distance_eq
    exact ⟨rfl, distance_eq.2.symm⟩
  · simp [initialState, Vector.get] at distance_eq
    exfalso
    apply target_source
    apply Fin.ext
    exact congrArg Fin.val distance_eq.1

theorem initialState_predecessorsFrom {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (initialState source).PredecessorsFrom edges := by
  intro target edge predecessor_eq
  simp [initialState, Vector.get] at predecessor_eq

theorem initialState_discoveryValid {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (initialState source).DiscoveryValid edges source := by
  refine ⟨⟨0, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [initialState, Vector.get]
    apply Fin.ext
    rfl
  · simp [initialState, Vector.get]
    apply Fin.ext
    rfl
  · simp [initialState, Vector.get]
  · intro vertex distance distance_eq
    by_cases vertex_source : vertex = source
    · subst vertex
      exact ⟨0, by
        simp [initialState, Vector.get]
        apply Fin.ext
        rfl⟩
    · simp [initialState, Vector.get] at distance_eq
      exfalso
      apply vertex_source
      apply Fin.ext
      exact congrArg Fin.val distance_eq.1
  · intro vertex distance distance_eq vertex_ne
    simp [initialState, Vector.get] at distance_eq
    exfalso
    apply vertex_ne
    apply Fin.ext
    exact congrArg Fin.val distance_eq.1
  · intro vertex edge predecessor_eq
    simp [initialState, Vector.get] at predecessor_eq
  · intro vertex rank rank_eq
    simp [initialState, Vector.get] at rank_eq
    rcases rank_eq with ⟨vertex_source, rfl⟩
    have vertex_eq : vertex = source := by
      apply Fin.ext
      exact congrArg Fin.val vertex_source
    subst vertex
    exact ⟨0, by
      simp [initialState, Vector.get]
      apply Fin.ext
      rfl⟩
  · intro vertex rank rank_eq
    simp [initialState, Vector.get] at rank_eq
    rcases rank_eq with ⟨_, rfl⟩
    change 0 < 1
    omega

@[simp]
theorem vector_get_set_same {α : Type} {n : Nat} (vector : Vector α n)
    (index : Fin n) (value : α) :
    (vector.set index value).get index = value := by
  change (vector.set index.val value)[index.val] = value
  exact Vector.getElem_set_self index.isLt

theorem vector_get_set_of_ne {α : Type} {n : Nat} (vector : Vector α n)
    {updated queried : Fin n} (different : queried ≠ updated) (value : α) :
    (vector.set updated value).get queried = vector.get queried := by
  have value_different : queried.val ≠ updated.val := by
    intro equal
    exact different (Fin.ext equal)
  change (vector.set updated.val value)[queried.val] = vector[queried.val]
  exact Vector.getElem_set_ne updated.isLt queried.isLt value_different.symm

def State.install {n : Nat} (state : State n) (edge : Edge n)
    (sourceDistance : Int) : State n :=
  let candidate := sourceDistance + edge.weight
  let previousTarget := state.distance.get edge.target
  let firstDiscovery := (state.distance.get edge.target).isNone
  { state with
    distance := state.distance.set edge.target (some candidate)
    predecessor := state.predecessor.set edge.target (some edge)
    predecessorSourceDistance :=
      state.predecessorSourceDistance.set edge.target (some sourceDistance)
    predecessorTargetDistance :=
      state.predecessorTargetDistance.set edge.target (some candidate)
    predecessorUpdateOrdinal :=
      state.predecessorUpdateOrdinal.set edge.target (some state.nextUpdateOrdinal)
    predecessorSourceOrdinal := state.predecessorSourceOrdinal.set edge.target
      (some (state.predecessorUpdateOrdinal.get edge.source))
    discoveryPredecessor :=
      if firstDiscovery then
        state.discoveryPredecessor.set edge.target (some edge)
      else
        state.discoveryPredecessor
    discoveryRank :=
      if firstDiscovery then state.discoveryRank.set edge.target (some state.nextRank)
      else state.discoveryRank
    nextRank := if firstDiscovery then state.nextRank + 1 else state.nextRank
    nextUpdateOrdinal := state.nextUpdateOrdinal + 1
    lastUpdated := some edge.target }

theorem State.install_distance {n : Nat} (state : State n) (edge : Edge n)
    (sourceDistance : Int) :
    (state.install edge sourceDistance).distance =
      state.distance.set edge.target (some (sourceDistance + edge.weight)) := by
  simp [State.install]

theorem State.install_discoveryPredecessor_of_none {n : Nat}
    (state : State n) (edge : Edge n) (sourceDistance : Int)
    (target_none : state.distance.get edge.target = none) :
    (state.install edge sourceDistance).discoveryPredecessor =
      state.discoveryPredecessor.set edge.target (some edge) := by
  simp [State.install, target_none]

theorem State.install_discoveryRank_of_none {n : Nat}
    (state : State n) (edge : Edge n) (sourceDistance : Int)
    (target_none : state.distance.get edge.target = none) :
    (state.install edge sourceDistance).discoveryRank =
      state.discoveryRank.set edge.target (some state.nextRank) := by
  simp [State.install, target_none]

theorem State.install_nextRank_of_none {n : Nat}
    (state : State n) (edge : Edge n) (sourceDistance : Int)
    (target_none : state.distance.get edge.target = none) :
    (state.install edge sourceDistance).nextRank = state.nextRank + 1 := by
  simp [State.install, target_none]

theorem State.install_discoveryPredecessor_of_some {n : Nat}
    (state : State n) (edge : Edge n) (sourceDistance targetDistance : Int)
    (target_eq : state.distance.get edge.target = some targetDistance) :
    (state.install edge sourceDistance).discoveryPredecessor =
      state.discoveryPredecessor := by
  simp [State.install, target_eq]

theorem State.install_discoveryRank_of_some {n : Nat}
    (state : State n) (edge : Edge n) (sourceDistance targetDistance : Int)
    (target_eq : state.distance.get edge.target = some targetDistance) :
    (state.install edge sourceDistance).discoveryRank = state.discoveryRank := by
  simp [State.install, target_eq]

theorem State.install_nextRank_of_some {n : Nat}
    (state : State n) (edge : Edge n) (sourceDistance targetDistance : Int)
    (target_eq : state.distance.get edge.target = some targetDistance) :
    (state.install edge sourceDistance).nextRank = state.nextRank := by
  simp [State.install, target_eq]

theorem State.install_discoveryValid_of_none {n : Nat}
    {edges : List (Edge n)} {source : Fin n} {state : State n}
    (valid : state.DiscoveryValid edges source) (edge : Edge n)
    (edge_mem : edge ∈ edges) (sourceDistance : Int)
    (source_eq : state.distance.get edge.source = some sourceDistance)
    (target_none : state.distance.get edge.target = none) :
    (state.install edge sourceDistance).DiscoveryValid edges source := by
  have target_ne_source : edge.target ≠ source := by
    rintro rfl
    obtain ⟨distance, distance_eq⟩ := valid.source_finite
    rw [target_none] at distance_eq
    contradiction
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨distance, distance_eq⟩ := valid.source_finite
    exact ⟨distance, by
      change (state.distance.set edge.target (some (sourceDistance + edge.weight))).get
        source = some distance
      rwa [vector_get_set_of_ne state.distance target_ne_source.symm]⟩
  · rw [State.install_discoveryRank_of_none state edge sourceDistance target_none,
      vector_get_set_of_ne state.discoveryRank target_ne_source.symm]
    exact valid.source_rank
  · rw [State.install_discoveryPredecessor_of_none state edge sourceDistance target_none,
      vector_get_set_of_ne state.discoveryPredecessor target_ne_source.symm]
    exact valid.source_predecessor
  · intro vertex distance distance_eq
    by_cases vertex_target : vertex = edge.target
    · subst vertex
      exact ⟨state.nextRank, by
        rw [State.install_discoveryRank_of_none state edge sourceDistance target_none,
          vector_get_set_same]⟩
    · have old_distance : state.distance.get vertex = some distance := by
        rw [State.install_distance,
          vector_get_set_of_ne state.distance vertex_target] at distance_eq
        exact distance_eq
      obtain ⟨rank, old_rank⟩ := valid.finite_rank vertex distance old_distance
      exact ⟨rank, by
        rw [State.install_discoveryRank_of_none state edge sourceDistance target_none,
          vector_get_set_of_ne state.discoveryRank vertex_target]
        exact old_rank⟩
  · intro vertex distance distance_eq vertex_source
    by_cases vertex_target : vertex = edge.target
    · subst vertex
      exact ⟨edge, by
        rw [State.install_discoveryPredecessor_of_none state edge sourceDistance target_none,
          vector_get_set_same]⟩
    · obtain ⟨oldDistance, old_distance⟩ :
          ∃ oldDistance, state.distance.get vertex = some oldDistance := by
        refine ⟨distance, ?_⟩
        change (state.distance.set edge.target (some (sourceDistance + edge.weight))).get
          vertex = some distance at distance_eq
        rwa [vector_get_set_of_ne state.distance vertex_target] at distance_eq
      obtain ⟨predecessor, predecessor_eq⟩ :=
        valid.finite_predecessor vertex oldDistance old_distance vertex_source
      exact ⟨predecessor, by
        rw [State.install_discoveryPredecessor_of_none state edge sourceDistance target_none,
          vector_get_set_of_ne state.discoveryPredecessor vertex_target]
        exact predecessor_eq⟩
  · intro vertex predecessor predecessor_eq
    by_cases vertex_target : vertex = edge.target
    · subst vertex
      have predecessor_edge : predecessor = edge := by
        rw [State.install_discoveryPredecessor_of_none state edge sourceDistance target_none,
          vector_get_set_same] at predecessor_eq
        exact (Option.some.inj predecessor_eq).symm
      subst predecessor
      obtain ⟨sourceRank, source_rank⟩ :=
        valid.finite_rank edge.source sourceDistance source_eq
      exact ⟨edge_mem, rfl, sourceRank, state.nextRank, by
        rw [State.install_discoveryRank_of_none state edge sourceDistance target_none]
        by_cases source_target : edge.source = edge.target
        · have impossible : state.distance.get edge.target = some sourceDistance := by
            rwa [← source_target]
          rw [target_none] at impossible
          contradiction
        · rwa [vector_get_set_of_ne state.discoveryRank source_target],
        by rw [State.install_discoveryRank_of_none state edge sourceDistance target_none,
          vector_get_set_same],
        valid.rank_lt_next edge.source sourceRank source_rank⟩
    · have old_predecessor :
          state.discoveryPredecessor.get vertex = some predecessor := by
        rw [State.install_discoveryPredecessor_of_none state edge sourceDistance target_none,
          vector_get_set_of_ne state.discoveryPredecessor vertex_target] at predecessor_eq
        exact predecessor_eq
      obtain ⟨predecessor_mem, predecessor_target, sourceRank, targetRank,
          source_rank, target_rank, rank_lt⟩ := valid.predecessor_spec _ _ old_predecessor
      exact ⟨predecessor_mem, predecessor_target, sourceRank, targetRank, by
        rw [State.install_discoveryRank_of_none state edge sourceDistance target_none]
        by_cases predecessor_source : predecessor.source = edge.target
        · obtain ⟨distance, distance_eq⟩ :=
            valid.rank_finite predecessor.source sourceRank source_rank
          rw [predecessor_source, target_none] at distance_eq
          contradiction
        · rwa [vector_get_set_of_ne state.discoveryRank predecessor_source], by
        rw [State.install_discoveryRank_of_none state edge sourceDistance target_none,
          vector_get_set_of_ne state.discoveryRank vertex_target]
        exact target_rank, rank_lt⟩
  · intro vertex rank rank_eq
    by_cases vertex_target : vertex = edge.target
    · subst vertex
      exact ⟨sourceDistance + edge.weight, by
        rw [State.install_distance, vector_get_set_same]⟩
    · have old_rank : state.discoveryRank.get vertex = some rank := by
        rw [State.install_discoveryRank_of_none state edge sourceDistance target_none,
          vector_get_set_of_ne state.discoveryRank vertex_target] at rank_eq
        exact rank_eq
      obtain ⟨distance, distance_eq⟩ := valid.rank_finite vertex rank old_rank
      exact ⟨distance, by
        rw [State.install_distance,
          vector_get_set_of_ne state.distance vertex_target]
        exact distance_eq⟩
  · intro vertex rank rank_eq
    by_cases vertex_target : vertex = edge.target
    · subst vertex
      rw [State.install_discoveryRank_of_none state edge sourceDistance target_none,
        vector_get_set_same] at rank_eq
      rw [State.install_nextRank_of_none state edge sourceDistance target_none]
      have rank_value : rank = state.nextRank := (Option.some.inj rank_eq).symm
      subst rank
      omega
    · have old_rank : state.discoveryRank.get vertex = some rank := by
        rw [State.install_discoveryRank_of_none state edge sourceDistance target_none,
          vector_get_set_of_ne state.discoveryRank vertex_target] at rank_eq
        exact rank_eq
      have := valid.rank_lt_next vertex rank old_rank
      rw [State.install_nextRank_of_none state edge sourceDistance target_none]
      omega

theorem State.install_discoveryValid_of_some {n : Nat}
    {edges : List (Edge n)} {source : Fin n} {state : State n}
    (valid : state.DiscoveryValid edges source) (edge : Edge n)
    (sourceDistance targetDistance : Int)
    (target_eq : state.distance.get edge.target = some targetDistance) :
    (state.install edge sourceDistance).DiscoveryValid edges source := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases source_target : source = edge.target
    · subst source
      exact ⟨sourceDistance + edge.weight, by
        rw [State.install_distance, vector_get_set_same]⟩
    · obtain ⟨distance, distance_eq⟩ := valid.source_finite
      exact ⟨distance, by
        rw [State.install_distance,
          vector_get_set_of_ne state.distance source_target]
        exact distance_eq⟩
  · rw [State.install_discoveryRank_of_some state edge sourceDistance targetDistance
      target_eq]
    exact valid.source_rank
  · rw [State.install_discoveryPredecessor_of_some state edge sourceDistance targetDistance
      target_eq]
    exact valid.source_predecessor
  · intro vertex distance distance_eq
    rw [State.install_discoveryRank_of_some state edge sourceDistance targetDistance
      target_eq]
    by_cases vertex_target : vertex = edge.target
    · subst vertex
      exact valid.finite_rank edge.target targetDistance target_eq
    · have old_distance : state.distance.get vertex = some distance := by
        rw [State.install_distance,
          vector_get_set_of_ne state.distance vertex_target] at distance_eq
        exact distance_eq
      exact valid.finite_rank vertex distance old_distance
  · intro vertex distance distance_eq vertex_source
    rw [State.install_discoveryPredecessor_of_some state edge sourceDistance targetDistance
      target_eq]
    by_cases vertex_target : vertex = edge.target
    · subst vertex
      exact valid.finite_predecessor edge.target targetDistance target_eq vertex_source
    · have old_distance : state.distance.get vertex = some distance := by
        rw [State.install_distance,
          vector_get_set_of_ne state.distance vertex_target] at distance_eq
        exact distance_eq
      exact valid.finite_predecessor vertex distance old_distance vertex_source
  · intro vertex predecessor predecessor_eq
    rw [State.install_discoveryPredecessor_of_some state edge sourceDistance targetDistance
      target_eq] at predecessor_eq
    rw [State.install_discoveryRank_of_some state edge sourceDistance targetDistance
      target_eq]
    exact valid.predecessor_spec vertex predecessor predecessor_eq
  · intro vertex rank rank_eq
    rw [State.install_discoveryRank_of_some state edge sourceDistance targetDistance
      target_eq] at rank_eq
    obtain ⟨distance, distance_eq⟩ := valid.rank_finite vertex rank rank_eq
    by_cases vertex_target : vertex = edge.target
    · subst vertex
      exact ⟨sourceDistance + edge.weight, by
        rw [State.install_distance, vector_get_set_same]⟩
    · exact ⟨distance, by
        rw [State.install_distance,
          vector_get_set_of_ne state.distance vertex_target]
        exact distance_eq⟩
  · intro vertex rank rank_eq
    rw [State.install_discoveryRank_of_some state edge sourceDistance targetDistance
      target_eq] at rank_eq
    rw [State.install_nextRank_of_some state edge sourceDistance targetDistance target_eq]
    exact valid.rank_lt_next vertex rank rank_eq

theorem State.install_snapshot {n : Nat} (state : State n) (edge : Edge n)
    (sourceDistance : Int) :
    (state.install edge sourceDistance).predecessor.get edge.target = some edge ∧
      (state.install edge sourceDistance).predecessorSourceDistance.get edge.target =
        some sourceDistance ∧
      (state.install edge sourceDistance).predecessorTargetDistance.get edge.target =
        some (sourceDistance + edge.weight) ∧
      (state.install edge sourceDistance).predecessorUpdateOrdinal.get edge.target =
        some state.nextUpdateOrdinal ∧
      (state.install edge sourceDistance).predecessorSourceOrdinal.get edge.target =
        some (state.predecessorUpdateOrdinal.get edge.source) := by
  simp [State.install, vector_get_set_same]

theorem State.install_realizes {n : Nat} {edges : List (Edge n)} {source : Fin n}
    {state : State n} {edge : Edge n} {sourceDistance : Int}
    (realizes : state.Realizes edges source) (edge_mem : edge ∈ edges)
    (source_distance : state.distance.get edge.source = some sourceDistance) :
    (state.install edge sourceDistance).Realizes edges source := by
  intro target distance distance_eq
  by_cases target_eq : target = edge.target
  · subst target
    change (state.distance.set edge.target (some (sourceDistance + edge.weight))).get
      edge.target = some distance at distance_eq
    rw [vector_get_set_same] at distance_eq
    have distance_value : sourceDistance + edge.weight = distance :=
      Option.some.inj distance_eq
    subst distance
    obtain ⟨path, path_valid, path_weight⟩ :=
      realizes edge.source sourceDistance source_distance
    exact ⟨path ++ [edge],
      isWeightedPath_append_edge path_valid edge_mem rfl rfl,
      by simp [pathWeight_append_edge, path_weight]⟩
  · have old_distance : state.distance.get target = some distance := by
      change (state.distance.set edge.target (some (sourceDistance + edge.weight))).get target =
        some distance at distance_eq
      rwa [vector_get_set_of_ne state.distance target_eq] at distance_eq
    exact realizes target distance old_distance

theorem State.install_rooted {n : Nat} {source : Fin n} {state : State n}
    (rooted : state.Rooted source) (edge : Edge n) (sourceDistance : Int) :
    (state.install edge sourceDistance).Rooted source := by
  intro target distance distance_eq predecessor_none
  by_cases target_eq : target = edge.target
  · subst target
    simp [State.install, vector_get_set_same] at predecessor_none
  · apply rooted target distance
    · change (state.distance.set edge.target (some (sourceDistance + edge.weight))).get
        target = some distance at distance_eq
      rwa [vector_get_set_of_ne state.distance target_eq] at distance_eq
    · change (state.predecessor.set edge.target (some edge)).get target = none at predecessor_none
      rwa [vector_get_set_of_ne state.predecessor target_eq] at predecessor_none

theorem State.install_predecessorsFrom {n : Nat} {edges : List (Edge n)}
    {state : State n} (from_edges : state.PredecessorsFrom edges)
    (edge : Edge n) (edge_mem : edge ∈ edges) (sourceDistance : Int) :
    (state.install edge sourceDistance).PredecessorsFrom edges := by
  intro target predecessorEdge predecessor_eq
  by_cases target_eq : target = edge.target
  · subst target
    change (state.predecessor.set edge.target (some edge)).get edge.target =
      some predecessorEdge at predecessor_eq
    rw [vector_get_set_same] at predecessor_eq
    simpa [Option.some.inj predecessor_eq] using edge_mem
  · apply from_edges target predecessorEdge
    change (state.predecessor.set edge.target (some edge)).get target =
      some predecessorEdge at predecessor_eq
    rwa [vector_get_set_of_ne state.predecessor target_eq] at predecessor_eq

end Internal

end Cslib.Algorithms.Lean.BellmanFord
