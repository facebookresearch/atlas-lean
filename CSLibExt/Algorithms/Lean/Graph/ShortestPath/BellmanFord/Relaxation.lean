/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Basic

/-! # Bellman-Ford relaxation state and invariants -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BellmanFord

namespace Internal

def State.DistanceDecreases {n : Nat} (after before : State n) : Prop :=
  ∀ vertex beforeDistance, before.distance.get vertex = some beforeDistance →
    ∃ afterDistance,
      after.distance.get vertex = some afterDistance ∧ afterDistance ≤ beforeDistance

def State.LastUpdatedImprovedFrom {n : Nat} (state origin : State n) : Prop :=
  ∀ target, state.lastUpdated = some target →
    ∃ newDistance,
      state.distance.get target = some newDistance ∧
        (origin.distance.get target = none ∨
          ∃ oldDistance,
            origin.distance.get target = some oldDistance ∧ newDistance < oldDistance)

theorem State.install_distanceDecreases {n : Nat} (state : State n)
    (edge : Edge n) (sourceDistance : Int)
    (improves : ∀ targetDistance,
      state.distance.get edge.target = some targetDistance →
        sourceDistance + edge.weight < targetDistance) :
    (state.install edge sourceDistance).DistanceDecreases state := by
  intro vertex beforeDistance before_eq
  by_cases vertex_target : vertex = edge.target
  · subst vertex
    refine ⟨sourceDistance + edge.weight, ?_, ?_⟩
    · simp [State.install, vector_get_set_same]
    · exact (improves beforeDistance before_eq).le
  · refine ⟨beforeDistance, ?_, le_rfl⟩
    change (state.distance.set edge.target (some (sourceDistance + edge.weight))).get
      vertex = some beforeDistance
    rwa [vector_get_set_of_ne state.distance vertex_target]

def relaxOne {n : Nat} (state : State n) (edge : Edge n) : State n :=
  match state.distance.get edge.source with
  | none => state
  | some sourceDistance =>
      let candidate := sourceDistance + edge.weight
      match state.distance.get edge.target with
      | none => state.install edge sourceDistance
      | some targetDistance =>
          if candidate < targetDistance then state.install edge sourceDistance else state

theorem relaxOne_distanceDecreases {n : Nat} (state : State n) (edge : Edge n) :
    (relaxOne state edge).DistanceDecreases state := by
  cases source_eq : state.distance.get edge.source with
  | none =>
      intro vertex distance distance_eq
      exact ⟨distance, by simpa [relaxOne, source_eq] using distance_eq, le_rfl⟩
  | some sourceDistance =>
      cases target_eq : state.distance.get edge.target with
      | none =>
          simpa [relaxOne, source_eq, target_eq] using
            State.install_distanceDecreases state edge sourceDistance
              (by
                intro targetDistance impossible
                rw [target_eq] at impossible
                contradiction)
      | some targetDistance =>
          by_cases improves : sourceDistance + edge.weight < targetDistance
          · simpa [relaxOne, source_eq, target_eq, improves] using
              State.install_distanceDecreases state edge sourceDistance
                (by
                  intro otherDistance other_eq
                  have : otherDistance = targetDistance :=
                    Option.some.inj (other_eq.symm.trans target_eq)
                  simpa [this] using improves)
          · intro vertex distance distance_eq
            exact ⟨distance,
              by simpa [relaxOne, source_eq, target_eq, improves] using distance_eq,
              le_rfl⟩

theorem relaxOne_lastUpdatedImprovedFrom {n : Nat}
    {origin state : State n} (decreases : state.DistanceDecreases origin)
    (improved : state.LastUpdatedImprovedFrom origin) (edge : Edge n) :
    (relaxOne state edge).LastUpdatedImprovedFrom origin := by
  cases source_eq : state.distance.get edge.source with
  | none => simpa [relaxOne, source_eq] using improved
  | some sourceDistance =>
      cases target_eq : state.distance.get edge.target with
      | none =>
          intro target last_eq
          have target_vertex : target = edge.target := by
            simp [relaxOne, source_eq, target_eq, State.install] at last_eq
            exact last_eq.symm
          subst target
          refine ⟨sourceDistance + edge.weight,
            by simp [relaxOne, source_eq, target_eq, State.install, vector_get_set_same], ?_⟩
          cases origin_eq : origin.distance.get edge.target with
          | none => exact Or.inl rfl
          | some oldDistance =>
              obtain ⟨currentDistance, current_eq, _⟩ :=
                decreases edge.target oldDistance origin_eq
              rw [target_eq] at current_eq
              contradiction
      | some targetDistance =>
          by_cases relaxes : sourceDistance + edge.weight < targetDistance
          · intro target last_eq
            have target_vertex : target = edge.target := by
              simp [relaxOne, source_eq, target_eq, relaxes, State.install] at last_eq
              exact last_eq.symm
            subst target
            refine ⟨sourceDistance + edge.weight,
              by simp [relaxOne, source_eq, target_eq, relaxes, State.install,
                vector_get_set_same], ?_⟩
            cases origin_eq : origin.distance.get edge.target with
            | none => exact Or.inl rfl
            | some oldDistance =>
                obtain ⟨currentDistance, current_eq, current_le⟩ :=
                  decreases edge.target oldDistance origin_eq
                have current_value : currentDistance = targetDistance :=
                  Option.some.inj (current_eq.symm.trans target_eq)
                subst currentDistance
                exact Or.inr ⟨oldDistance, rfl, by omega⟩
          · simpa [relaxOne, source_eq, target_eq, relaxes] using improved

theorem relaxOne_edge_bound {n : Nat} (state : State n) (edge : Edge n)
    (sourceDistance : Int)
    (source_eq : state.distance.get edge.source = some sourceDistance) :
    ∃ targetDistance,
      (relaxOne state edge).distance.get edge.target = some targetDistance ∧
        targetDistance ≤ sourceDistance + edge.weight := by
  cases target_eq : state.distance.get edge.target with
  | none =>
      exact ⟨sourceDistance + edge.weight,
        by simp [relaxOne, source_eq, target_eq, State.install, vector_get_set_same],
        le_rfl⟩
  | some targetDistance =>
      by_cases improves : sourceDistance + edge.weight < targetDistance
      · exact ⟨sourceDistance + edge.weight,
          by simp [relaxOne, source_eq, target_eq, improves, State.install,
            vector_get_set_same],
          le_rfl⟩
      · exact ⟨targetDistance,
          by simp [relaxOne, source_eq, target_eq, improves],
          by omega⟩

theorem State.DistanceDecreases.trans {n : Nat} {first middle last : State n}
    (last_middle : last.DistanceDecreases middle)
    (middle_first : middle.DistanceDecreases first) :
    last.DistanceDecreases first := by
  intro vertex firstDistance first_eq
  obtain ⟨middleDistance, middle_eq, middle_le⟩ :=
    middle_first vertex firstDistance first_eq
  obtain ⟨lastDistance, last_eq, last_le⟩ :=
    last_middle vertex middleDistance middle_eq
  exact ⟨lastDistance, last_eq, last_le.trans middle_le⟩

def State.OrdinalsBound {n : Nat} (state : State n) : Prop :=
  ∀ vertex ordinal,
    state.predecessorUpdateOrdinal.get vertex = some ordinal →
      ordinal < state.nextUpdateOrdinal

def State.CurrentSnapshotsValid {n : Nat} (state : State n) : Prop :=
  ∀ target edge, state.predecessor.get target = some edge →
    ∃ sourceDistance targetDistance ordinal sourceOrdinal,
      state.predecessorSourceDistance.get target = some sourceDistance ∧
        state.predecessorTargetDistance.get target = some targetDistance ∧
        state.predecessorUpdateOrdinal.get target = some ordinal ∧
        state.predecessorSourceOrdinal.get target = some sourceOrdinal ∧
        edge.target = target ∧
        state.distance.get target = some targetDistance ∧
        targetDistance = sourceDistance + edge.weight ∧
        (∃ currentSourceDistance,
          state.distance.get edge.source = some currentSourceDistance ∧
            currentSourceDistance ≤ sourceDistance) ∧
        (state.distance.get edge.source = some sourceDistance →
          state.predecessorUpdateOrdinal.get edge.source = sourceOrdinal) ∧
        ∀ sourceOrdinalValue,
          sourceOrdinal = some sourceOrdinalValue → sourceOrdinalValue < ordinal

theorem initialState_currentSnapshotsValid {n : Nat} (source : Fin n) :
    (initialState source).CurrentSnapshotsValid := by
  intro target edge predecessor_eq
  simp [initialState, Vector.get] at predecessor_eq

theorem initialState_ordinalsBound {n : Nat} (source : Fin n) :
    (initialState source).OrdinalsBound := by
  intro vertex ordinal ordinal_eq
  simp [initialState, Vector.get] at ordinal_eq

theorem State.install_ordinalsBound {n : Nat} {state : State n}
    (ordinals : state.OrdinalsBound) (edge : Edge n) (sourceDistance : Int) :
    (state.install edge sourceDistance).OrdinalsBound := by
  intro vertex ordinal ordinal_eq
  by_cases vertex_target : vertex = edge.target
  · subst vertex
    simp [State.install, vector_get_set_same] at ordinal_eq
    change ordinal < state.nextUpdateOrdinal + 1
    omega
  · have old_eq : state.predecessorUpdateOrdinal.get vertex = some ordinal := by
      change
        (state.predecessorUpdateOrdinal.set edge.target (some state.nextUpdateOrdinal)).get
          vertex = some ordinal at ordinal_eq
      rwa [vector_get_set_of_ne state.predecessorUpdateOrdinal vertex_target] at ordinal_eq
    have := ordinals vertex ordinal old_eq
    simp [State.install]
    omega

theorem State.install_currentSnapshotsValid {n : Nat} {state : State n}
    (valid : state.CurrentSnapshotsValid) (ordinals : state.OrdinalsBound)
    (edge : Edge n) (sourceDistance : Int)
    (source_eq : state.distance.get edge.source = some sourceDistance)
    (improves : ∀ targetDistance,
      state.distance.get edge.target = some targetDistance →
        sourceDistance + edge.weight < targetDistance) :
    (state.install edge sourceDistance).CurrentSnapshotsValid := by
  intro target predecessorEdge predecessor_eq
  by_cases target_eq : target = edge.target
  · subst target
    have predecessorEdge_eq : predecessorEdge = edge := by
      change (state.predecessor.set edge.target (some edge)).get edge.target =
        some predecessorEdge at predecessor_eq
      rw [vector_get_set_same] at predecessor_eq
      exact (Option.some.inj predecessor_eq).symm
    subst predecessorEdge
    let sourceOrdinal := state.predecessorUpdateOrdinal.get edge.source
    refine ⟨sourceDistance, sourceDistance + edge.weight, state.nextUpdateOrdinal,
      sourceOrdinal, ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · simp [State.install, vector_get_set_same]
    · simp [State.install, vector_get_set_same]
    · simp [State.install, vector_get_set_same]
    · simp [State.install, sourceOrdinal, vector_get_set_same]
    · simp [State.install, vector_get_set_same]
    · by_cases same : edge.source = edge.target
      · refine ⟨sourceDistance + edge.weight,
          by simp [State.install, same, vector_get_set_same], ?_⟩
        apply (improves sourceDistance ?_).le
        rwa [← same]
      · refine ⟨sourceDistance, ?_, le_rfl⟩
        change (state.distance.set edge.target (some (sourceDistance + edge.weight))).get
          edge.source = some sourceDistance
        rwa [vector_get_set_of_ne state.distance same]
    · intro final_source_eq
      by_cases same : edge.source = edge.target
      · have candidate_lt : sourceDistance + edge.weight < sourceDistance :=
          improves sourceDistance (by rwa [← same])
        have candidate_eq : sourceDistance + edge.weight = sourceDistance := by
          change
            (state.distance.set edge.target (some (sourceDistance + edge.weight))).get
              edge.source = some sourceDistance at final_source_eq
          rw [same, vector_get_set_same] at final_source_eq
          exact Option.some.inj final_source_eq
        omega
      · change
          (state.predecessorUpdateOrdinal.set edge.target
            (some state.nextUpdateOrdinal)).get edge.source = sourceOrdinal
        rw [vector_get_set_of_ne state.predecessorUpdateOrdinal same]
    · intro sourceOrdinalValue source_ordinal_eq
      exact ordinals edge.source sourceOrdinalValue source_ordinal_eq
  · obtain ⟨snapshotSource, snapshotTarget, ordinal, sourceOrdinal,
        snapshot_source_eq, snapshot_target_eq, ordinal_eq, source_ordinal_eq,
        predecessor_target, target_distance, target_formula,
        ⟨currentSource, current_source_eq, current_source_le⟩,
        source_ordinal_current, source_ordinal_lt⟩ :=
      valid target predecessorEdge (by
        change (state.predecessor.set edge.target (some edge)).get target =
          some predecessorEdge at predecessor_eq
        rwa [vector_get_set_of_ne state.predecessor target_eq] at predecessor_eq)
    refine ⟨snapshotSource, snapshotTarget, ordinal, sourceOrdinal, ?_, ?_, ?_, ?_,
      predecessor_target, ?_, target_formula, ?_, ?_, source_ordinal_lt⟩
    · change
        (state.predecessorSourceDistance.set edge.target (some sourceDistance)).get target =
          some snapshotSource
      rwa [vector_get_set_of_ne state.predecessorSourceDistance target_eq]
    · change
        (state.predecessorTargetDistance.set edge.target
          (some (sourceDistance + edge.weight))).get target = some snapshotTarget
      rwa [vector_get_set_of_ne state.predecessorTargetDistance target_eq]
    · change
        (state.predecessorUpdateOrdinal.set edge.target
          (some state.nextUpdateOrdinal)).get target = some ordinal
      rwa [vector_get_set_of_ne state.predecessorUpdateOrdinal target_eq]
    · change
        (state.predecessorSourceOrdinal.set edge.target
          (some (state.predecessorUpdateOrdinal.get edge.source))).get target =
            some sourceOrdinal
      rwa [vector_get_set_of_ne state.predecessorSourceOrdinal target_eq]
    · change (state.distance.set edge.target (some (sourceDistance + edge.weight))).get
        target = some snapshotTarget
      rwa [vector_get_set_of_ne state.distance target_eq]
    · have decreases := State.install_distanceDecreases state edge sourceDistance improves
      exact decreases predecessorEdge.source currentSource current_source_eq |>.imp
        fun _ pair => ⟨pair.1, pair.2.trans current_source_le⟩
    · intro final_source_eq
      by_cases updated_source : predecessorEdge.source = edge.target
      · have candidate_eq : sourceDistance + edge.weight = snapshotSource := by
          change (state.distance.set edge.target (some (sourceDistance + edge.weight))).get
            predecessorEdge.source = some snapshotSource at final_source_eq
          rw [updated_source, vector_get_set_same] at final_source_eq
          exact Option.some.inj final_source_eq
        have target_old_eq : state.distance.get edge.target = some currentSource := by
          rwa [← updated_source]
        have candidate_lt := improves currentSource target_old_eq
        omega
      · have old_source_eq :
            state.distance.get predecessorEdge.source = some snapshotSource := by
          change (state.distance.set edge.target (some (sourceDistance + edge.weight))).get
            predecessorEdge.source = some snapshotSource at final_source_eq
          rwa [vector_get_set_of_ne state.distance updated_source] at final_source_eq
        have old_ordinal := source_ordinal_current old_source_eq
        change
          (state.predecessorUpdateOrdinal.set edge.target
            (some state.nextUpdateOrdinal)).get predecessorEdge.source = sourceOrdinal
        rwa [vector_get_set_of_ne state.predecessorUpdateOrdinal updated_source]

theorem relaxOne_ordinalsBound {n : Nat} {state : State n}
    (ordinals : state.OrdinalsBound) (edge : Edge n) :
    (relaxOne state edge).OrdinalsBound := by
  cases source_eq : state.distance.get edge.source with
  | none => simpa [relaxOne, source_eq] using ordinals
  | some sourceDistance =>
      cases target_eq : state.distance.get edge.target with
      | none =>
          simpa [relaxOne, source_eq, target_eq] using
            State.install_ordinalsBound ordinals edge sourceDistance
      | some targetDistance =>
          by_cases improves : sourceDistance + edge.weight < targetDistance
          · simpa [relaxOne, source_eq, target_eq, improves] using
              State.install_ordinalsBound ordinals edge sourceDistance
          · simpa [relaxOne, source_eq, target_eq, improves] using ordinals

theorem relaxOne_currentSnapshotsValid {n : Nat} {state : State n}
    (valid : state.CurrentSnapshotsValid) (ordinals : state.OrdinalsBound)
    (edge : Edge n) :
    (relaxOne state edge).CurrentSnapshotsValid := by
  cases source_eq : state.distance.get edge.source with
  | none => simpa [relaxOne, source_eq] using valid
  | some sourceDistance =>
      cases target_eq : state.distance.get edge.target with
      | none =>
          simpa [relaxOne, source_eq, target_eq] using
            State.install_currentSnapshotsValid valid ordinals edge sourceDistance source_eq
              (by simp [target_eq])
      | some targetDistance =>
          by_cases improves : sourceDistance + edge.weight < targetDistance
          · simpa [relaxOne, source_eq, target_eq, improves] using
              State.install_currentSnapshotsValid valid ordinals edge sourceDistance source_eq
                (by
                  intro otherDistance other_eq
                  have : otherDistance = targetDistance :=
                    Option.some.inj (other_eq.symm.trans target_eq)
                  simpa [this] using improves)
          · simpa [relaxOne, source_eq, target_eq, improves] using valid

theorem relaxOne_realizes {n : Nat} {edges : List (Edge n)} {source : Fin n}
    {state : State n} (realizes : state.Realizes edges source) {edge : Edge n}
    (edge_mem : edge ∈ edges) :
    (relaxOne state edge).Realizes edges source := by
  cases source_eq : state.distance.get edge.source with
  | none => simpa [relaxOne, source_eq] using realizes
  | some sourceDistance =>
      cases target_eq : state.distance.get edge.target with
      | none =>
          simpa [relaxOne, source_eq, target_eq] using
            state.install_realizes realizes edge_mem source_eq
      | some targetDistance =>
          by_cases improves : sourceDistance + edge.weight < targetDistance
          · simpa [relaxOne, source_eq, target_eq, improves] using
              state.install_realizes realizes edge_mem source_eq
          · simpa [relaxOne, source_eq, target_eq, improves] using realizes

theorem relaxOne_rooted {n : Nat} {source : Fin n} {state : State n}
    (rooted : state.Rooted source) (edge : Edge n) :
    (relaxOne state edge).Rooted source := by
  cases source_eq : state.distance.get edge.source with
  | none => simpa [relaxOne, source_eq] using rooted
  | some sourceDistance =>
      cases target_eq : state.distance.get edge.target with
      | none =>
          simpa [relaxOne, source_eq, target_eq] using
            State.install_rooted rooted edge sourceDistance
      | some targetDistance =>
          by_cases improves : sourceDistance + edge.weight < targetDistance
          · simpa [relaxOne, source_eq, target_eq, improves] using
              State.install_rooted rooted edge sourceDistance
          · simpa [relaxOne, source_eq, target_eq, improves] using rooted

theorem relaxOne_predecessorsFrom {n : Nat} {edges : List (Edge n)}
    {state : State n} (from_edges : state.PredecessorsFrom edges)
    (edge : Edge n) (edge_mem : edge ∈ edges) :
    (relaxOne state edge).PredecessorsFrom edges := by
  cases source_eq : state.distance.get edge.source with
  | none => simpa [relaxOne, source_eq] using from_edges
  | some sourceDistance =>
      cases target_eq : state.distance.get edge.target with
      | none =>
          simpa [relaxOne, source_eq, target_eq] using
            State.install_predecessorsFrom from_edges edge edge_mem sourceDistance
      | some targetDistance =>
          by_cases improves : sourceDistance + edge.weight < targetDistance
          · simpa [relaxOne, source_eq, target_eq, improves] using
              State.install_predecessorsFrom from_edges edge edge_mem sourceDistance
          · simpa [relaxOne, source_eq, target_eq, improves] using from_edges

theorem relaxOne_discoveryValid {n : Nat} {edges : List (Edge n)}
    {source : Fin n} {state : State n} (valid : state.DiscoveryValid edges source)
    (edge : Edge n) (edge_mem : edge ∈ edges) :
    (relaxOne state edge).DiscoveryValid edges source := by
  cases source_eq : state.distance.get edge.source with
  | none => simpa [relaxOne, source_eq] using valid
  | some sourceDistance =>
      cases target_eq : state.distance.get edge.target with
      | none =>
          simpa [relaxOne, source_eq, target_eq] using
            State.install_discoveryValid_of_none valid edge edge_mem sourceDistance
              source_eq target_eq
      | some targetDistance =>
          by_cases improves : sourceDistance + edge.weight < targetDistance
          · simpa [relaxOne, source_eq, target_eq, improves] using
              State.install_discoveryValid_of_some valid edge sourceDistance targetDistance
                target_eq
          · simpa [relaxOne, source_eq, target_eq, improves] using valid

def State.EdgeStable {n : Nat} (state : State n) (edge : Edge n) : Prop :=
  ∀ sourceDistance, state.distance.get edge.source = some sourceDistance →
    ∃ targetDistance,
      state.distance.get edge.target = some targetDistance ∧
        targetDistance ≤ sourceDistance + edge.weight

theorem relaxOne_eq_self_and_stable_of_lastUpdated_none {n : Nat}
    (state : State n) (edge : Edge n)
    (after_none : (relaxOne state edge).lastUpdated = none) :
    relaxOne state edge = state ∧ state.EdgeStable edge := by
  cases source_eq : state.distance.get edge.source with
  | none =>
      refine ⟨by simp [relaxOne, source_eq], ?_⟩
      intro sourceDistance impossible
      simp [source_eq] at impossible
  | some sourceDistance =>
      cases target_eq : state.distance.get edge.target with
      | none =>
          simp [relaxOne, source_eq, target_eq, State.install] at after_none
      | some targetDistance =>
          by_cases improves : sourceDistance + edge.weight < targetDistance
          · simp [relaxOne, source_eq, target_eq, improves, State.install] at after_none
          · refine ⟨by simp [relaxOne, source_eq, target_eq, improves], ?_⟩
            intro distance source_distance
            have distance_eq : distance = sourceDistance := Option.some.inj
              (source_distance.symm.trans source_eq)
            subst distance
            exact ⟨targetDistance, target_eq, by omega⟩

theorem relaxOne_lastUpdated_ne_none {n : Nat} (state : State n) (edge : Edge n)
    (before : state.lastUpdated ≠ none) :
    (relaxOne state edge).lastUpdated ≠ none := by
  cases source_eq : state.distance.get edge.source with
  | none => simpa [relaxOne, source_eq] using before
  | some sourceDistance =>
      cases target_eq : state.distance.get edge.target with
      | none => simp [relaxOne, source_eq, target_eq, State.install]
      | some targetDistance =>
          by_cases improves : sourceDistance + edge.weight < targetDistance
          · simp [relaxOne, source_eq, target_eq, improves, State.install]
          · simpa [relaxOne, source_eq, target_eq, improves] using before

def relaxEdges {n : Nat} :
    List (Edge n) → State n → TimeM Cost (State n)
  | [], state => pure state
  | edge :: rest, state => do
      let _ ← TimeM.tick ⟨1, 0⟩
      relaxEdges rest (relaxOne state edge)

theorem relaxEdges_distanceDecreases {n : Nat} (edges : List (Edge n))
    (state : State n) :
    (relaxEdges edges state).ret.DistanceDecreases state := by
  induction edges generalizing state with
  | nil =>
      intro vertex distance distance_eq
      exact ⟨distance, distance_eq, le_rfl⟩
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.ret_bind]
      exact (induction (relaxOne state edge)).trans
        (relaxOne_distanceDecreases state edge)

theorem relaxEdges_edge_bound {n : Nat} (edges : List (Edge n))
    (state : State n) (edge : Edge n) (edge_mem : edge ∈ edges)
    (sourceDistance : Int)
    (source_eq : state.distance.get edge.source = some sourceDistance) :
    ∃ targetDistance,
      (relaxEdges edges state).ret.distance.get edge.target = some targetDistance ∧
        targetDistance ≤ sourceDistance + edge.weight := by
  induction edges generalizing state sourceDistance with
  | nil => simp at edge_mem
  | cons head rest induction =>
      simp only [List.mem_cons] at edge_mem
      simp only [relaxEdges, TimeM.ret_bind]
      rcases edge_mem with rfl | edge_mem
      · obtain ⟨afterHeadDistance, after_head_eq, after_head_le⟩ :=
          relaxOne_edge_bound state edge sourceDistance source_eq
        obtain ⟨finalDistance, final_eq, final_le⟩ :=
          relaxEdges_distanceDecreases rest (relaxOne state edge) edge.target
            afterHeadDistance after_head_eq
        exact ⟨finalDistance, final_eq, final_le.trans after_head_le⟩
      · obtain ⟨afterHeadSource, after_head_source_eq, after_head_source_le⟩ :=
          relaxOne_distanceDecreases state head edge.source sourceDistance source_eq
        obtain ⟨finalDistance, final_eq, final_le⟩ :=
          induction (relaxOne state head) edge_mem afterHeadSource after_head_source_eq
        exact ⟨finalDistance, final_eq, by omega⟩

theorem relaxEdges_lastUpdatedImprovedFrom {n : Nat} (edges : List (Edge n))
    {origin state : State n} (decreases : state.DistanceDecreases origin)
    (improved : state.LastUpdatedImprovedFrom origin) :
    (relaxEdges edges state).ret.LastUpdatedImprovedFrom origin := by
  induction edges generalizing state with
  | nil => simpa [relaxEdges] using improved
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.ret_bind]
      have head_decreases :=
        (relaxOne_distanceDecreases state edge).trans decreases
      exact induction head_decreases
        (relaxOne_lastUpdatedImprovedFrom decreases improved edge)

theorem relaxEdges_lastUpdated_improves_initial {n : Nat}
    (edges : List (Edge n)) (state : State n) (initial_none : state.lastUpdated = none) :
    (relaxEdges edges state).ret.LastUpdatedImprovedFrom state := by
  apply relaxEdges_lastUpdatedImprovedFrom edges
  · intro vertex distance distance_eq
    exact ⟨distance, distance_eq, le_rfl⟩
  · intro target updated
    rw [initial_none] at updated
    contradiction

theorem relaxEdges_boundsPaths_succ {n : Nat} (edges : List (Edge n))
    (source : Fin n) (steps : Nat) {state : State n}
    (bounds : state.BoundsPaths edges source steps) :
    (relaxEdges edges state).ret.BoundsPaths edges source (steps + 1) := by
  intro target path path_valid length_le
  induction path using List.reverseRecOn with
  | nil =>
      obtain ⟨oldDistance, old_eq, old_le⟩ :=
        bounds target [] path_valid (Nat.zero_le steps)
      obtain ⟨newDistance, new_eq, new_le⟩ :=
        relaxEdges_distanceDecreases edges state target oldDistance old_eq
      exact ⟨newDistance, new_eq, new_le.trans old_le⟩
  | append_singleton path edge _ =>
      obtain ⟨prefix_valid, edge_mem, edge_target⟩ :=
        isWeightedPath_append_edge_iff.mp path_valid
      have prefix_length : path.length ≤ steps := by
        simp only [List.length_append, List.length_singleton] at length_le
        omega
      obtain ⟨sourceDistance, source_eq, source_le⟩ :=
        bounds edge.source path prefix_valid prefix_length
      obtain ⟨targetDistance, target_eq, target_le⟩ :=
        relaxEdges_edge_bound edges state edge edge_mem sourceDistance source_eq
      subst target
      refine ⟨targetDistance, target_eq, ?_⟩
      rw [pathWeight_append_edge]
      omega

theorem relaxEdges_ordinalsBound {n : Nat} (edges : List (Edge n))
    {state : State n} (ordinals : state.OrdinalsBound) :
    (relaxEdges edges state).ret.OrdinalsBound := by
  induction edges generalizing state with
  | nil => simpa [relaxEdges] using ordinals
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.ret_bind]
      exact induction (relaxOne_ordinalsBound ordinals edge)

theorem relaxEdges_currentSnapshotsValid {n : Nat} (edges : List (Edge n))
    {state : State n} (valid : state.CurrentSnapshotsValid)
    (ordinals : state.OrdinalsBound) :
    (relaxEdges edges state).ret.CurrentSnapshotsValid := by
  induction edges generalizing state with
  | nil => simpa [relaxEdges] using valid
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.ret_bind]
      exact induction (relaxOne_currentSnapshotsValid valid ordinals edge)
        (relaxOne_ordinalsBound ordinals edge)

theorem relaxEdges_rooted {n : Nat} {source : Fin n}
    (edges : List (Edge n)) {state : State n} (rooted : state.Rooted source) :
    (relaxEdges edges state).ret.Rooted source := by
  induction edges generalizing state with
  | nil => simpa [relaxEdges] using rooted
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.ret_bind]
      exact induction (relaxOne_rooted rooted edge)

theorem relaxEdges_predecessorsFrom {n : Nat} {allEdges : List (Edge n)}
    (processed : List (Edge n)) {state : State n}
    (from_edges : state.PredecessorsFrom allEdges)
    (processed_mem : ∀ edge ∈ processed, edge ∈ allEdges) :
    (relaxEdges processed state).ret.PredecessorsFrom allEdges := by
  induction processed generalizing state with
  | nil => simpa [relaxEdges] using from_edges
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.ret_bind]
      exact induction
        (relaxOne_predecessorsFrom from_edges edge (processed_mem edge (by simp)))
        (fun item item_mem => processed_mem item (by simp [item_mem]))

theorem relaxEdges_discoveryValid {n : Nat} {allEdges : List (Edge n)}
    {source : Fin n} (processed : List (Edge n)) {state : State n}
    (valid : state.DiscoveryValid allEdges source)
    (processed_mem : ∀ edge ∈ processed, edge ∈ allEdges) :
    (relaxEdges processed state).ret.DiscoveryValid allEdges source := by
  induction processed generalizing state with
  | nil => simpa [relaxEdges] using valid
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.ret_bind]
      exact induction
        (relaxOne_discoveryValid valid edge (processed_mem edge (by simp)))
        (fun item item_mem => processed_mem item (by simp [item_mem]))

theorem relaxEdges_initial_none_of_final_none {n : Nat}
    (edges : List (Edge n)) (state : State n)
    (final_none : (relaxEdges edges state).ret.lastUpdated = none) :
    state.lastUpdated = none := by
  induction edges generalizing state with
  | nil => simpa [relaxEdges] using final_none
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.ret_bind] at final_none
      have after_none := induction (relaxOne state edge) final_none
      by_contra before_not_none
      exact relaxOne_lastUpdated_ne_none state edge before_not_none after_none

theorem relaxEdges_eq_self_and_stable_of_final_none {n : Nat}
    (edges : List (Edge n)) (state : State n)
    (final_none : (relaxEdges edges state).ret.lastUpdated = none) :
    (relaxEdges edges state).ret = state ∧ ∀ edge ∈ edges, state.EdgeStable edge := by
  induction edges generalizing state with
  | nil => simp [relaxEdges]
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.ret_bind] at final_none ⊢
      have after_none : (relaxOne state edge).lastUpdated = none :=
        relaxEdges_initial_none_of_final_none rest (relaxOne state edge) final_none
      obtain ⟨tail_eq, tail_stable⟩ := induction (relaxOne state edge) final_none
      obtain ⟨head_eq, head_stable⟩ :=
        relaxOne_eq_self_and_stable_of_lastUpdated_none state edge after_none
      rw [head_eq] at tail_eq tail_stable
      rw [head_eq]
      exact ⟨tail_eq, by
        intro item item_mem
        simp only [List.mem_cons] at item_mem
        rcases item_mem with rfl | item_mem
        · exact head_stable
        · exact tail_stable item item_mem⟩

theorem stable_path_bound {n : Nat} {edges : List (Edge n)}
    {state : State n} (stable : ∀ edge ∈ edges, state.EdgeStable edge)
    {source target : Fin n} {path : List (Edge n)}
    (path_valid : IsWeightedPath edges source target path)
    {sourceDistance : Int} (source_distance : state.distance.get source = some sourceDistance) :
    ∃ targetDistance,
      state.distance.get target = some targetDistance ∧
        targetDistance ≤ sourceDistance + pathWeight path := by
  induction path generalizing source sourceDistance with
  | nil =>
      have source_target : source = target := path_valid.2.2
      subst target
      exact ⟨sourceDistance, source_distance, by simp [pathWeight]⟩
  | cons edge rest induction =>
      have edge_mem : edge ∈ edges := path_valid.1 edge (by simp)
      have edge_source : edge.source = source := path_valid.2.2.1
      have stable_edge := stable edge edge_mem sourceDistance (edge_source ▸ source_distance)
      obtain ⟨middleDistance, middle_distance, middle_le⟩ := stable_edge
      obtain ⟨targetDistance, target_distance, target_le⟩ :=
        induction (isWeightedPath_tail path_valid) middle_distance
      refine ⟨targetDistance, target_distance, ?_⟩
      simp only [pathWeight, List.map_cons, List.sum_cons]
      rw [show (List.map Edge.weight rest).sum = pathWeight rest by rfl]
      omega

theorem stable_closed_path_nonnegative {n : Nat} {edges : List (Edge n)}
    {state : State n} (stable : ∀ edge ∈ edges, state.EdgeStable edge)
    {base : Fin n} {path : List (Edge n)}
    (path_valid : IsWeightedPath edges base base path)
    {distance : Int} (base_distance : state.distance.get base = some distance) :
    0 ≤ pathWeight path := by
  obtain ⟨targetDistance, target_distance, target_le⟩ :=
    stable_path_bound stable path_valid base_distance
  have target_eq : targetDistance = distance :=
    Option.some.inj (target_distance.symm.trans base_distance)
  subst targetDistance
  omega

def State.SourceNonpositive {n : Nat} (source : Fin n) (state : State n) : Prop :=
  ∃ distance, state.distance.get source = some distance ∧ distance ≤ 0

theorem initialState_sourceNonpositive {n : Nat} (source : Fin n) :
    (initialState source).SourceNonpositive source := by
  refine ⟨0, ?_, by omega⟩
  simp [initialState, Vector.get]
  apply Fin.ext
  rfl

theorem relaxOne_sourceNonpositive {n : Nat} {source : Fin n}
    {state : State n} (nonpositive : state.SourceNonpositive source) (edge : Edge n) :
    (relaxOne state edge).SourceNonpositive source := by
  obtain ⟨sourceValue, source_eq, source_le⟩ := nonpositive
  cases edge_source_eq : state.distance.get edge.source with
  | none => simpa [relaxOne, edge_source_eq] using ⟨sourceValue, source_eq, source_le⟩
  | some edgeSourceValue =>
      cases target_eq : state.distance.get edge.target with
      | none =>
          have target_ne_source : edge.target ≠ source := by
            intro target_source
            subst target_source
            simp [source_eq] at target_eq
          refine ⟨sourceValue, ?_, source_le⟩
          simp only [relaxOne, edge_source_eq, target_eq]
          change (state.distance.set edge.target (some (edgeSourceValue + edge.weight))).get
            source = some sourceValue
          rwa [vector_get_set_of_ne state.distance target_ne_source.symm]
      | some targetValue =>
          by_cases improves : edgeSourceValue + edge.weight < targetValue
          · by_cases target_source : edge.target = source
            · subst target_source
              have target_value_eq : targetValue = sourceValue :=
                Option.some.inj (target_eq.symm.trans source_eq)
              subst targetValue
              refine ⟨edgeSourceValue + edge.weight, ?_, by omega⟩
              simp [relaxOne, edge_source_eq, target_eq, improves, State.install,
                vector_get_set_same]
            · refine ⟨sourceValue, ?_, source_le⟩
              simp only [relaxOne, edge_source_eq, target_eq, improves, ↓reduceIte]
              change (state.distance.set edge.target (some (edgeSourceValue + edge.weight))).get
                source = some sourceValue
              rwa [vector_get_set_of_ne state.distance (fun equal => target_source equal.symm)]
          · simpa [relaxOne, edge_source_eq, target_eq, improves] using
              ⟨sourceValue, source_eq, source_le⟩

theorem relaxEdges_realizes {n : Nat} {edges : List (Edge n)} {source : Fin n}
    (processed : List (Edge n)) (state : State n) (realizes : state.Realizes edges source)
    (processed_mem : ∀ edge ∈ processed, edge ∈ edges) :
    (relaxEdges processed state).ret.Realizes edges source := by
  induction processed generalizing state with
  | nil => simpa [relaxEdges] using realizes
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.ret_bind]
      exact induction (relaxOne state edge)
        (relaxOne_realizes realizes (processed_mem edge (by simp)))
        (fun item item_mem => processed_mem item (by simp [item_mem]))

theorem relaxEdges_sourceNonpositive {n : Nat} {source : Fin n}
    (edges : List (Edge n)) (state : State n) (nonpositive : state.SourceNonpositive source) :
    (relaxEdges edges state).ret.SourceNonpositive source := by
  induction edges generalizing state with
  | nil => simpa [relaxEdges] using nonpositive
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.ret_bind]
      exact induction _ (relaxOne_sourceNonpositive nonpositive edge)

def runPasses {n : Nat} (edges : List (Edge n)) :
    Nat → State n → TimeM Cost (State n)
  | 0, state => pure state
  | passes + 1, state => do
      let state ← relaxEdges edges state
      runPasses edges passes state

theorem runPasses_distanceDecreases {n : Nat} (edges : List (Edge n))
    (passes : Nat) (state : State n) :
    (runPasses edges passes state).ret.DistanceDecreases state := by
  induction passes generalizing state with
  | zero =>
      intro vertex distance distance_eq
      exact ⟨distance, distance_eq, le_rfl⟩
  | succ passes induction =>
      simp only [runPasses, TimeM.ret_bind]
      exact (induction (relaxEdges edges state).ret).trans
        (relaxEdges_distanceDecreases edges state)

theorem runPasses_boundsPaths {n : Nat} (edges : List (Edge n))
    (source : Fin n) (passes steps : Nat) {state : State n}
    (bounds : state.BoundsPaths edges source steps) :
    (runPasses edges passes state).ret.BoundsPaths edges source (steps + passes) := by
  induction passes generalizing state steps with
  | zero => simpa [runPasses] using bounds
  | succ passes induction =>
      simp only [runPasses, TimeM.ret_bind]
      have after_pass := relaxEdges_boundsPaths_succ edges source steps bounds
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        induction (steps + 1) after_pass

theorem runPasses_initial_boundsPaths {n : Nat} (edges : List (Edge n))
    (source : Fin n) (passes : Nat) :
    (runPasses edges passes (initialState source)).ret.BoundsPaths edges source passes := by
  simpa using runPasses_boundsPaths edges source passes 0
    (initialState_boundsPaths edges source)

theorem runPasses_ordinalsBound {n : Nat} (edges : List (Edge n))
    (passes : Nat) {state : State n} (ordinals : state.OrdinalsBound) :
    (runPasses edges passes state).ret.OrdinalsBound := by
  induction passes generalizing state with
  | zero => simpa [runPasses] using ordinals
  | succ passes induction =>
      simp only [runPasses, TimeM.ret_bind]
      exact induction (relaxEdges_ordinalsBound edges ordinals)

theorem runPasses_currentSnapshotsValid {n : Nat} (edges : List (Edge n))
    (passes : Nat) {state : State n} (valid : state.CurrentSnapshotsValid)
    (ordinals : state.OrdinalsBound) :
    (runPasses edges passes state).ret.CurrentSnapshotsValid := by
  induction passes generalizing state with
  | zero => simpa [runPasses] using valid
  | succ passes induction =>
      simp only [runPasses, TimeM.ret_bind]
      exact induction (relaxEdges_currentSnapshotsValid edges valid ordinals)
        (relaxEdges_ordinalsBound edges ordinals)

theorem runPasses_rooted {n : Nat} (edges : List (Edge n))
    {source : Fin n} (passes : Nat) {state : State n} (rooted : state.Rooted source) :
    (runPasses edges passes state).ret.Rooted source := by
  induction passes generalizing state with
  | zero => simpa [runPasses] using rooted
  | succ passes induction =>
      simp only [runPasses, TimeM.ret_bind]
      exact induction (relaxEdges_rooted edges rooted)

theorem runPasses_predecessorsFrom {n : Nat} (edges : List (Edge n))
    (passes : Nat) {state : State n} (from_edges : state.PredecessorsFrom edges) :
    (runPasses edges passes state).ret.PredecessorsFrom edges := by
  induction passes generalizing state with
  | zero => simpa [runPasses] using from_edges
  | succ passes induction =>
      simp only [runPasses, TimeM.ret_bind]
      exact induction (relaxEdges_predecessorsFrom edges from_edges (fun _ => id))

theorem runPasses_discoveryValid {n : Nat} (edges : List (Edge n))
    (source : Fin n) (passes : Nat) {state : State n}
    (valid : state.DiscoveryValid edges source) :
    (runPasses edges passes state).ret.DiscoveryValid edges source := by
  induction passes generalizing state with
  | zero => simpa [runPasses] using valid
  | succ passes induction =>
      simp only [runPasses, TimeM.ret_bind]
      exact induction (relaxEdges_discoveryValid edges valid (fun _ => id))

theorem runPasses_realizes {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (passes : Nat) (state : State n) (realizes : state.Realizes edges source) :
    (runPasses edges passes state).ret.Realizes edges source := by
  induction passes generalizing state with
  | zero => simpa [runPasses] using realizes
  | succ passes induction =>
      simp only [runPasses, TimeM.ret_bind]
      exact induction _ (relaxEdges_realizes edges state realizes (fun _ => id))

theorem runPasses_sourceNonpositive {n : Nat} (edges : List (Edge n))
    (source : Fin n) (passes : Nat) (state : State n)
    (nonpositive : state.SourceNonpositive source) :
    (runPasses edges passes state).ret.SourceNonpositive source := by
  induction passes generalizing state with
  | zero => simpa [runPasses] using nonpositive
  | succ passes induction =>
      simp only [runPasses, TimeM.ret_bind]
      exact induction _ (relaxEdges_sourceNonpositive edges state nonpositive)


end Internal

end Cslib.Algorithms.Lean.BellmanFord
