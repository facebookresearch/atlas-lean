/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Basic

import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Relaxation
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Extraction

/-! # Bellman-Ford implementation and semantic correctness -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BellmanFord

namespace Internal

def followPredecessorsAux {n : Nat} (source : Fin n)
    (predecessor : Vector (Option (Edge n)) n) :
    Nat → Fin n → List (Edge n) → Option (List (Edge n))
  | 0, current, suffix => if current = source then some suffix else none
  | fuel + 1, current, suffix =>
      if current = source then
        some suffix
      else
        match predecessor.get current with
        | none => none
        | some edge => followPredecessorsAux source predecessor fuel edge.source (edge :: suffix)

def followPredecessors {n : Nat} (source : Fin n)
    (predecessor : Vector (Option (Edge n)) n) (fuel : Nat) (current : Fin n) :
    Option (List (Edge n)) :=
  followPredecessorsAux source predecessor fuel current []

theorem followPredecessorsAux_eq {n : Nat} (source : Fin n)
    (predecessor : Vector (Option (Edge n)) n) :
    ∀ (fuel : Nat) (current : Fin n) (suffix : List (Edge n)),
      followPredecessorsAux source predecessor fuel current suffix =
        (followPredecessors source predecessor fuel current).map (· ++ suffix) := by
  intro fuel
  induction fuel with
  | zero =>
      intro current suffix
      by_cases current_source : current = source
      · simp [followPredecessors, followPredecessorsAux, current_source]
      · simp [followPredecessors, followPredecessorsAux, current_source]
  | succ fuel induction =>
      intro current suffix
      by_cases current_source : current = source
      · simp [followPredecessors, followPredecessorsAux, current_source]
      · cases predecessor_eq : predecessor.get current with
        | none => simp [followPredecessors, followPredecessorsAux, current_source,
            predecessor_eq]
        | some edge =>
            have e1 : followPredecessors source predecessor (fuel + 1) current =
                followPredecessorsAux source predecessor fuel edge.source [edge] := by
              simp [followPredecessors, followPredecessorsAux, current_source,
                predecessor_eq]
            have e2 : followPredecessorsAux source predecessor (fuel + 1) current suffix =
                followPredecessorsAux source predecessor fuel edge.source
                  (edge :: suffix) := by
              simp [followPredecessorsAux, current_source, predecessor_eq]
            rw [e2, e1, induction edge.source [edge],
              induction edge.source (edge :: suffix)]
            cases tail : followPredecessors source predecessor fuel edge.source with
            | none => rfl
            | some path => simp [List.append_assoc]

theorem followPredecessors_succ_of_ne {n : Nat} {source current : Fin n}
    (predecessor : Vector (Option (Edge n)) n) (fuel : Nat)
    (current_source : current ≠ source) {edge : Edge n}
    (predecessor_eq : predecessor.get current = some edge) :
    followPredecessors source predecessor (fuel + 1) current =
      (followPredecessors source predecessor fuel edge.source).map (· ++ [edge]) := by
  have e1 : followPredecessors source predecessor (fuel + 1) current =
      followPredecessorsAux source predecessor fuel edge.source [edge] := by
    simp [followPredecessors, followPredecessorsAux, current_source, predecessor_eq]
  rw [e1, followPredecessorsAux_eq]

@[simp]
theorem followPredecessors_source {n : Nat} (source : Fin n)
    (predecessor : Vector (Option (Edge n)) n) (fuel : Nat) :
    followPredecessors source predecessor fuel source = some [] := by
  cases fuel <;> simp [followPredecessors, followPredecessorsAux]

theorem pathTo?_eq_followPredecessors {n : Nat} (result : Distances n) (target : Fin n) :
    result.pathTo? target =
      followPredecessors result.source result.predecessor n target := by
  unfold Distances.pathTo?
  have equal : ∀ (fuel : Nat) (current : Fin n) (suffix : List (Edge n)),
      Distances.pathTo?.follow result current fuel suffix =
        (followPredecessors result.source result.predecessor fuel current).map
          (· ++ suffix) := by
    intro fuel
    induction fuel with
    | zero =>
        intro current suffix
        by_cases current_source : current = result.source
        · subst current
          simp [Distances.pathTo?.follow, followPredecessors, followPredecessorsAux]
        · simp [Distances.pathTo?.follow, followPredecessors, followPredecessorsAux,
            current_source]
    | succ fuel induction =>
        intro current suffix
        by_cases current_source : current = result.source
        · subst current
          simp [Distances.pathTo?.follow, followPredecessors, followPredecessorsAux]
        · cases predecessor_eq : result.predecessor.get current with
          | none => simp [Distances.pathTo?.follow, followPredecessors,
              followPredecessorsAux, current_source, predecessor_eq]
          | some edge =>
              have step := followPredecessors_succ_of_ne result.predecessor fuel
                current_source predecessor_eq
              have unfold : Distances.pathTo?.follow result current (fuel + 1) suffix =
                  Distances.pathTo?.follow result edge.source fuel (edge :: suffix) := by
                simp [Distances.pathTo?.follow, current_source, predecessor_eq]
              rw [step, unfold, induction edge.source (edge :: suffix)]
              cases tail : followPredecessors result.source result.predecessor fuel
                  edge.source with
              | none => rfl
              | some path => simp [List.append_assoc]
  have final := equal n target []
  simpa using final

theorem finish_distances_distance_eq {n : Nat} (edges : List (Edge n))
    (source : Fin n) (state : State n) (result : Distances n)
    (returns : (finish edges source state).ret = Result.distances result) :
    result.distance = state.distance := by
  let distanceOf : Result edges source → Vector (Option Int) n
    | .distances distances => distances.distance
    | .negativeCycle _ => state.distance
  have mapped := congrArg distanceOf returns
  cases updated_eq : state.lastUpdated with
  | none => simpa [finish, updated_eq, distanceOf, State.toDistances] using mapped.symm
  | some updated =>
      cases base_eq : (localizeCycle state.predecessor n updated).ret with
      | none =>
          simpa [finish, updated_eq, base_eq, distanceOf, State.toDistances] using mapped.symm
      | some base =>
          cases cycle_eq : (collectCycle state.predecessor base n base []).ret with
          | none =>
              simpa [finish, updated_eq, base_eq, cycle_eq, distanceOf,
                State.toDistances] using mapped.symm
          | some cycle =>
              cases prefix_eq :
                  (collectPrefix state.discoveryPredecessor source (n - 1) base []).ret with
              | none =>
                  simpa [finish, updated_eq, base_eq, cycle_eq, prefix_eq, distanceOf,
                    State.toDistances] using mapped.symm
              | some «prefix» =>
                  cases make_eq : makeWitness? edges source base «prefix» cycle with
                  | none =>
                      simpa [finish, updated_eq, base_eq, cycle_eq, prefix_eq, make_eq,
                        distanceOf, State.toDistances] using mapped.symm
                  | some witness =>
                      simp [finish, updated_eq, base_eq, cycle_eq, prefix_eq, make_eq] at returns

def beforeFinal {n : Nat} (edges : List (Edge n)) (source : Fin n) : State n :=
  { (runPasses edges (n - 1) (initialState source)).ret with lastUpdated := none }

def afterFinal {n : Nat} (edges : List (Edge n)) (source : Fin n) : State n :=
  (relaxEdges edges (beforeFinal edges source)).ret

theorem beforeFinal_boundsPaths {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (beforeFinal edges source).BoundsPaths edges source (n - 1) := by
  simpa [beforeFinal, State.BoundsPaths] using
    runPasses_initial_boundsPaths edges source (n - 1)

theorem afterFinal_currentSnapshotsValid {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (afterFinal edges source).CurrentSnapshotsValid := by
  apply relaxEdges_currentSnapshotsValid edges
  · simpa [beforeFinal, State.CurrentSnapshotsValid] using
      runPasses_currentSnapshotsValid edges (n - 1)
        (initialState_currentSnapshotsValid source) (initialState_ordinalsBound source)
  · simpa [beforeFinal, State.OrdinalsBound] using
      runPasses_ordinalsBound edges (n - 1) (initialState_ordinalsBound source)

theorem afterFinal_rooted {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (afterFinal edges source).Rooted source := by
  apply relaxEdges_rooted edges
  simpa [beforeFinal, State.Rooted] using
    runPasses_rooted edges (n - 1) (initialState_rooted source)

theorem afterFinal_predecessorsFrom {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (afterFinal edges source).PredecessorsFrom edges := by
  apply relaxEdges_predecessorsFrom edges
  · simpa [beforeFinal, State.PredecessorsFrom] using
      runPasses_predecessorsFrom edges (n - 1)
        (initialState_predecessorsFrom edges source)
  · exact fun _ => id

theorem afterFinal_discoveryValid {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (afterFinal edges source).DiscoveryValid edges source := by
  apply relaxEdges_discoveryValid edges
  · exact (runPasses_discoveryValid edges source (n - 1)
      (initialState_discoveryValid edges source)).resetLastUpdated
  · exact fun _ => id

theorem afterFinal_lastUpdatedImproved {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (afterFinal edges source).LastUpdatedImprovedFrom (beforeFinal edges source) := by
  exact relaxEdges_lastUpdated_improves_initial edges (beforeFinal edges source) rfl

theorem afterFinal_localizeCycle_some {n : Nat} (edges : List (Edge n))
    (source updated : Fin n)
    (final_updated : (afterFinal edges source).lastUpdated = some updated) :
    ∃ base,
      (localizeCycle (afterFinal edges source).predecessor n updated).ret = some base := by
  obtain ⟨finalDistance, final_distance, improved⟩ :=
    afterFinal_lastUpdatedImproved edges source updated final_updated
  cases localize_eq :
      (localizeCycle (afterFinal edges source).predecessor n updated).ret with
  | some base => exact ⟨base, rfl⟩
  | none =>
      obtain ⟨root, path, rootDistance, root_none, root_distance,
          path_valid, path_length, path_le⟩ :=
        localizeCycle_none_path (afterFinal_currentSnapshotsValid edges source)
          (afterFinal_predecessorsFrom edges source) n updated finalDistance
          final_distance localize_eq
      obtain ⟨root_source, root_zero⟩ :=
        afterFinal_rooted edges source root rootDistance root_distance root_none
      subst root
      subst rootDistance
      have length_le : path.length ≤ n - 1 := by omega
      obtain ⟨beforeDistance, before_distance, before_le⟩ :=
        beforeFinal_boundsPaths edges source updated path path_valid length_le
      rcases improved with before_none | ⟨oldDistance, before_old, final_lt⟩
      · rw [before_none] at before_distance
        contradiction
      · have old_eq : oldDistance = beforeDistance :=
          Option.some.inj (before_old.symm.trans before_distance)
        subst oldDistance
        have path_final_le : pathWeight path ≤ finalDistance := by
          simpa only [Int.sub_zero] using path_le
        omega

theorem afterFinal_collectCycle_some {n : Nat} (edges : List (Edge n))
    (source updated base : Fin n)
    (localizes :
      (localizeCycle (afterFinal edges source).predecessor n updated).ret = some base) :
    ∃ cycle,
      (collectCycle (afterFinal edges source).predecessor base n base []).ret =
        some cycle := by
  obtain ⟨period, period_pos, period_le, periodic, reads⟩ :=
    localizeCycle_periodic_of_ret_some
      (afterFinal edges source).predecessor updated base localizes
  exact collectCycle_some_of_reaches (afterFinal edges source).predecessor
    base base period n [] period_pos period_le periodic reads

theorem afterFinal_cycle_spec {n : Nat} (edges : List (Edge n))
    (source base : Fin n) (cycle : List (Edge n))
    (cycle_eq :
      (collectCycle (afterFinal edges source).predecessor base n base []).ret =
        some cycle) :
    IsWeightedPath edges base base cycle ∧ cycle ≠ [] ∧
      (cycle.map Edge.source).Nodup ∧ pathWeight cycle < 0 := by
  obtain ⟨cycle_valid, cycle_nonempty, cycle_predecessors⟩ :=
    collectCycle_spec (afterFinal_currentSnapshotsValid edges source)
      (afterFinal_predecessorsFrom edges source) base n base [] cycle
      (by simp [IsWeightedPath]) (by simp) cycle_eq
  exact ⟨cycle_valid, cycle_nonempty,
    collectCycle_sources_nodup (afterFinal edges source).predecessor base n cycle cycle_eq,
    predecessor_cycle_negative (afterFinal_currentSnapshotsValid edges source)
      (afterFinal_predecessorsFrom edges source) cycle_valid cycle_nonempty
      cycle_predecessors⟩

theorem afterFinal_collectPrefix_some {n : Nat} (edges : List (Edge n))
    (source updated base : Fin n)
    (final_updated : (afterFinal edges source).lastUpdated = some updated)
    (localizes :
      (localizeCycle (afterFinal edges source).predecessor n updated).ret = some base) :
    ∃ path,
      (collectPrefix (afterFinal edges source).discoveryPredecessor source (n - 1) base []).ret =
        some path := by
  obtain ⟨updatedDistance, updated_distance, _⟩ :=
    afterFinal_lastUpdatedImproved edges source updated final_updated
  obtain ⟨baseDistance, base_distance⟩ :=
    localizeCycle_finite_of_ret_some (afterFinal_currentSnapshotsValid edges source)
      (afterFinal_predecessorsFrom edges source) n updated base updatedDistance
      updated_distance localizes
  exact collectPrefix_some_of_finite (afterFinal_discoveryValid edges source)
    base baseDistance base_distance

theorem afterFinal_prefix_spec {n : Nat} (edges : List (Edge n))
    (source base : Fin n) (path : List (Edge n))
    (path_eq :
      (collectPrefix (afterFinal edges source).discoveryPredecessor source (n - 1) base []).ret =
        some path) :
    IsWeightedPath edges source base path ∧ (pathVertices source path).Nodup ∧
      path.length < n := by
  obtain ⟨path_valid, path_predecessors⟩ :=
    collectPrefix_spec (target := base) (afterFinal_discoveryValid edges source)
      (n - 1) base [] path
      (by simp [IsWeightedPath]) (by simp) path_eq
  have path_nodup := discovery_path_nodup (afterFinal_discoveryValid edges source)
    path_valid path_predecessors
  have length_le := path_nodup.length_le_card
  simp [pathVertices] at length_le
  exact ⟨path_valid, path_nodup, by omega⟩

theorem afterFinal_finish_negativeCycle_of_updated {n : Nat}
    (edges : List (Edge n)) (source updated : Fin n)
    (final_updated : (afterFinal edges source).lastUpdated = some updated) :
    ∃ witness,
      (finish edges source (afterFinal edges source)).ret =
        Result.negativeCycle witness := by
  obtain ⟨base, localizes⟩ :=
    afterFinal_localizeCycle_some edges source updated final_updated
  obtain ⟨cycle, cycle_eq⟩ := afterFinal_collectCycle_some edges source updated base localizes
  obtain ⟨path, path_eq⟩ :=
    afterFinal_collectPrefix_some edges source updated base final_updated localizes
  obtain ⟨cycle_valid, cycle_nonempty, cycle_simple, cycle_negative⟩ :=
    afterFinal_cycle_spec edges source base cycle cycle_eq
  obtain ⟨path_valid, path_simple, _⟩ :=
    afterFinal_prefix_spec edges source base path path_eq
  obtain ⟨witness, witness_eq⟩ :=
    makeWitness_some_of_spec edges source base path cycle path_valid path_simple
      cycle_valid cycle_nonempty cycle_simple cycle_negative
  exact ⟨witness, by
    simp [finish, final_updated, localizes, cycle_eq, path_eq, witness_eq]⟩

theorem afterFinal_realizes {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    (afterFinal edges source).Realizes edges source := by
  apply relaxEdges_realizes edges (beforeFinal edges source)
  · exact runPasses_realizes edges source (n - 1) (initialState source)
      (initialState_realizes edges source)
  · exact fun _ => id

theorem afterFinal_sourceNonpositive {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (afterFinal edges source).SourceNonpositive source := by
  apply relaxEdges_sourceNonpositive edges (beforeFinal edges source)
  exact runPasses_sourceNonpositive edges source (n - 1) (initialState source)
    (initialState_sourceNonpositive source)

theorem afterFinal_stable_of_none {n : Nat} (edges : List (Edge n))
    (source : Fin n) (final_none : (afterFinal edges source).lastUpdated = none) :
    ∀ edge ∈ edges, (afterFinal edges source).EdgeStable edge := by
  obtain ⟨final_eq, stable⟩ :=
    relaxEdges_eq_self_and_stable_of_final_none edges (beforeFinal edges source) final_none
  change ∀ edge ∈ edges,
    ((relaxEdges edges (beforeFinal edges source)).ret).EdgeStable edge
  rw [final_eq]
  exact stable

theorem afterFinal_source_distance_zero_of_none {n : Nat} (edges : List (Edge n))
    (source : Fin n) (final_none : (afterFinal edges source).lastUpdated = none) :
    (afterFinal edges source).distance.get source = some 0 := by
  obtain ⟨sourceDistance, source_distance, source_le⟩ :=
    afterFinal_sourceNonpositive edges source
  obtain ⟨path, path_valid, path_weight⟩ :=
    afterFinal_realizes edges source source sourceDistance source_distance
  have path_nonnegative : 0 ≤ pathWeight path :=
    stable_closed_path_nonnegative (afterFinal_stable_of_none edges source final_none)
      path_valid source_distance
  have source_zero : sourceDistance = 0 := by omega
  simpa [source_zero] using source_distance

theorem afterFinal_minimal_of_none {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} (final_none : (afterFinal edges source).lastUpdated = none)
    {distance : Int} (distance_eq : (afterFinal edges source).distance.get target = some distance)
    {path : List (Edge n)} (path_valid : IsWeightedPath edges source target path) :
    distance ≤ pathWeight path := by
  obtain ⟨targetDistance, target_distance, target_le⟩ :=
    stable_path_bound (afterFinal_stable_of_none edges source final_none) path_valid
      (afterFinal_source_distance_zero_of_none edges source final_none)
  have target_eq : targetDistance = distance :=
    Option.some.inj (target_distance.symm.trans distance_eq)
  subst targetDistance
  simpa using target_le

theorem afterFinal_distance_eq_none_iff_of_none {n : Nat}
    {edges : List (Edge n)} {source target : Fin n}
    (final_none : (afterFinal edges source).lastUpdated = none) :
    (afterFinal edges source).distance.get target = none ↔
      ¬(toDirectedAdjacency edges).Reachable source target := by
  constructor
  · intro distance_none reachable
    obtain ⟨path, path_valid⟩ := reachable_iff_exists_isWeightedPath.mp reachable
    obtain ⟨targetDistance, target_distance, _⟩ :=
      stable_path_bound (afterFinal_stable_of_none edges source final_none) path_valid
        (afterFinal_source_distance_zero_of_none edges source final_none)
    rw [distance_none] at target_distance
    contradiction
  · intro not_reachable
    cases distance_eq : (afterFinal edges source).distance.get target with
    | none => rfl
    | some distance =>
        exfalso
        apply not_reachable
        obtain ⟨path, path_valid, _⟩ :=
          afterFinal_realizes edges source target distance distance_eq
        exact reachable_iff_exists_isWeightedPath.mpr ⟨path, path_valid⟩

theorem afterFinal_no_negativeCycle_of_none {n : Nat}
    (edges : List (Edge n)) (source : Fin n)
    (final_none : (afterFinal edges source).lastUpdated = none) :
    ¬HasReachableNegativeCycle edges source := by
  rintro ⟨witness⟩
  obtain ⟨baseDistance, base_distance, _⟩ :=
    stable_path_bound (afterFinal_stable_of_none edges source final_none)
      witness.prefix_valid (afterFinal_source_distance_zero_of_none edges source final_none)
  have cycle_nonnegative :=
    stable_closed_path_nonnegative (afterFinal_stable_of_none edges source final_none)
      witness.cycle_valid base_distance
  exact (not_lt_of_ge cycle_nonnegative) witness.cycle_negative

theorem afterFinal_predecessor_not_strict_of_none {n : Nat}
    {edges : List (Edge n)} {source target : Fin n} {edge : Edge n}
    (final_none : (afterFinal edges source).lastUpdated = none)
    (predecessor_eq : (afterFinal edges source).predecessor.get target = some edge) :
    ¬(afterFinal edges source).PredecessorStrict edge := by
  rintro ⟨sourceDistance, targetDistance, source_eq, target_eq, strict⟩
  obtain ⟨edge_mem, edge_target, _, _, _, _, _⟩ :=
    (afterFinal edges source).predecessor_step
      (afterFinal_currentSnapshotsValid edges source)
      (afterFinal_predecessorsFrom edges source) predecessor_eq
  obtain ⟨stableTarget, stable_target_eq, upper⟩ :=
    afterFinal_stable_of_none edges source final_none edge edge_mem sourceDistance source_eq
  have target_value : stableTarget = targetDistance :=
    Option.some.inj (stable_target_eq.symm.trans (edge_target ▸ target_eq))
  subst stableTarget
  omega

theorem afterFinal_predecessor_of_finite {n : Nat}
    {edges : List (Edge n)} {source current : Fin n} {sourceEdge : Edge n}
    (source_predecessor :
      (afterFinal edges source).predecessor.get source = some sourceEdge)
    (distance : Int)
    (current_distance : (afterFinal edges source).distance.get current = some distance) :
    ∃ edge, (afterFinal edges source).predecessor.get current = some edge := by
  cases predecessor_eq : (afterFinal edges source).predecessor.get current with
  | some edge => exact ⟨edge, rfl⟩
  | none =>
      obtain ⟨current_source, _⟩ :=
        afterFinal_rooted edges source current distance current_distance predecessor_eq
      subst current
      rw [source_predecessor] at predecessor_eq
      contradiction

theorem afterFinal_predecessor_trace {n : Nat} {edges : List (Edge n)}
    {source : Fin n} {sourceEdge : Edge n}
    (final_none : (afterFinal edges source).lastUpdated = none)
    (source_predecessor :
      (afterFinal edges source).predecessor.get source = some sourceEdge)
    (fuel : Nat) (current : Fin n) (distance : Int)
    (current_distance : (afterFinal edges source).distance.get current = some distance) :
    ∃ ordinal,
      (afterFinal edges source).predecessorUpdateOrdinal.get current = some ordinal ∧
        let vertices := current ::
          vertexTrace (predecessorVertex (afterFinal edges source).predecessor) fuel current
        vertices.Nodup ∧
          ∀ vertex ∈ vertices,
            ∃ vertexOrdinal,
              (afterFinal edges source).predecessorUpdateOrdinal.get vertex =
                some vertexOrdinal ∧ vertexOrdinal ≤ ordinal := by
  induction fuel generalizing current distance with
  | zero =>
      obtain ⟨edge, predecessor_eq⟩ :=
        afterFinal_predecessor_of_finite source_predecessor distance current_distance
      obtain ⟨_, _, ordinal, _, _, _, ordinal_eq, _, _, _, _, _, _, _⟩ :=
        afterFinal_currentSnapshotsValid edges source current edge predecessor_eq
      refine ⟨ordinal, ordinal_eq, ?_⟩
      dsimp [vertexTrace]
      exact ⟨by simp, by
        intro vertex vertex_mem
        simp only [List.mem_singleton] at vertex_mem
        subst vertex
        exact ⟨ordinal, ordinal_eq, le_rfl⟩⟩
  | succ fuel induction =>
      obtain ⟨edge, predecessor_eq⟩ :=
        afterFinal_predecessor_of_finite source_predecessor distance current_distance
      obtain ⟨_, _, sourceDistance, _, source_distance, _, _⟩ :=
        (afterFinal edges source).predecessor_step
          (afterFinal_currentSnapshotsValid edges source)
          (afterFinal_predecessorsFrom edges source) predecessor_eq
      obtain ⟨sourcePredecessor, source_predecessor_eq⟩ :=
        afterFinal_predecessor_of_finite source_predecessor sourceDistance source_distance
      obtain ⟨sourceOrdinal, currentOrdinal, source_ordinal_eq, current_ordinal_eq,
          ordinal_lt⟩ :=
        (afterFinal edges source).predecessor_ordinal_lt_of_not_strict
          (afterFinal_currentSnapshotsValid edges source) predecessor_eq
          source_predecessor_eq
          (afterFinal_predecessor_not_strict_of_none final_none predecessor_eq)
      obtain ⟨tailOrdinal, tail_ordinal_eq, tail_nodup, tail_bound⟩ :=
        induction edge.source sourceDistance source_distance
      have tail_ordinal_value : tailOrdinal = sourceOrdinal :=
        Option.some.inj (tail_ordinal_eq.symm.trans source_ordinal_eq)
      subst tailOrdinal
      let tailVertices := edge.source ::
        vertexTrace (predecessorVertex (afterFinal edges source).predecessor) fuel edge.source
      have current_not_tail : current ∉ tailVertices := by
        intro current_mem
        obtain ⟨vertexOrdinal, vertex_ordinal_eq, vertex_ordinal_le⟩ :=
          tail_bound current current_mem
        have vertex_value : vertexOrdinal = currentOrdinal :=
          Option.some.inj (vertex_ordinal_eq.symm.trans current_ordinal_eq)
        subst vertexOrdinal
        omega
      refine ⟨currentOrdinal, current_ordinal_eq, ?_⟩
      dsimp only
      rw [vertexTrace, predecessorVertex, predecessor_eq]
      change (current :: tailVertices).Nodup ∧ _
      refine ⟨List.nodup_cons.mpr ⟨current_not_tail, tail_nodup⟩, ?_⟩
      intro vertex vertex_mem
      simp only [List.mem_cons] at vertex_mem
      rcases vertex_mem with rfl | vertex_mem
      · exact ⟨currentOrdinal, current_ordinal_eq, le_rfl⟩
      · obtain ⟨vertexOrdinal, vertex_ordinal_eq, vertex_ordinal_le⟩ :=
          tail_bound vertex (by simpa [tailVertices] using vertex_mem)
        exact ⟨vertexOrdinal, vertex_ordinal_eq, vertex_ordinal_le.trans ordinal_lt.le⟩

theorem afterFinal_source_predecessor_none_of_none {n : Nat}
    (edges : List (Edge n)) (source : Fin n)
    (final_none : (afterFinal edges source).lastUpdated = none) :
    (afterFinal edges source).predecessor.get source = none := by
  cases source_predecessor : (afterFinal edges source).predecessor.get source with
  | none => rfl
  | some sourceEdge =>
      have source_distance := afterFinal_source_distance_zero_of_none edges source final_none
      obtain ⟨_, _, vertices_nodup, _⟩ :=
        afterFinal_predecessor_trace final_none source_predecessor n source 0 source_distance
      have length_le := vertices_nodup.length_le_card
      rw [vertexTrace_eq_ofFn] at length_le
      simp only [List.length_cons, List.length_ofFn, Fintype.card_fin] at length_le
      omega

def predecessorOrdinalValue {n : Nat} (state : State n) (vertex : Fin n) : Nat :=
  (state.predecessorUpdateOrdinal.get vertex).getD 0

theorem afterFinal_path_target_rank_chain {n : Nat} {edges : List (Edge n)}
    {root start target : Fin n} (final_none : (afterFinal edges root).lastUpdated = none)
    {path : List (Edge n)} (path_valid : IsWeightedPath edges start target path)
    (path_predecessors : ∀ edge ∈ path,
      (afterFinal edges root).predecessor.get edge.target = some edge) :
    ((path.map Edge.target).map (predecessorOrdinalValue (afterFinal edges root))).IsChain
      (fun left right => left < right) := by
  induction path generalizing start with
  | nil => simp
  | cons first rest induction =>
      cases rest with
      | nil => simp
      | cons second tail =>
          have first_predecessor := path_predecessors first (by simp)
          have second_predecessor := path_predecessors second (by simp)
          have connects : first.target = second.source := path_valid.2.1.rel
          obtain ⟨firstOrdinal, secondOrdinal, first_ordinal_eq, second_ordinal_eq,
              ordinal_lt⟩ :=
            (afterFinal edges root).predecessor_ordinal_lt_of_not_strict
              (afterFinal_currentSnapshotsValid edges root) second_predecessor
              (connects ▸ first_predecessor)
              (afterFinal_predecessor_not_strict_of_none final_none second_predecessor)
          have tail_chain := induction (isWeightedPath_tail path_valid)
            (fun item item_mem => path_predecessors item (by simp [item_mem]))
          change List.IsChain (fun left right : Nat => left < right)
            (predecessorOrdinalValue (afterFinal edges root) first.target ::
              (List.map Edge.target (second :: tail)).map
                (predecessorOrdinalValue (afterFinal edges root)))
          apply List.IsChain.cons tail_chain
          intro value value_head
          have value_eq :
              value = predecessorOrdinalValue (afterFinal edges root) second.target := by
            simpa using value_head.symm
          subst value
          simp only [predecessorOrdinalValue]
          rw [connects, first_ordinal_eq, second_ordinal_eq]
          exact ordinal_lt

theorem afterFinal_predecessor_path_nodup {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} (final_none : (afterFinal edges source).lastUpdated = none)
    {path : List (Edge n)} (path_valid : IsWeightedPath edges source target path)
    (path_predecessors : ∀ edge ∈ path,
      (afterFinal edges source).predecessor.get edge.target = some edge) :
    (pathVertices source path).Nodup := by
  have chain := afterFinal_path_target_rank_chain final_none path_valid path_predecessors
  rw [List.isChain_iff_pairwise] at chain
  have rank_nodup : ((path.map Edge.target).map
      (predecessorOrdinalValue (afterFinal edges source))).Nodup :=
    chain.imp (fun less => Nat.ne_of_lt less)
  have targets_nodup : (path.map Edge.target).Nodup := rank_nodup.of_map _
  have source_not_targets : source ∉ path.map Edge.target := by
    intro source_mem
    obtain ⟨edge, edge_mem, edge_target⟩ := List.mem_map.mp source_mem
    have predecessor_eq := path_predecessors edge edge_mem
    have source_none := afterFinal_source_predecessor_none_of_none edges source final_none
    rw [edge_target, source_none] at predecessor_eq
    contradiction
  exact List.nodup_cons.mpr ⟨source_not_targets, targets_nodup⟩

theorem followPredecessors_core_spec {n : Nat} {edges : List (Edge n)}
    {source current : Fin n} (final_none : (afterFinal edges source).lastUpdated = none)
    (fuel : Nat) (distance : Int)
    (current_distance : (afterFinal edges source).distance.get current = some distance)
    (path : List (Edge n))
    (returns : followPredecessors source (afterFinal edges source).predecessor fuel current =
      some path) :
    IsWeightedPath edges source current path ∧
      (afterFinal edges source).distance.get current = some (pathWeight path) ∧
      ∀ edge ∈ path, (afterFinal edges source).predecessor.get edge.target = some edge := by
  induction fuel generalizing current distance path with
  | zero =>
      by_cases current_source : current = source
      · have path_nil : path = [] := by
          simpa [followPredecessors, followPredecessorsAux, current_source] using returns.symm
        subst path
        subst current
        exact ⟨by simp [IsWeightedPath], by
          simpa [pathWeight] using
            afterFinal_source_distance_zero_of_none edges source final_none, by simp⟩
      · simp [followPredecessors, followPredecessorsAux, current_source] at returns
  | succ fuel induction =>
      by_cases current_source : current = source
      · have path_nil : path = [] := by
          simpa [followPredecessors, followPredecessorsAux, current_source] using returns.symm
        subst path
        subst current
        exact ⟨by simp [IsWeightedPath], by
          simpa [pathWeight] using
            afterFinal_source_distance_zero_of_none edges source final_none, by simp⟩
      · cases predecessor_eq : (afterFinal edges source).predecessor.get current with
        | none => simp [followPredecessors, followPredecessorsAux, current_source, predecessor_eq] at returns
        | some edge =>
            cases tail_eq : followPredecessors source (afterFinal edges source).predecessor
                fuel edge.source with
            | none =>
                have step := followPredecessors_succ_of_ne
                  (afterFinal edges source).predecessor fuel current_source predecessor_eq
                rw [step, tail_eq] at returns
                simp at returns
            | some tail =>
                have path_eq : path = tail ++ [edge] := by
                  have step := followPredecessors_succ_of_ne
                    (afterFinal edges source).predecessor fuel current_source predecessor_eq
                  rw [step, tail_eq] at returns
                  simpa using returns.symm
                subst path
                obtain ⟨edge_mem, edge_target, sourceDistance, targetDistance,
                    source_eq, target_eq, lower⟩ :=
                  (afterFinal edges source).predecessor_step
                    (afterFinal_currentSnapshotsValid edges source)
                    (afterFinal_predecessorsFrom edges source) predecessor_eq
                obtain ⟨tail_valid, tail_distance, tail_predecessors⟩ :=
                  induction sourceDistance source_eq tail tail_eq
                obtain ⟨stableTarget, stable_target_eq, upper⟩ :=
                  afterFinal_stable_of_none edges source final_none edge edge_mem
                    sourceDistance source_eq
                have target_at_current :
                    (afterFinal edges source).distance.get current = some targetDistance := by
                  exact target_eq
                have stable_at_current :
                    (afterFinal edges source).distance.get current = some stableTarget := by
                  rwa [← edge_target]
                have target_value : targetDistance = distance :=
                  Option.some.inj (target_at_current.symm.trans current_distance)
                have stable_value : stableTarget = distance :=
                  Option.some.inj (stable_at_current.symm.trans current_distance)
                have source_value : sourceDistance = pathWeight tail :=
                  Option.some.inj (source_eq.symm.trans tail_distance)
                subst targetDistance
                subst stableTarget
                subst sourceDistance
                refine ⟨isWeightedPath_append_edge tail_valid edge_mem rfl edge_target,
                  ?_, ?_⟩
                · rw [pathWeight_append_edge]
                  exact current_distance.trans (by congr 1; omega)
                · intro item item_mem
                  simp only [List.mem_append, List.mem_singleton] at item_mem
                  rcases item_mem with item_mem | rfl
                  · exact tail_predecessors item item_mem
                  · simpa [edge_target] using predecessor_eq

theorem followPredecessors_spec {n : Nat} {edges : List (Edge n)}
    {source current : Fin n} (final_none : (afterFinal edges source).lastUpdated = none)
    (distance : Int)
    (current_distance : (afterFinal edges source).distance.get current = some distance)
    (path : List (Edge n))
    (returns : followPredecessors source (afterFinal edges source).predecessor n current =
      some path) :
    IsWeightedPath edges source current path ∧
      (afterFinal edges source).distance.get current = some (pathWeight path) ∧
      (pathVertices source path).Nodup ∧ path.length < n := by
  obtain ⟨path_valid, path_distance, path_predecessors⟩ :=
    followPredecessors_core_spec final_none n distance current_distance path returns
  have path_nodup := afterFinal_predecessor_path_nodup final_none path_valid path_predecessors
  have length_le := path_nodup.length_le_card
  simp [pathVertices] at length_le
  exact ⟨path_valid, path_distance, path_nodup, by omega⟩

theorem followPredecessors_none_trace {n : Nat} {edges : List (Edge n)}
    {source current : Fin n} (final_none : (afterFinal edges source).lastUpdated = none)
    (fuel : Nat) (distance : Int)
    (current_distance : (afterFinal edges source).distance.get current = some distance)
    (returns :
      followPredecessors source (afterFinal edges source).predecessor fuel current = none) :
    ∃ ordinal,
      (afterFinal edges source).predecessorUpdateOrdinal.get current = some ordinal ∧
        let vertices := current ::
          vertexTrace (predecessorVertex (afterFinal edges source).predecessor) fuel current
        vertices.Nodup ∧
          ∀ vertex ∈ vertices,
            ∃ vertexOrdinal,
              (afterFinal edges source).predecessorUpdateOrdinal.get vertex =
                some vertexOrdinal ∧ vertexOrdinal ≤ ordinal := by
  induction fuel generalizing current distance with
  | zero =>
      have current_ne_source : current ≠ source := by
        intro current_source
        subst current
        simp [followPredecessors, followPredecessorsAux] at returns
      cases predecessor_eq : (afterFinal edges source).predecessor.get current with
      | none =>
          obtain ⟨current_source, _⟩ :=
            afterFinal_rooted edges source current distance current_distance predecessor_eq
          contradiction
      | some edge =>
          obtain ⟨_, _, ordinal, _, _, _, ordinal_eq, _, _, _, _, _, _, _⟩ :=
            afterFinal_currentSnapshotsValid edges source current edge predecessor_eq
          refine ⟨ordinal, ordinal_eq, ?_⟩
          dsimp [vertexTrace]
          exact ⟨by simp, by
            intro vertex vertex_mem
            simp only [List.mem_singleton] at vertex_mem
            subst vertex
            exact ⟨ordinal, ordinal_eq, le_rfl⟩⟩
  | succ fuel induction =>
      have current_ne_source : current ≠ source := by
        intro current_source
        subst current
        simp [followPredecessors, followPredecessorsAux] at returns
      cases predecessor_eq : (afterFinal edges source).predecessor.get current with
      | none =>
          obtain ⟨current_source, _⟩ :=
            afterFinal_rooted edges source current distance current_distance predecessor_eq
          contradiction
      | some edge =>
          cases tail_eq : followPredecessors source (afterFinal edges source).predecessor
              fuel edge.source with
          | some tail =>
              have step := followPredecessors_succ_of_ne
                (afterFinal edges source).predecessor fuel current_ne_source predecessor_eq
              rw [step, tail_eq] at returns
              simp at returns
          | none =>
              obtain ⟨_, _, sourceDistance, _, source_distance, _, _⟩ :=
                (afterFinal edges source).predecessor_step
                  (afterFinal_currentSnapshotsValid edges source)
                  (afterFinal_predecessorsFrom edges source) predecessor_eq
              have edge_source_ne : edge.source ≠ source := by
                intro edge_source
                have impossible := tail_eq
                rw [edge_source, followPredecessors_source] at impossible
                contradiction
              cases source_predecessor_eq :
                  (afterFinal edges source).predecessor.get edge.source with
              | none =>
                  obtain ⟨edge_source_source, _⟩ :=
                    afterFinal_rooted edges source edge.source sourceDistance source_distance
                      source_predecessor_eq
                  contradiction
              | some sourceEdge =>
                  obtain ⟨sourceOrdinal, currentOrdinal, source_ordinal_eq,
                      current_ordinal_eq, ordinal_lt⟩ :=
                    (afterFinal edges source).predecessor_ordinal_lt_of_not_strict
                      (afterFinal_currentSnapshotsValid edges source) predecessor_eq
                      source_predecessor_eq
                      (afterFinal_predecessor_not_strict_of_none final_none predecessor_eq)
                  obtain ⟨tailOrdinal, tail_ordinal_eq, tail_nodup, tail_bound⟩ :=
                    induction sourceDistance source_distance tail_eq
                  have tail_ordinal_value : tailOrdinal = sourceOrdinal :=
                    Option.some.inj (tail_ordinal_eq.symm.trans source_ordinal_eq)
                  subst tailOrdinal
                  let tailVertices := edge.source ::
                    vertexTrace (predecessorVertex (afterFinal edges source).predecessor)
                      fuel edge.source
                  have current_not_tail : current ∉ tailVertices := by
                    intro current_mem
                    obtain ⟨vertexOrdinal, vertex_ordinal_eq, vertex_ordinal_le⟩ :=
                      tail_bound current current_mem
                    have vertex_value : vertexOrdinal = currentOrdinal :=
                      Option.some.inj (vertex_ordinal_eq.symm.trans current_ordinal_eq)
                    subst vertexOrdinal
                    omega
                  refine ⟨currentOrdinal, current_ordinal_eq, ?_⟩
                  dsimp only
                  rw [vertexTrace, predecessorVertex, predecessor_eq]
                  change (current :: tailVertices).Nodup ∧ _
                  refine ⟨List.nodup_cons.mpr ⟨current_not_tail, tail_nodup⟩, ?_⟩
                  intro vertex vertex_mem
                  simp only [List.mem_cons] at vertex_mem
                  rcases vertex_mem with rfl | vertex_mem
                  · exact ⟨currentOrdinal, current_ordinal_eq, le_rfl⟩
                  · obtain ⟨vertexOrdinal, vertex_ordinal_eq, vertex_ordinal_le⟩ :=
                      tail_bound vertex (by simpa [tailVertices] using vertex_mem)
                    exact ⟨vertexOrdinal, vertex_ordinal_eq,
                      vertex_ordinal_le.trans ordinal_lt.le⟩

theorem followPredecessors_some_of_finite {n : Nat} {edges : List (Edge n)}
    {source current : Fin n} (final_none : (afterFinal edges source).lastUpdated = none)
    (distance : Int)
    (current_distance : (afterFinal edges source).distance.get current = some distance) :
    ∃ path,
      followPredecessors source (afterFinal edges source).predecessor n current = some path := by
  cases path_eq : followPredecessors source (afterFinal edges source).predecessor n current with
  | some path => exact ⟨path, rfl⟩
  | none =>
      obtain ⟨_, _, vertices_nodup, _⟩ :=
        followPredecessors_none_trace final_none n distance current_distance path_eq
      have length_le := vertices_nodup.length_le_card
      rw [vertexTrace_eq_ofFn] at length_le
      simp only [List.length_cons, List.length_ofFn, Fintype.card_fin] at length_le
      omega

theorem followPredecessors_none_of_distance_none {n : Nat}
    {edges : List (Edge n)} {source current : Fin n}
    (final_none : (afterFinal edges source).lastUpdated = none)
    (distance_none : (afterFinal edges source).distance.get current = none) :
    followPredecessors source (afterFinal edges source).predecessor n current = none := by
  have current_ne_source : current ≠ source := by
    intro current_source
    subst current
    rw [afterFinal_source_distance_zero_of_none edges source final_none] at distance_none
    contradiction
  have predecessor_none : (afterFinal edges source).predecessor.get current = none := by
    cases predecessor_eq : (afterFinal edges source).predecessor.get current with
    | none => rfl
    | some edge =>
        obtain ⟨_, _, _, targetDistance, _, target_eq, _⟩ :=
          (afterFinal edges source).predecessor_step
            (afterFinal_currentSnapshotsValid edges source)
            (afterFinal_predecessorsFrom edges source) predecessor_eq
        rw [distance_none] at target_eq
        contradiction
  cases n with
  | zero => exact Fin.elim0 source
  | succ n => simp [followPredecessors, followPredecessorsAux, current_ne_source, predecessor_none]

theorem afterFinal_lastUpdated_none_iff {n : Nat}
    (edges : List (Edge n)) (source : Fin n) :
    (afterFinal edges source).lastUpdated = none ↔
      ¬HasReachableNegativeCycle edges source := by
  constructor
  · exact afterFinal_no_negativeCycle_of_none edges source
  · intro no_negative
    cases updated_eq : (afterFinal edges source).lastUpdated with
    | none => rfl
    | some updated =>
        exfalso
        apply no_negative
        obtain ⟨witness, _⟩ :=
          afterFinal_finish_negativeCycle_of_updated edges source updated updated_eq
        exact ⟨witness⟩

theorem bellmanFord_eq_finish_afterFinal {n : Nat}
    (edges : List (Edge n)) (source : Fin n) :
    (bellmanFord edges source).ret =
      (finish edges source (afterFinal edges source)).ret := by
  rfl

theorem afterFinal_none_of_bellmanFord_distances {n : Nat}
    {edges : List (Edge n)} {source : Fin n} {result : Distances n}
    (hRun : (bellmanFord edges source).ret = Result.distances result) :
    (afterFinal edges source).lastUpdated = none := by
  cases updated_eq : (afterFinal edges source).lastUpdated with
  | none => rfl
  | some updated =>
      obtain ⟨witness, finish_negative⟩ :=
        afterFinal_finish_negativeCycle_of_updated edges source updated updated_eq
      have run_negative :
          (bellmanFord edges source).ret = Result.negativeCycle witness := by
        rw [bellmanFord_eq_finish_afterFinal]
        exact finish_negative
      rw [hRun] at run_negative
      contradiction

theorem bellmanFord_distances_eq_afterFinal {n : Nat}
    {edges : List (Edge n)} {source : Fin n} {result : Distances n}
    (hRun : (bellmanFord edges source).ret = Result.distances result) :
    result = (afterFinal edges source).toDistances source := by
  have final_none := afterFinal_none_of_bellmanFord_distances hRun
  rw [bellmanFord_eq_finish_afterFinal] at hRun
  have result_eq :
      (Result.distances ((afterFinal edges source).toDistances source) : Result edges source) =
        (Result.distances result : Result edges source) := by
    simpa [finish, final_none] using hRun
  exact (Result.distances.inj result_eq).symm

attribute [simp] initialState State.install relaxOne relaxEdges runPasses localizeCycle
  collectCycle collectPrefix allMemDecidable isWeightedPathDecidable
  State.toDistances finish Internal.bellmanFord

private lemma ranked_source_path {n : Nat} (result : Distances n)
    (edges : List (Edge n)) (rank : Fin n → Nat)
    (source_zero : result.distance.get result.source = some 0)
    (fuel : Nat) (distance : Int)
    (current_distance : result.distance.get result.source = some distance) :
    ∃ path, followPredecessors result.source result.predecessor fuel result.source = some path ∧
      IsWeightedPath edges result.source result.source path ∧
      pathWeight path = distance ∧ path.length ≤ rank result.source := by
  have distance_zero : distance = 0 := Option.some.inj (current_distance.symm.trans source_zero)
  subst distance
  exact ⟨[], followPredecessors_source _ _ _, by simp [IsWeightedPath],
    by simp [pathWeight], by simp⟩

private lemma ranked_finite_path {n : Nat} (result : Distances n)
    (edges : List (Edge n)) (rank : Fin n → Nat)
    (source_zero : result.distance.get result.source = some 0)
    (finite_predecessor : ∀ vertex distance, result.distance.get vertex = some distance →
      vertex ≠ result.source → ∃ edge, result.predecessor.get vertex = some edge)
    (predecessor_step : ∀ vertex edge, result.predecessor.get vertex = some edge →
      edge ∈ edges ∧ edge.target = vertex ∧ ∃ sourceDistance,
        result.distance.get edge.source = some sourceDistance ∧
        result.distance.get vertex = some (sourceDistance + edge.weight) ∧
        rank edge.source < rank vertex)
    (fuel : Nat) (current : Fin n) (distance : Int)
    (current_distance : result.distance.get current = some distance)
    (rank_le : rank current ≤ fuel) :
    ∃ path, followPredecessors result.source result.predecessor fuel current = some path ∧
      IsWeightedPath edges result.source current path ∧
      pathWeight path = distance ∧ path.length ≤ rank current := by
  induction fuel generalizing current distance with
  | zero =>
      have current_source : current = result.source := by
        by_contra different
        obtain ⟨edge, predecessor_eq⟩ :=
          finite_predecessor current distance current_distance different
        obtain ⟨_, _, _, _, _, rank_lt⟩ := predecessor_step current edge predecessor_eq
        omega
      subst current
      exact ranked_source_path result edges rank source_zero 0 distance current_distance
  | succ fuel induction =>
      by_cases current_source : current = result.source
      · subst current
        exact ranked_source_path result edges rank source_zero (fuel + 1) distance current_distance
      · obtain ⟨edge, predecessor_eq⟩ :=
          finite_predecessor current distance current_distance current_source
        obtain ⟨edge_mem, edge_target, sourceDistance, source_eq, target_eq, rank_lt⟩ :=
          predecessor_step current edge predecessor_eq
        obtain ⟨tail, tail_eq, tail_valid, tail_weight, tail_length⟩ :=
          induction edge.source sourceDistance source_eq (by omega)
        refine ⟨tail ++ [edge], ?_,
          isWeightedPath_append_edge tail_valid edge_mem rfl edge_target, ?_, ?_⟩
        · rw [followPredecessors_succ_of_ne result.predecessor fuel current_source
            predecessor_eq, tail_eq]
          rfl
        · rw [pathWeight_append_edge, tail_weight]
          exact Option.some.inj (target_eq.symm.trans current_distance)
        · simp only [List.length_append, List.length_singleton]
          omega

end Internal

/-- **Bellman–Ford algorithm.** Let $E$ be a list of integer-weighted directed edges on the
vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex. Bellman–Ford run on $E$ from $s$ starts
with distance $d(s) = 0$ and $d(v) = \infty$ for every other vertex $v$, and makes $n - 1$ passes
over $E$ followed by one final pass. A pass goes through the edges of $E$ in list order, charging
one relaxation check per edge occurrence; an edge from $u$ to $v$ of weight $w$ with $d(u)$ finite
sets $d(v)$ to $d(u) + w$ and records the edge as the predecessor edge of $v$ when $d(v) = \infty$
or $d(u) + w < d(v)$. If the final pass changes no distance, the result is the distances and
predecessor edges. Otherwise, starting from the vertex whose distance the final pass changed
last, the algorithm follows $n$ predecessor edges back to a vertex $b$; it then collects the
cycle of predecessor edges through $b$, following at most $n$ predecessor edges back from $b$
until it reaches an edge with source $b$, and collects a path from $s$ to $b$ of at most $n - 1$
edges by following back from $b$ the edges by which vertices first received a finite distance.
Each lookup of a recorded edge in these three steps is charged as one witness step, also when
no edge is recorded. If all three steps succeed and give a reachable negative cycle witness for
$E$ and $s$, that witness is the result; otherwise the result is the distances and predecessor
edges. -/
public def bellmanFord {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    TimeM Cost (Result edges source) :=
  Internal.bellmanFord edges source

open Internal

/-- **Bellman-Ford succeeds exactly when no negative cycle is reachable.** Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex.
Bellman-Ford run on $E$ from $s$ returns distances if and only if there is no negative cycle
reachable from $s$, that is, no simple path from $s$ to a vertex $b$ together with a nonempty
cycle through $b$ along edges of $E$ whose edge sources are pairwise distinct and whose total
weight is negative. -/
public theorem bellmanFord_returns_distances_iff {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (∃ result, (bellmanFord edges source).ret = Result.distances result) ↔
      ¬HasReachableNegativeCycle edges source := by
  constructor
  · rintro ⟨result, hRun⟩
    exact afterFinal_lastUpdated_none_iff edges source |>.mp
      (afterFinal_none_of_bellmanFord_distances hRun)
  · intro no_negative
    have final_none := (afterFinal_lastUpdated_none_iff edges source).mpr no_negative
    refine ⟨(afterFinal edges source).toDistances source, ?_⟩
    change (Internal.bellmanFord edges source).ret = _
    rw [bellmanFord_eq_finish_afterFinal]
    simp [finish, final_none]

/-- **Bellman-Ford reports a negative cycle exactly when one is reachable.** Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex.
Bellman-Ford run on $E$ from $s$ returns a reachable negative cycle witness if and only if a
negative cycle is reachable from $s$, that is, there are a simple path from $s$ to a vertex $b$
and a nonempty cycle through $b$ along edges of $E$ whose edge sources are pairwise distinct and
whose total weight is negative. -/
public theorem bellmanFord_returns_negativeCycle_iff {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (∃ witness, (bellmanFord edges source).ret = Result.negativeCycle witness) ↔
      HasReachableNegativeCycle edges source := by
  constructor
  · rintro ⟨witness, _⟩
    exact ⟨witness⟩
  · intro has_negative
    cases updated_eq : (afterFinal edges source).lastUpdated with
    | none =>
        exact False.elim ((afterFinal_no_negativeCycle_of_none edges source updated_eq)
          has_negative)
    | some updated =>
        obtain ⟨witness, finish_eq⟩ :=
          afterFinal_finish_negativeCycle_of_updated edges source updated updated_eq
        exact ⟨witness, by
          change (Internal.bellmanFord edges source).ret = _
          rw [bellmanFord_eq_finish_afterFinal]
          exact finish_eq⟩

/-- **Bellman-Ford distances are realized by walks.** Let $E$ be a list of integer-weighted
directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex. If Bellman-Ford run
on $E$ from $s$ returns distances $d$ and the distance $d(t)$ of a vertex $t$ is a finite integer
$\delta$, then there is a walk from $s$ to $t$ along edges of $E$ whose total weight is
$\delta$. -/
public theorem bellmanFord_distance_realized {n : Nat} {edges : List (Edge n)}
    {source target : Fin n}
    {result : Distances n} {distance : Int}
    (hRun : (bellmanFord edges source).ret = Result.distances result)
    (hDistance : result.distance.get target = some distance) :
    ∃ path, IsWeightedPath edges source target path ∧ pathWeight path = distance := by
  let ordinary := (runPasses edges (n - 1) (initialState source)).ret
  let finalState := (relaxEdges edges { ordinary with lastUpdated := none }).ret
  have ordinary_realizes : ordinary.Realizes edges source := by
    exact runPasses_realizes edges source (n - 1) (initialState source)
      (initialState_realizes edges source)
  have reset_realizes : ({ ordinary with lastUpdated := none }).Realizes edges source :=
    ordinary_realizes
  have final_realizes : finalState.Realizes edges source := by
    exact relaxEdges_realizes edges { ordinary with lastUpdated := none } reset_realizes
      (fun _ => id)
  have finish_returns : (finish edges source finalState).ret = Result.distances result := by
    simpa only [bellmanFord, Internal.bellmanFord, TimeM.ret_bind, ordinary, finalState] using hRun
  have distance_vector := finish_distances_distance_eq edges source finalState result finish_returns
  apply final_realizes target distance
  rwa [← distance_vector]

/-- **Bellman-Ford distances are lower bounds on walk weights.** Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex.
If Bellman-Ford run on $E$ from $s$ returns distances $d$, the distance $d(t)$ of a vertex $t$
is a finite integer $\delta$, and $P$ is a walk from $s$ to $t$ along edges of $E$ (vertices may
repeat), then $\delta$ is at most the total weight of $P$. -/
public theorem bellmanFord_distance_minimal {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {result : Distances n} {distance : Int}
    {path : List (Edge n)}
    (hRun : (bellmanFord edges source).ret = Result.distances result)
    (hDistance : result.distance.get target = some distance)
    (hPath : IsWeightedPath edges source target path) :
    distance ≤ pathWeight path := by
  have result_eq := bellmanFord_distances_eq_afterFinal hRun
  have final_none := afterFinal_none_of_bellmanFord_distances hRun
  subst result
  exact afterFinal_minimal_of_none final_none hDistance hPath

/-- **Bellman-Ford leaves exactly the unreachable vertices at infinite distance.** Let $E$ be a
list of integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a
vertex. If Bellman-Ford run on $E$ from $s$ returns distances $d$, with $\infty$ marking a vertex
that has no finite distance, then for every vertex $t$, $d(t) = \infty$ if and only if $t$ is not
reachable from $s$ in the directed graph obtained from $E$ by forgetting the weights. -/
public theorem bellmanFord_distance_eq_none_iff {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {result : Distances n}
    (hRun : (bellmanFord edges source).ret = Result.distances result) :
    result.distance.get target = none ↔
      ¬(toDirectedAdjacency edges).Reachable source target := by
  have result_eq := bellmanFord_distances_eq_afterFinal hRun
  have final_none := afterFinal_none_of_bellmanFord_distances hRun
  subst result
  exact afterFinal_distance_eq_none_iff_of_none final_none

/-- **Bellman-Ford predecessor edges are tight.** Let $E$ be a list of integer-weighted directed
edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex. Suppose Bellman-Ford run on
$E$ from $s$ returns distances $d$ together with predecessor edges, and the predecessor edge of a
vertex $t$ is an edge $e$ from $u$ to $v$ of weight $w$. Then $e$ belongs to $E$, $v = t$, and
$d(u)$ and $d(t)$ are both finite with $d(t) = d(u) + w$. -/
public theorem bellmanFord_predecessor_spec {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {result : Distances n} {edge : Edge n}
    (hRun : (bellmanFord edges source).ret = Result.distances result)
    (hPredecessor : result.predecessor.get target = some edge) :
    edge ∈ edges ∧ edge.target = target ∧
      ∃ sourceDistance targetDistance,
        result.distance.get edge.source = some sourceDistance ∧
          result.distance.get target = some targetDistance ∧
          targetDistance = sourceDistance + edge.weight := by
  have result_eq := bellmanFord_distances_eq_afterFinal hRun
  have final_none := afterFinal_none_of_bellmanFord_distances hRun
  subst result
  obtain ⟨edge_mem, edge_target, sourceDistance, targetDistance,
      source_eq, target_eq, lower⟩ :=
    (afterFinal edges source).predecessor_step
      (afterFinal_currentSnapshotsValid edges source)
      (afterFinal_predecessorsFrom edges source) hPredecessor
  obtain ⟨stableTarget, stable_target_eq, upper⟩ :=
    afterFinal_stable_of_none edges source final_none edge edge_mem sourceDistance source_eq
  have target_value : stableTarget = targetDistance :=
    Option.some.inj (stable_target_eq.symm.trans (edge_target ▸ target_eq))
  subst stableTarget
  exact ⟨edge_mem, edge_target, sourceDistance, targetDistance, source_eq,
    edge_target ▸ target_eq, by omega⟩

/-- **Bellman-Ford gives the source no predecessor.** Let $E$ be a list of integer-weighted
directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex. If Bellman-Ford run
on $E$ from $s$ returns distances together with predecessor edges, then $s$ has no predecessor
edge. -/
public theorem bellmanFord_source_predecessor_eq_none {n : Nat} {edges : List (Edge n)}
    {source : Fin n} {result : Distances n}
    (hRun : (bellmanFord edges source).ret = Result.distances result) :
    result.predecessor.get source = none := by
  have result_eq := bellmanFord_distances_eq_afterFinal hRun
  have final_none := afterFinal_none_of_bellmanFord_distances hRun
  subst result
  exact afterFinal_source_predecessor_none_of_none edges source final_none

/-- **Bellman-Ford path reconstruction fails exactly at infinite distances.** Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex. If
Bellman-Ford run on $E$ from $s$ returns distances $d$, with $\infty$ marking a vertex that has
no finite distance, together with predecessor edges, then for every vertex $t$, reconstructing a
path to $t$ (following predecessor edges back from $t$ for at most $n$ steps until $s$ is
reached) fails if and only if $d(t) = \infty$. -/
public theorem bellmanFord_pathTo?_eq_none_iff {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {result : Distances n}
    (hRun : (bellmanFord edges source).ret = Result.distances result) :
    result.pathTo? target = none ↔ result.distance.get target = none := by
  have result_eq := bellmanFord_distances_eq_afterFinal hRun
  have final_none := afterFinal_none_of_bellmanFord_distances hRun
  subst result
  rw [pathTo?_eq_followPredecessors]
  change followPredecessors source (afterFinal edges source).predecessor n target = none ↔
    (afterFinal edges source).distance.get target = none
  constructor
  · intro follow_none
    cases distance_eq : (afterFinal edges source).distance.get target with
    | none => rfl
    | some distance =>
        obtain ⟨path, path_eq⟩ :=
          followPredecessors_some_of_finite final_none distance distance_eq
        rw [path_eq] at follow_none
        contradiction
  · exact followPredecessors_none_of_distance_none final_none

/-- **Bellman-Ford reconstructed paths are simple and realize the distances.** Let $E$ be a list
of integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex.
Suppose Bellman-Ford run on $E$ from $s$ returns distances $d$ together with predecessor edges,
and that reconstructing a path to a vertex $t$ (following predecessor edges back from $t$ for at
most $n$ steps until $s$ is reached) yields the edge sequence $P$. Then $P$ is a walk from $s$
to $t$ along edges of $E$, $d(t)$ is finite and equals the total weight of $P$, the vertex $s$
and the targets of the edges of $P$ are pairwise distinct, and $P$ has fewer than $n$ edges. -/
public theorem bellmanFord_pathTo?_spec {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {result : Distances n} {path : List (Edge n)}
    (hRun : (bellmanFord edges source).ret = Result.distances result)
    (hPath : result.pathTo? target = some path) :
    IsWeightedPath edges source target path ∧
      result.distance.get target = some (pathWeight path) ∧
      (pathVertices source path).Nodup ∧ path.length < n := by
  have result_eq := bellmanFord_distances_eq_afterFinal hRun
  have final_none := afterFinal_none_of_bellmanFord_distances hRun
  subst result
  rw [pathTo?_eq_followPredecessors] at hPath
  change followPredecessors source (afterFinal edges source).predecessor n target =
    some path at hPath
  cases distance_eq : (afterFinal edges source).distance.get target with
  | none =>
      have follow_none := followPredecessors_none_of_distance_none final_none distance_eq
      rw [hPath] at follow_none
      contradiction
  | some distance =>
      exact followPredecessors_spec final_none distance distance_eq path hPath

/-- **Predecessor paths realize the distances under a decreasing rank.** Let $R$ be a
distances record on $n$ vertices with source $s$, distance table $d$ (each $d(v)$ is an integer
or infinite) and predecessor table $p$; let $E$ be a list of weighted edges; and let $r$ assign to
each vertex $v$ a natural number $r(v) < n$. Suppose that $d(s) = 0$, that every vertex $v$ with
$d(v)$ infinite has no predecessor, that every vertex $v \ne s$ with $d(v)$ finite has a
predecessor, and that whenever $p(v) = e$, the edge $e$ occurs in $E$, ends at $v$, and its start
$u$ has $d(u)$ finite, $d(v) = d(u) + w(e)$ where $w(e)$ is the weight of $e$, and $r(u) < r(v)$.
Then for every vertex $t$, following predecessors from $t$ back to $s$ for at most $n$ edges fails
exactly when $d(t)$ is infinite; and whenever it returns a path $P$ and $d(t)$ is finite, $P$ is a
path from $s$ to $t$ made of edges of $E$, its total weight is $d(t)$, and it has fewer than $n$
edges. -/
public theorem Distances.pathTo?_spec_of_rank {n : Nat} (result : Distances n)
    (edges : List (Edge n)) (rank : Fin n → Nat)
    (rank_bound : ∀ vertex, rank vertex < n)
    (source_zero : result.distance.get result.source = some 0)
    (infinite_predecessor : ∀ vertex, result.distance.get vertex = none →
      result.predecessor.get vertex = none)
    (finite_predecessor : ∀ vertex distance, result.distance.get vertex = some distance →
      vertex ≠ result.source → ∃ edge, result.predecessor.get vertex = some edge)
    (predecessor_step : ∀ vertex edge, result.predecessor.get vertex = some edge →
      edge ∈ edges ∧ edge.target = vertex ∧ ∃ sourceDistance,
        result.distance.get edge.source = some sourceDistance ∧
        result.distance.get vertex = some (sourceDistance + edge.weight) ∧
        rank edge.source < rank vertex) :
    ∀ target, (result.pathTo? target = none ↔ result.distance.get target = none) ∧
      ∀ path distance, result.pathTo? target = some path →
        result.distance.get target = some distance →
        IsWeightedPath edges result.source target path ∧
        pathWeight path = distance ∧ path.length < n := by
  intro target
  have finite_path (distance : Int) (saved : result.distance.get target = some distance) :
      ∃ path, result.pathTo? target = some path ∧
        IsWeightedPath edges result.source target path ∧
        pathWeight path = distance ∧ path.length < n := by
    obtain ⟨path, follows, valid, weight, length_le⟩ :=
      ranked_finite_path result edges rank source_zero finite_predecessor predecessor_step
        n target distance saved (rank_bound target).le
    exact ⟨path, (pathTo?_eq_followPredecessors result target).trans follows,
      valid, weight, length_le.trans_lt (rank_bound target)⟩
  refine ⟨?_, ?_⟩
  · constructor
    · intro failed
      cases saved : result.distance.get target with
      | none => rfl
      | some distance =>
          obtain ⟨path, returns, _⟩ := finite_path distance saved
          rw [returns] at failed
          contradiction
    · intro infinite
      have target_ne_source : target ≠ result.source := by
        intro equal
        subst target
        rw [source_zero] at infinite
        contradiction
      have predecessor_none := infinite_predecessor target infinite
      rw [pathTo?_eq_followPredecessors]
      cases n <;> simp [followPredecessors, followPredecessorsAux,
        target_ne_source, predecessor_none]
  · intro path distance returns saved
    obtain ⟨output, output_eq, valid, weight, length_lt⟩ := finite_path distance saved
    have output_path : output = path := Option.some.inj (output_eq.symm.trans returns)
    subst output
    exact ⟨valid, weight, length_lt⟩

end Cslib.Algorithms.Lean.BellmanFord
