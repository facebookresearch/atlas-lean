/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Relaxation

/-! # Bellman-Ford negative-cycle and prefix extraction -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BellmanFord

namespace Internal

theorem State.predecessor_step {n : Nat} {edges : List (Edge n)}
    {state : State n} (valid : state.CurrentSnapshotsValid)
    (from_edges : state.PredecessorsFrom edges) {target : Fin n} {edge : Edge n}
    (predecessor_eq : state.predecessor.get target = some edge) :
    edge ∈ edges ∧ edge.target = target ∧
      ∃ sourceDistance targetDistance,
        state.distance.get edge.source = some sourceDistance ∧
          state.distance.get target = some targetDistance ∧
          sourceDistance + edge.weight ≤ targetDistance := by
  obtain ⟨snapshotSource, targetDistance, _, _, _, _, _, _, edge_target,
      target_eq, target_formula, ⟨sourceDistance, source_eq, source_le⟩, _, _⟩ :=
    valid target edge predecessor_eq
  exact ⟨from_edges target edge predecessor_eq, edge_target, sourceDistance,
    targetDistance, source_eq, target_eq, by omega⟩

def localizeCycle {n : Nat} (predecessor : Vector (Option (Edge n)) n) :
    Nat → Fin n → TimeM Cost (Option (Fin n))
  | 0, current => pure (some current)
  | steps + 1, current => do
      let _ ← TimeM.tick ⟨0, 1⟩
      match predecessor.get current with
      | none => pure none
      | some edge => localizeCycle predecessor steps edge.source

def predecessorVertex {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (current : Fin n) : Fin n :=
  match predecessor.get current with
  | none => current
  | some edge => edge.source

def vertexTrace {n : Nat} (f : Fin n → Fin n) : Nat → Fin n → List (Fin n)
  | 0, _ => []
  | steps + 1, current => f current :: vertexTrace f steps (f current)

theorem vertexTrace_eq_ofFn {n : Nat} (f : Fin n → Fin n)
    (steps : Nat) (current : Fin n) :
    vertexTrace f steps current =
      List.ofFn (fun index : Fin steps => (f^[index.val + 1]) current) := by
  induction steps generalizing current with
  | zero => simp [vertexTrace]
  | succ steps induction =>
      rw [vertexTrace, List.ofFn_succ]
      congr 1
      rw [induction]
      apply congrArg List.ofFn
      funext index
      rw [← Function.iterate_succ_apply]
      congr 1

theorem vertexTrace_nodup_of_first_return {n : Nat} (f : Fin n → Fin n)
    (current : Fin n) (period : Nat)
    (periodic : (f^[period]) current = current)
    (first_return : ∀ step, 0 < step → step < period → (f^[step]) current ≠ current) :
    (vertexTrace f period current).Nodup := by
  rw [vertexTrace_eq_ofFn]
  apply List.nodup_ofFn_ofInjective
  intro left right equal
  apply Fin.ext
  by_contra different
  rcases lt_or_gt_of_ne different with before | before
  · have mapped := congrArg (fun vertex ↦ (f^[period - (right.val + 1)]) vertex) equal
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at mapped
    have right_exponent : period - (right.val + 1) + (right.val + 1) = period := by
      omega
    have left_pos : 0 < period - (right.val + 1) + (left.val + 1) := by omega
    have left_lt : period - (right.val + 1) + (left.val + 1) < period := by omega
    rw [right_exponent, periodic] at mapped
    exact first_return _ left_pos left_lt mapped
  · have mapped := congrArg (fun vertex ↦ (f^[period - (left.val + 1)]) vertex) equal.symm
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at mapped
    have left_exponent : period - (left.val + 1) + (left.val + 1) = period := by omega
    have right_pos : 0 < period - (left.val + 1) + (right.val + 1) := by omega
    have right_lt : period - (left.val + 1) + (right.val + 1) < period := by omega
    rw [left_exponent, periodic] at mapped
    exact first_return _ right_pos right_lt mapped

theorem localizeCycle_iterate_eq_of_ret_some {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (steps : Nat) (current base : Fin n)
    (returns : (localizeCycle predecessor steps current).ret = some base) :
    ((predecessorVertex predecessor)^[steps]) current = base := by
  induction steps generalizing current with
  | zero => simpa [localizeCycle] using Option.some.inj returns
  | succ steps induction =>
      cases predecessor_eq : predecessor.get current with
      | none => simp [localizeCycle, predecessor_eq] at returns
      | some edge =>
          have tail_returns :
              (localizeCycle predecessor steps edge.source).ret = some base := by
            simpa [localizeCycle, predecessor_eq] using returns
          rw [Function.iterate_succ_apply, predecessorVertex, predecessor_eq]
          exact induction edge.source tail_returns

theorem localizeCycle_reads_of_ret_some {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (steps : Nat) (current base : Fin n)
    (returns : (localizeCycle predecessor steps current).ret = some base)
    (index : Nat) (index_lt : index < steps) :
    ∃ edge,
      predecessor.get (((predecessorVertex predecessor)^[index]) current) = some edge := by
  induction steps generalizing current index with
  | zero => omega
  | succ steps induction =>
      cases predecessor_eq : predecessor.get current with
      | none => simp [localizeCycle, predecessor_eq] at returns
      | some edge =>
          have tail_returns :
              (localizeCycle predecessor steps edge.source).ret = some base := by
            simpa [localizeCycle, predecessor_eq] using returns
          cases index with
          | zero => exact ⟨edge, predecessor_eq⟩
          | succ index =>
              rw [Function.iterate_succ_apply, predecessorVertex, predecessor_eq]
              exact induction edge.source tail_returns index (by omega)

theorem localizeCycle_periodic_of_ret_some {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (current base : Fin n)
    (returns : (localizeCycle predecessor n current).ret = some base) :
    ∃ period, 0 < period ∧ period ≤ n ∧
      ((predecessorVertex predecessor)^[period]) base = base ∧
      ∀ index < period,
        ∃ edge,
          predecessor.get (((predecessorVertex predecessor)^[index]) base) = some edge := by
  obtain ⟨earlier, earlier_lt, earlier_eq⟩ :=
    iterate_fin_has_earlier (predecessorVertex predecessor) current
  have base_eq : ((predecessorVertex predecessor)^[earlier]) current = base := by
    rw [earlier_eq]
    exact localizeCycle_iterate_eq_of_ret_some predecessor n current base returns
  refine ⟨n - earlier, by omega, Nat.sub_le n earlier, ?_, ?_⟩
  · have mapped := congrArg
      (fun vertex ↦ ((predecessorVertex predecessor)^[n - earlier]) vertex) base_eq
    rw [← Function.iterate_add_apply] at mapped
    have exponent : n - earlier + earlier = n := by omega
    rw [exponent, localizeCycle_iterate_eq_of_ret_some predecessor n current base returns]
      at mapped
    exact mapped.symm
  · intro index index_lt
    have combined_lt : earlier + index < n := by omega
    obtain ⟨edge, edge_eq⟩ := localizeCycle_reads_of_ret_some predecessor n current
      base returns (earlier + index) combined_lt
    refine ⟨edge, ?_⟩
    rw [← base_eq, ← Function.iterate_add_apply]
    simpa [Nat.add_comm] using edge_eq

theorem localizeCycle_none_path {n : Nat} {edges : List (Edge n)}
    {state : State n} (valid : state.CurrentSnapshotsValid)
    (from_edges : state.PredecessorsFrom edges) (steps : Nat) (current : Fin n)
    (currentDistance : Int)
    (current_eq : state.distance.get current = some currentDistance)
    (returns : (localizeCycle state.predecessor steps current).ret = none) :
    ∃ root path rootDistance,
      state.predecessor.get root = none ∧
        state.distance.get root = some rootDistance ∧
        IsWeightedPath edges root current path ∧ path.length < steps ∧
        pathWeight path ≤ currentDistance - rootDistance := by
  induction steps generalizing current currentDistance with
  | zero => simp [localizeCycle] at returns
  | succ steps induction =>
      cases predecessor_eq : state.predecessor.get current with
      | none =>
          exact ⟨current, [], currentDistance, predecessor_eq, current_eq,
            by simp [IsWeightedPath], by simp, by simp [pathWeight]⟩
      | some edge =>
          have tail_returns :
              (localizeCycle state.predecessor steps edge.source).ret = none := by
            simpa [localizeCycle, predecessor_eq] using returns
          obtain ⟨edge_mem, edge_target, sourceDistance, targetDistance,
              source_eq, target_eq, step_le⟩ :=
            state.predecessor_step valid from_edges predecessor_eq
          have targetDistance_eq : targetDistance = currentDistance :=
            Option.some.inj (target_eq.symm.trans current_eq)
          subst targetDistance
          obtain ⟨root, path, rootDistance, root_none, root_eq, path_valid,
              path_length, path_le⟩ :=
            induction edge.source sourceDistance source_eq tail_returns
          refine ⟨root, path ++ [edge], rootDistance, root_none, root_eq,
            isWeightedPath_append_edge path_valid edge_mem rfl edge_target,
            ?_, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            omega
          · rw [pathWeight_append_edge]
            omega

theorem localizeCycle_finite_of_ret_some {n : Nat} {edges : List (Edge n)}
    {state : State n} (valid : state.CurrentSnapshotsValid)
    (from_edges : state.PredecessorsFrom edges) (steps : Nat) (current base : Fin n)
    (currentDistance : Int)
    (current_eq : state.distance.get current = some currentDistance)
    (returns : (localizeCycle state.predecessor steps current).ret = some base) :
    ∃ baseDistance, state.distance.get base = some baseDistance := by
  induction steps generalizing current currentDistance with
  | zero =>
      have base_eq : base = current := by
        simpa [localizeCycle] using (Option.some.inj returns).symm
      subst base
      exact ⟨currentDistance, current_eq⟩
  | succ steps induction =>
      cases predecessor_eq : state.predecessor.get current with
      | none => simp [localizeCycle, predecessor_eq] at returns
      | some edge =>
          obtain ⟨_, _, sourceDistance, _, source_eq, _, _⟩ :=
            state.predecessor_step valid from_edges predecessor_eq
          have tail_returns :
              (localizeCycle state.predecessor steps edge.source).ret = some base := by
            simpa [localizeCycle, predecessor_eq] using returns
          exact induction edge.source sourceDistance source_eq tail_returns

def collectCycle {n : Nat} (predecessor : Vector (Option (Edge n)) n)
    (base : Fin n) : Nat → Fin n → List (Edge n) → TimeM Cost (Option (List (Edge n)))
  | 0, _, _ => pure none
  | fuel + 1, current, reversePath => do
      let _ ← TimeM.tick ⟨0, 1⟩
      match predecessor.get current with
      | none => pure none
      | some edge =>
          let path := edge :: reversePath
          if edge.source = base then pure (some path)
          else collectCycle predecessor base fuel edge.source path

theorem collectCycle_some_of_reaches {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (base current : Fin n)
    (period fuel : Nat) (path : List (Edge n))
    (period_pos : 0 < period) (period_le : period ≤ fuel)
    (reaches : ((predecessorVertex predecessor)^[period]) current = base)
    (reads : ∀ index < period,
      ∃ edge,
        predecessor.get (((predecessorVertex predecessor)^[index]) current) = some edge) :
    ∃ output,
      (collectCycle predecessor base fuel current path).ret = some output := by
  induction period generalizing fuel current path with
  | zero => omega
  | succ period induction =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          obtain ⟨edge, predecessor_eq⟩ := reads 0 (by omega)
          simp only [Function.iterate_zero, id_eq] at predecessor_eq
          by_cases closes : edge.source = base
          · exact ⟨edge :: path, by
              simp [collectCycle, predecessor_eq, closes]⟩
          · have tail_reaches :
                ((predecessorVertex predecessor)^[period]) edge.source = base := by
              rw [Function.iterate_succ_apply, predecessorVertex, predecessor_eq] at reaches
              exact reaches
            have tail_reads : ∀ index < period,
                ∃ nextEdge,
                  predecessor.get
                    (((predecessorVertex predecessor)^[index]) edge.source) =
                      some nextEdge := by
              intro index index_lt
              obtain ⟨nextEdge, next_eq⟩ := reads (index + 1) (by omega)
              refine ⟨nextEdge, ?_⟩
              rw [show index + 1 = index.succ by omega,
                Function.iterate_succ_apply, predecessorVertex, predecessor_eq] at next_eq
              exact next_eq
            have period_positive : 0 < period := by
              by_contra period_not_pos
              have period_zero : period = 0 := by omega
              subst period
              simp at tail_reaches
              exact closes tail_reaches
            obtain ⟨output, output_eq⟩ := induction edge.source fuel (edge :: path)
              period_positive (by omega) tail_reaches tail_reads
            exact ⟨output, by
              simpa [collectCycle, predecessor_eq, closes] using output_eq⟩

theorem collectCycle_trace_spec {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (base : Fin n)
    (fuel : Nat) (current : Fin n) (path output : List (Edge n))
    (returns : (collectCycle predecessor base fuel current path).ret = some output) :
    ∃ steps, 0 < steps ∧ steps ≤ fuel ∧
      output.map Edge.source =
        (vertexTrace (predecessorVertex predecessor) steps current).reverse ++
          path.map Edge.source ∧
      ((predecessorVertex predecessor)^[steps]) current = base ∧
      ∀ step, 0 < step → step < steps →
        ((predecessorVertex predecessor)^[step]) current ≠ base := by
  induction fuel generalizing current path with
  | zero => simp [collectCycle] at returns
  | succ fuel induction =>
      cases predecessor_eq : predecessor.get current with
      | none => simp [collectCycle, predecessor_eq] at returns
      | some edge =>
          by_cases closes : edge.source = base
          · have output_eq : output = edge :: path := by
              simpa [collectCycle, predecessor_eq, closes] using returns.symm
            subst output
            refine ⟨1, by omega, by omega, ?_, ?_, ?_⟩
            · simp [vertexTrace, predecessorVertex, predecessor_eq]
            · simpa [predecessorVertex, predecessor_eq] using closes
            · intro step step_pos step_lt
              omega
          · have tail_returns :
                (collectCycle predecessor base fuel edge.source (edge :: path)).ret =
                  some output := by
              simpa [collectCycle, predecessor_eq, closes] using returns
            obtain ⟨steps, steps_pos, steps_le, output_sources, reaches,
                first_return⟩ := induction edge.source (edge :: path) tail_returns
            refine ⟨steps + 1, by omega, by omega, ?_, ?_, ?_⟩
            · rw [output_sources]
              simp [vertexTrace, predecessorVertex, predecessor_eq, List.reverse_cons,
                List.append_assoc]
            · rw [show steps + 1 = steps.succ by omega,
                Function.iterate_succ_apply, predecessorVertex, predecessor_eq]
              exact reaches
            · intro step step_pos step_lt step_returns
              by_cases step_one : step = 1
              · subst step
                simp [predecessorVertex, predecessor_eq] at step_returns
                exact closes step_returns
              · have tail_step_pos : 0 < step - 1 := by omega
                have tail_step_lt : step - 1 < steps := by omega
                apply first_return (step - 1) tail_step_pos tail_step_lt
                rw [show step = (step - 1).succ by omega,
                  Function.iterate_succ_apply, predecessorVertex, predecessor_eq] at step_returns
                exact step_returns

theorem collectCycle_sources_nodup {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (base : Fin n)
    (fuel : Nat) (output : List (Edge n))
    (returns : (collectCycle predecessor base fuel base []).ret = some output) :
    (output.map Edge.source).Nodup := by
  obtain ⟨steps, _, _, output_sources, periodic, first_return⟩ :=
    collectCycle_trace_spec predecessor base fuel base [] output returns
  have trace_nodup := vertexTrace_nodup_of_first_return
    (predecessorVertex predecessor) base steps periodic first_return
  rw [List.map_nil, List.append_nil] at output_sources
  rw [output_sources]
  exact trace_nodup.reverse.imp Ne.symm

theorem collectCycle_spec {n : Nat} {edges : List (Edge n)}
    {state : State n} (valid : state.CurrentSnapshotsValid)
    (from_edges : state.PredecessorsFrom edges) (base : Fin n)
    (fuel : Nat) (current : Fin n) (path output : List (Edge n))
    (path_valid : IsWeightedPath edges current base path)
    (path_predecessors : ∀ edge ∈ path,
      state.predecessor.get edge.target = some edge)
    (returns : (collectCycle state.predecessor base fuel current path).ret = some output) :
    IsWeightedPath edges base base output ∧ output ≠ [] ∧
      ∀ edge ∈ output, state.predecessor.get edge.target = some edge := by
  induction fuel generalizing current path with
  | zero => simp [collectCycle] at returns
  | succ fuel induction =>
      cases predecessor_eq : state.predecessor.get current with
      | none => simp [collectCycle, predecessor_eq] at returns
      | some edge =>
          obtain ⟨edge_mem, edge_target, _, _, _, _, _⟩ :=
            state.predecessor_step valid from_edges predecessor_eq
          have extended_valid : IsWeightedPath edges edge.source base (edge :: path) :=
            isWeightedPath_cons edge_mem rfl (edge_target ▸ path_valid)
          have extended_predecessors : ∀ item ∈ edge :: path,
              state.predecessor.get item.target = some item := by
            intro item item_mem
            simp only [List.mem_cons] at item_mem
            rcases item_mem with rfl | item_mem
            · simpa [edge_target] using predecessor_eq
            · exact path_predecessors item item_mem
          by_cases closes : edge.source = base
          · have output_eq : output = edge :: path := by
              simpa [collectCycle, predecessor_eq, closes] using returns.symm
            subst output
            exact ⟨closes ▸ extended_valid, by simp, extended_predecessors⟩
          · have tail_returns :
                (collectCycle state.predecessor base fuel edge.source (edge :: path)).ret =
                  some output := by
              simpa [collectCycle, predecessor_eq, closes] using returns
            exact induction edge.source (edge :: path) extended_valid extended_predecessors
              tail_returns

theorem predecessor_path_bound {n : Nat} {edges : List (Edge n)}
    {state : State n} (valid : state.CurrentSnapshotsValid)
    (from_edges : state.PredecessorsFrom edges) {source target : Fin n}
    {path : List (Edge n)} (path_valid : IsWeightedPath edges source target path)
    (path_predecessors : ∀ edge ∈ path,
      state.predecessor.get edge.target = some edge)
    (sourceDistance : Int)
    (source_eq : state.distance.get source = some sourceDistance) :
    ∃ targetDistance,
      state.distance.get target = some targetDistance ∧
        sourceDistance + pathWeight path ≤ targetDistance := by
  induction path generalizing source sourceDistance with
  | nil =>
      have source_target : source = target := path_valid.2.2
      subst target
      exact ⟨sourceDistance, source_eq, by simp [pathWeight]⟩
  | cons edge rest induction =>
      have predecessor_eq := path_predecessors edge (by simp)
      obtain ⟨_, edge_target, edgeSourceDistance, edgeTargetDistance,
          edge_source_eq, edge_target_eq, edge_le⟩ :=
        state.predecessor_step valid from_edges predecessor_eq
      have edge_source : edge.source = source := path_valid.2.2.1
      have source_value : edgeSourceDistance = sourceDistance :=
        Option.some.inj ((edge_source ▸ edge_source_eq).symm.trans source_eq)
      subst edgeSourceDistance
      obtain ⟨targetDistance, target_eq, tail_le⟩ :=
        induction (isWeightedPath_tail path_valid)
          (fun item item_mem => path_predecessors item (by simp [item_mem]))
          edgeTargetDistance edge_target_eq
      refine ⟨targetDistance, target_eq, ?_⟩
      simp only [pathWeight, List.map_cons, List.sum_cons]
      rw [show (List.map Edge.weight rest).sum = pathWeight rest by rfl]
      omega

theorem predecessor_cycle_nonpositive {n : Nat} {edges : List (Edge n)}
    {state : State n} (valid : state.CurrentSnapshotsValid)
    (from_edges : state.PredecessorsFrom edges) {base : Fin n}
    {cycle : List (Edge n)} (cycle_valid : IsWeightedPath edges base base cycle)
    (cycle_predecessors : ∀ edge ∈ cycle,
      state.predecessor.get edge.target = some edge)
    (baseDistance : Int)
    (base_eq : state.distance.get base = some baseDistance) :
    pathWeight cycle ≤ 0 := by
  obtain ⟨targetDistance, target_eq, cycle_le⟩ :=
    predecessor_path_bound valid from_edges cycle_valid cycle_predecessors
      baseDistance base_eq
  have target_value : targetDistance = baseDistance :=
    Option.some.inj (target_eq.symm.trans base_eq)
  subst targetDistance
  omega

def State.PredecessorStrict {n : Nat} (state : State n)
    (edge : Edge n) : Prop :=
  ∃ sourceDistance targetDistance,
    state.distance.get edge.source = some sourceDistance ∧
      state.distance.get edge.target = some targetDistance ∧
      sourceDistance + edge.weight < targetDistance

theorem State.predecessor_ordinal_lt_of_not_strict {n : Nat}
    {state : State n} (valid : state.CurrentSnapshotsValid)
    {target : Fin n} {edge sourceEdge : Edge n}
    (target_predecessor : state.predecessor.get target = some edge)
    (source_predecessor : state.predecessor.get edge.source = some sourceEdge)
    (not_strict : ¬state.PredecessorStrict edge) :
    ∃ sourceOrdinal targetOrdinal,
      state.predecessorUpdateOrdinal.get edge.source = some sourceOrdinal ∧
        state.predecessorUpdateOrdinal.get target = some targetOrdinal ∧
        sourceOrdinal < targetOrdinal := by
  obtain ⟨snapshotSource, targetDistance, targetOrdinal, sourceOrdinal,
      _, _, target_ordinal_eq, _, edge_target, target_distance, target_formula,
      ⟨sourceDistance, source_distance, source_le⟩,
      source_ordinal_current, source_ordinal_lt⟩ :=
    valid target edge target_predecessor
  have tight : sourceDistance + edge.weight = targetDistance := by
    by_contra different
    apply not_strict
    refine ⟨sourceDistance, targetDistance, source_distance,
      by simpa [edge_target] using target_distance, ?_⟩
    omega
  have source_value : sourceDistance = snapshotSource := by omega
  subst sourceDistance
  have captured_eq := source_ordinal_current source_distance
  obtain ⟨_, _, sourceOrdinalValue, _, _, _, source_ordinal_eq, _, _, _, _, _, _, _⟩ :=
    valid edge.source sourceEdge source_predecessor
  have captured_value : sourceOrdinal = some sourceOrdinalValue := by
    rw [← captured_eq, source_ordinal_eq]
  exact ⟨sourceOrdinalValue, targetOrdinal, source_ordinal_eq, target_ordinal_eq,
    source_ordinal_lt sourceOrdinalValue captured_value⟩

theorem predecessor_path_ordinal_lt {n : Nat} {edges : List (Edge n)}
    {state : State n} (valid : state.CurrentSnapshotsValid)
    {source target : Fin n} {path : List (Edge n)}
    (path_valid : IsWeightedPath edges source target path) (path_ne : path ≠ [])
    (path_predecessors : ∀ edge ∈ path,
      state.predecessor.get edge.target = some edge)
    (not_strict : ∀ edge ∈ path, ¬state.PredecessorStrict edge)
    (sourceEdge : Edge n)
    (source_predecessor : state.predecessor.get source = some sourceEdge) :
    ∃ sourceOrdinal targetOrdinal,
      state.predecessorUpdateOrdinal.get source = some sourceOrdinal ∧
        state.predecessorUpdateOrdinal.get target = some targetOrdinal ∧
        sourceOrdinal < targetOrdinal := by
  induction path generalizing source sourceEdge with
  | nil => contradiction
  | cons edge rest induction =>
      have edge_source : edge.source = source := path_valid.2.2.1
      have edge_predecessor := path_predecessors edge (by simp)
      obtain ⟨sourceOrdinal, edgeOrdinal, source_ordinal_eq, edge_ordinal_eq,
          head_lt⟩ :=
        state.predecessor_ordinal_lt_of_not_strict valid edge_predecessor
          (edge_source ▸ source_predecessor) (not_strict edge (by simp))
      cases rest with
      | nil =>
          have edge_target : edge.target = target := by
            simpa [IsWeightedPath] using isWeightedPath_tail path_valid
          subst target
          exact ⟨sourceOrdinal, edgeOrdinal,
            edge_source ▸ source_ordinal_eq, edge_ordinal_eq, head_lt⟩
      | cons next tail =>
          obtain ⟨restSourceOrdinal, targetOrdinal, rest_source_eq,
              target_ordinal_eq, tail_lt⟩ :=
            induction (isWeightedPath_tail path_valid) (by simp)
              (fun item item_mem => path_predecessors item (by simp [item_mem]))
              (fun item item_mem => not_strict item (by simp [item_mem]))
              edge edge_predecessor
          have ordinal_eq : edgeOrdinal = restSourceOrdinal :=
            Option.some.inj (edge_ordinal_eq.symm.trans rest_source_eq)
          subst restSourceOrdinal
          exact ⟨sourceOrdinal, targetOrdinal,
            edge_source ▸ source_ordinal_eq, target_ordinal_eq, head_lt.trans tail_lt⟩

theorem predecessor_path_bound_strict {n : Nat} {edges : List (Edge n)}
    {state : State n} (valid : state.CurrentSnapshotsValid)
    (from_edges : state.PredecessorsFrom edges) {source target : Fin n}
    {path : List (Edge n)} (path_valid : IsWeightedPath edges source target path)
    (path_predecessors : ∀ edge ∈ path,
      state.predecessor.get edge.target = some edge)
    (strict : ∃ edge ∈ path, state.PredecessorStrict edge)
    (sourceDistance : Int)
    (source_eq : state.distance.get source = some sourceDistance) :
    ∃ targetDistance,
      state.distance.get target = some targetDistance ∧
        sourceDistance + pathWeight path < targetDistance := by
  induction path generalizing source sourceDistance with
  | nil => simp at strict
  | cons edge rest induction =>
      have predecessor_eq := path_predecessors edge (by simp)
      obtain ⟨_, edge_target, edgeSourceDistance, edgeTargetDistance,
          edge_source_eq, edge_target_eq, edge_le⟩ :=
        state.predecessor_step valid from_edges predecessor_eq
      have edge_source : edge.source = source := path_valid.2.2.1
      have source_value : edgeSourceDistance = sourceDistance :=
        Option.some.inj ((edge_source ▸ edge_source_eq).symm.trans source_eq)
      subst edgeSourceDistance
      rcases strict with ⟨strictEdge, strict_mem, strict_edge⟩
      simp only [List.mem_cons] at strict_mem
      rcases strict_mem with strict_head | strict_tail
      · subst strictEdge
        obtain ⟨strictSource, strictTarget, strict_source_eq, strict_target_eq,
            edge_strict⟩ := strict_edge
        have strict_source_value : strictSource = sourceDistance :=
          Option.some.inj (strict_source_eq.symm.trans edge_source_eq)
        have strict_target_value : strictTarget = edgeTargetDistance :=
          Option.some.inj (strict_target_eq.symm.trans edge_target_eq)
        subst strictSource
        subst strictTarget
        obtain ⟨targetDistance, target_eq, tail_le⟩ :=
          predecessor_path_bound valid from_edges (isWeightedPath_tail path_valid)
            (fun item item_mem => path_predecessors item (by simp [item_mem]))
            edgeTargetDistance edge_target_eq
        refine ⟨targetDistance, target_eq, ?_⟩
        simp only [pathWeight, List.map_cons, List.sum_cons]
        rw [show (List.map Edge.weight rest).sum = pathWeight rest by rfl]
        omega
      · obtain ⟨targetDistance, target_eq, tail_lt⟩ :=
          induction (isWeightedPath_tail path_valid)
            (fun item item_mem => path_predecessors item (by simp [item_mem]))
            ⟨strictEdge, strict_tail, strict_edge⟩ edgeTargetDistance edge_target_eq
        refine ⟨targetDistance, target_eq, ?_⟩
        simp only [pathWeight, List.map_cons, List.sum_cons]
        rw [show (List.map Edge.weight rest).sum = pathWeight rest by rfl]
        omega

theorem predecessor_cycle_negative {n : Nat} {edges : List (Edge n)}
    {state : State n} (valid : state.CurrentSnapshotsValid)
    (from_edges : state.PredecessorsFrom edges) {base : Fin n}
    {cycle : List (Edge n)} (cycle_valid : IsWeightedPath edges base base cycle)
    (cycle_nonempty : cycle ≠ [])
    (cycle_predecessors : ∀ edge ∈ cycle,
      state.predecessor.get edge.target = some edge) :
    pathWeight cycle < 0 := by
  obtain ⟨baseEdge, base_predecessor⟩ :
      ∃ edge, state.predecessor.get base = some edge := by
    induction cycle using List.reverseRecOn with
    | nil => contradiction
    | append_singleton path edge _ =>
        obtain ⟨_, _, edge_target⟩ := isWeightedPath_append_edge_iff.mp cycle_valid
        exact ⟨edge, by
          simpa [edge_target] using cycle_predecessors edge (by simp)⟩
  obtain ⟨_, _, _, baseDistance, _, base_distance, _⟩ :=
    state.predecessor_step valid from_edges base_predecessor
  have nonpositive := predecessor_cycle_nonpositive valid from_edges cycle_valid
    cycle_predecessors baseDistance base_distance
  by_contra not_negative
  have weight_zero : pathWeight cycle = 0 := by omega
  have no_strict : ∀ edge ∈ cycle, ¬state.PredecessorStrict edge := by
    intro edge edge_mem edge_strict
    obtain ⟨targetDistance, target_distance, strict_bound⟩ :=
      predecessor_path_bound_strict valid from_edges cycle_valid cycle_predecessors
        ⟨edge, edge_mem, edge_strict⟩ baseDistance base_distance
    have target_value : targetDistance = baseDistance :=
      Option.some.inj (target_distance.symm.trans base_distance)
    subst targetDistance
    omega
  obtain ⟨sourceOrdinal, targetOrdinal, source_ordinal_eq, target_ordinal_eq,
      ordinal_lt⟩ :=
    predecessor_path_ordinal_lt valid cycle_valid cycle_nonempty cycle_predecessors
      no_strict baseEdge base_predecessor
  have ordinal_eq : sourceOrdinal = targetOrdinal :=
    Option.some.inj (source_ordinal_eq.symm.trans target_ordinal_eq)
  omega

def collectPrefix {n : Nat} (predecessor : Vector (Option (Edge n)) n)
    (source : Fin n) : Nat → Fin n → List (Edge n) → TimeM Cost (Option (List (Edge n)))
  | 0, current, path => if current = source then pure (some path) else pure none
  | fuel + 1, current, path =>
      if current = source then
        pure (some path)
      else do
        let _ ← TimeM.tick ⟨0, 1⟩
        match predecessor.get current with
        | none => pure none
        | some edge => collectPrefix predecessor source fuel edge.source (edge :: path)

def discoveryVertex {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (current : Fin n) : Fin n :=
  match predecessor.get current with
  | none => current
  | some edge => edge.source

theorem State.DiscoveryValid.step {n : Nat} {edges : List (Edge n)}
    {source : Fin n} {state : State n} (valid : state.DiscoveryValid edges source)
    {current : Fin n} {distance : Int} {rank : Nat}
    (current_distance : state.distance.get current = some distance)
    (current_rank : state.discoveryRank.get current = some rank)
    (current_ne_source : current ≠ source) :
    ∃ edge sourceRank sourceDistance,
      state.discoveryPredecessor.get current = some edge ∧ edge.target = current ∧
        state.discoveryRank.get edge.source = some sourceRank ∧ sourceRank < rank ∧
        state.distance.get edge.source = some sourceDistance := by
  obtain ⟨edge, predecessor_eq⟩ :=
    valid.finite_predecessor current distance current_distance current_ne_source
  obtain ⟨_, edge_target, sourceRank, targetRank, source_rank, target_rank, rank_lt⟩ :=
    valid.predecessor_spec current edge predecessor_eq
  have target_rank_value : targetRank = rank :=
    Option.some.inj (target_rank.symm.trans current_rank)
  subst targetRank
  obtain ⟨sourceDistance, source_distance⟩ :=
    valid.rank_finite edge.source sourceRank source_rank
  exact ⟨edge, sourceRank, sourceDistance, predecessor_eq, edge_target, source_rank,
    rank_lt, source_distance⟩

theorem collectPrefix_none_trace {n : Nat} {edges : List (Edge n)}
    {source : Fin n} {state : State n} (valid : state.DiscoveryValid edges source)
    (fuel : Nat) (current : Fin n) (path : List (Edge n)) (distance : Int)
    (current_distance : state.distance.get current = some distance)
    (returns :
      (collectPrefix state.discoveryPredecessor source fuel current path).ret = none) :
    ∃ rank,
      state.discoveryRank.get current = some rank ∧
        let vertices := current ::
          vertexTrace (discoveryVertex state.discoveryPredecessor) fuel current
        vertices.Nodup ∧ source ∉ vertices ∧
          ∀ vertex ∈ vertices,
            ∃ vertexRank,
              state.discoveryRank.get vertex = some vertexRank ∧ vertexRank ≤ rank := by
  induction fuel generalizing current path distance with
  | zero =>
      have current_ne_source : current ≠ source := by
        intro current_source
        subst current
        simp [collectPrefix] at returns
      obtain ⟨rank, rank_eq⟩ := valid.finite_rank current distance current_distance
      refine ⟨rank, rank_eq, ?_⟩
      dsimp [vertexTrace]
      refine ⟨by simp, by simpa using current_ne_source.symm, ?_⟩
      intro vertex vertex_mem
      simp only [List.mem_singleton] at vertex_mem
      subst vertex
      exact ⟨rank, rank_eq, le_rfl⟩
  | succ fuel induction =>
      have current_ne_source : current ≠ source := by
        intro current_source
        subst current
        simp [collectPrefix] at returns
      obtain ⟨rank, rank_eq⟩ := valid.finite_rank current distance current_distance
      obtain ⟨edge, sourceRank, sourceDistance, predecessor_eq, _, source_rank,
          source_rank_lt, source_distance⟩ :=
        valid.step current_distance rank_eq current_ne_source
      have tail_returns :
          (collectPrefix state.discoveryPredecessor source fuel edge.source
            (edge :: path)).ret = none := by
        simpa [collectPrefix, current_ne_source, predecessor_eq] using returns
      obtain ⟨tailRank, tail_rank_eq, tail_nodup, source_not_tail, tail_bound⟩ :=
        induction edge.source (edge :: path) sourceDistance source_distance tail_returns
      have tail_rank_value : tailRank = sourceRank :=
        Option.some.inj (tail_rank_eq.symm.trans source_rank)
      subst tailRank
      let tailVertices := edge.source ::
        vertexTrace (discoveryVertex state.discoveryPredecessor) fuel edge.source
      have current_not_tail : current ∉ tailVertices := by
        intro current_mem
        obtain ⟨vertexRank, vertex_rank_eq, vertex_rank_le⟩ :=
          tail_bound current current_mem
        have vertex_rank_value : vertexRank = rank :=
          Option.some.inj (vertex_rank_eq.symm.trans rank_eq)
        subst vertexRank
        omega
      refine ⟨rank, rank_eq, ?_⟩
      dsimp only
      rw [vertexTrace, discoveryVertex, predecessor_eq]
      change (current :: tailVertices).Nodup ∧ source ∉ current :: tailVertices ∧ _
      refine ⟨List.nodup_cons.mpr ⟨current_not_tail, tail_nodup⟩,
        by
          intro source_mem
          simp only [List.mem_cons] at source_mem
          rcases source_mem with source_current | source_mem
          · exact current_ne_source source_current.symm
          · exact source_not_tail source_mem,
        ?_⟩
      intro vertex vertex_mem
      simp only [List.mem_cons] at vertex_mem
      rcases vertex_mem with rfl | vertex_mem
      · exact ⟨rank, rank_eq, le_rfl⟩
      · obtain ⟨vertexRank, vertex_rank_eq, vertex_rank_le⟩ :=
          tail_bound vertex (by simpa [tailVertices] using vertex_mem)
        exact ⟨vertexRank, vertex_rank_eq, vertex_rank_le.trans source_rank_lt.le⟩

theorem collectPrefix_some_of_finite {n : Nat} {edges : List (Edge n)}
    {source : Fin n} {state : State n} (valid : state.DiscoveryValid edges source)
    (current : Fin n) (distance : Int)
    (current_distance : state.distance.get current = some distance) :
    ∃ path,
      (collectPrefix state.discoveryPredecessor source (n - 1) current []).ret =
        some path := by
  cases path_eq :
      (collectPrefix state.discoveryPredecessor source (n - 1) current []).ret with
  | some path => exact ⟨path, rfl⟩
  | none =>
      obtain ⟨_, _, vertices_nodup, source_not_vertices, _⟩ :=
        collectPrefix_none_trace valid (n - 1) current [] distance current_distance path_eq
      let vertices := current ::
        vertexTrace (discoveryVertex state.discoveryPredecessor) (n - 1) current
      have all_nodup : (source :: vertices).Nodup :=
        List.nodup_cons.mpr ⟨source_not_vertices, vertices_nodup⟩
      have length_le := all_nodup.length_le_card
      have n_pos : 0 < n := Nat.zero_lt_of_lt source.isLt
      dsimp [vertices] at length_le
      rw [vertexTrace_eq_ofFn] at length_le
      simp at length_le
      omega

theorem collectPrefix_spec {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {state : State n}
    (valid : state.DiscoveryValid edges source) (fuel : Nat) (current : Fin n)
    (path output : List (Edge n))
    (path_valid : IsWeightedPath edges current target path)
    (path_predecessors : ∀ edge ∈ path,
      state.discoveryPredecessor.get edge.target = some edge)
    (returns :
      (collectPrefix state.discoveryPredecessor source fuel current path).ret = some output) :
    IsWeightedPath edges source target output ∧
      ∀ edge ∈ output, state.discoveryPredecessor.get edge.target = some edge := by
  induction fuel generalizing current path with
  | zero =>
      by_cases current_source : current = source
      · have output_eq : output = path := by
          simpa [collectPrefix, current_source] using returns.symm
        subst output
        exact ⟨current_source ▸ path_valid, path_predecessors⟩
      · simp [collectPrefix, current_source] at returns
  | succ fuel induction =>
      by_cases current_source : current = source
      · have output_eq : output = path := by
          simpa [collectPrefix, current_source] using returns.symm
        subst output
        exact ⟨current_source ▸ path_valid, path_predecessors⟩
      · cases predecessor_eq : state.discoveryPredecessor.get current with
        | none => simp [collectPrefix, current_source, predecessor_eq] at returns
        | some edge =>
            obtain ⟨edge_mem, edge_target, _, _, _, _, _⟩ :=
              valid.predecessor_spec current edge predecessor_eq
            have extended_valid : IsWeightedPath edges edge.source target (edge :: path) :=
              isWeightedPath_cons edge_mem rfl (edge_target ▸ path_valid)
            have extended_predecessors : ∀ item ∈ edge :: path,
                state.discoveryPredecessor.get item.target = some item := by
              intro item item_mem
              simp only [List.mem_cons] at item_mem
              rcases item_mem with rfl | item_mem
              · simpa [edge_target] using predecessor_eq
              · exact path_predecessors item item_mem
            have tail_returns :
                (collectPrefix state.discoveryPredecessor source fuel edge.source
                  (edge :: path)).ret = some output := by
              simpa [collectPrefix, current_source, predecessor_eq] using returns
            exact induction edge.source (edge :: path) extended_valid extended_predecessors
              tail_returns

def discoveryRankValue {n : Nat} (state : State n) (vertex : Fin n) : Nat :=
  (state.discoveryRank.get vertex).getD 0

theorem discovery_path_rank_chain {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {state : State n}
    (predecessor_spec : ∀ vertex edge,
      state.discoveryPredecessor.get vertex = some edge →
        edge ∈ edges ∧ edge.target = vertex ∧
          ∃ sourceRank targetRank,
            state.discoveryRank.get edge.source = some sourceRank ∧
              state.discoveryRank.get vertex = some targetRank ∧ sourceRank < targetRank)
    {path : List (Edge n)}
    (path_valid : IsWeightedPath edges source target path)
    (path_predecessors : ∀ edge ∈ path,
      state.discoveryPredecessor.get edge.target = some edge) :
    ((pathVertices source path).map (discoveryRankValue state)).IsChain (fun left right =>
      left < right) := by
  induction path generalizing source with
  | nil => simp [pathVertices]
  | cons edge rest induction =>
      have edge_source : edge.source = source := path_valid.2.2.1
      have predecessor_eq := path_predecessors edge (by simp)
      obtain ⟨_, _, sourceRank, targetRank, source_rank, target_rank, rank_lt⟩ :=
        predecessor_spec edge.target edge predecessor_eq
      have tail_chain := induction (isWeightedPath_tail path_valid)
        (fun item item_mem => path_predecessors item (by simp [item_mem]))
      change List.IsChain (fun left right : Nat => left < right)
        (discoveryRankValue state source ::
          (pathVertices edge.target rest).map (discoveryRankValue state))
      apply List.IsChain.cons tail_chain
      intro value value_head
      have value_eq : value = discoveryRankValue state edge.target := by
        simpa [pathVertices] using value_head.symm
      subst value
      have source_rank' : state.discoveryRank.get source = some sourceRank := by
        simpa only [edge_source] using source_rank
      simp only [discoveryRankValue]
      rw [source_rank', target_rank]
      exact rank_lt

theorem discovery_path_nodup {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {state : State n}
    (valid : state.DiscoveryValid edges source) {path : List (Edge n)}
    (path_valid : IsWeightedPath edges source target path)
    (path_predecessors : ∀ edge ∈ path,
      state.discoveryPredecessor.get edge.target = some edge) :
    (pathVertices source path).Nodup := by
  have chain := discovery_path_rank_chain valid.predecessor_spec path_valid path_predecessors
  rw [List.isChain_iff_pairwise] at chain
  have rank_nodup : ((pathVertices source path).map
      (discoveryRankValue state)).Nodup := chain.imp (fun less => Nat.ne_of_lt less)
  exact rank_nodup.of_map _

def allMemDecidable {α : Type} [DecidableEq α] (left right : List α) :
    Decidable (∀ item ∈ left, item ∈ right) := by
  induction left with
  | nil => exact isTrue (by simp)
  | cons item rest induction =>
      if item_mem : item ∈ right then
        match induction with
        | isTrue rest_mem => exact isTrue (by simp_all)
        | isFalse rest_not_mem => exact isFalse (by simp_all)
      else
        exact isFalse (by simp_all)

def isWeightedPathDecidable {n : Nat} (edges : List (Edge n))
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

def makeWitness? {n : Nat} (edges : List (Edge n)) (source base : Fin n)
    («prefix» cycle : List (Edge n)) : Option (ReachableNegativeCycle edges source) :=
  letI : Decidable (IsWeightedPath edges source base «prefix») :=
    isWeightedPathDecidable edges source base «prefix»
  letI : Decidable (IsWeightedPath edges base base cycle) :=
    isWeightedPathDecidable edges base base cycle
  if prefix_valid : IsWeightedPath edges source base «prefix» then
    if prefix_simple : (pathVertices source «prefix»).Nodup then
      if cycle_valid : IsWeightedPath edges base base cycle then
        if cycle_nonempty : cycle ≠ [] then
          if cycle_simple : (cycle.map Edge.source).Nodup then
            if cycle_negative : pathWeight cycle < 0 then
              some {
                base := base
                «prefix» := «prefix»
                cycle := cycle
                prefix_valid := prefix_valid
                prefix_simple := prefix_simple
                cycle_valid := cycle_valid
                cycle_nonempty := cycle_nonempty
                cycle_simple := cycle_simple
                cycle_negative := cycle_negative }
            else none
          else none
        else none
      else none
    else none
  else none

theorem makeWitness_some_of_spec {n : Nat} (edges : List (Edge n))
    (source base : Fin n) (path cycle : List (Edge n))
    (path_valid : IsWeightedPath edges source base path)
    (path_simple : (pathVertices source path).Nodup)
    (cycle_valid : IsWeightedPath edges base base cycle)
    (cycle_nonempty : cycle ≠ [])
    (cycle_simple : (cycle.map Edge.source).Nodup)
    (cycle_negative : pathWeight cycle < 0) :
    ∃ witness,
      makeWitness? edges source base path cycle = some witness := by
  unfold makeWitness?
  simp [path_valid, path_simple, cycle_valid, cycle_nonempty, cycle_simple, cycle_negative]

theorem makeWitness_fields {n : Nat} (edges : List (Edge n))
    (source base : Fin n) («prefix» cycle : List (Edge n))
    (witness : ReachableNegativeCycle edges source)
    (returns : makeWitness? edges source base «prefix» cycle = some witness) :
    witness.base = base ∧ witness.prefix = «prefix» ∧ witness.cycle = cycle := by
  unfold makeWitness? at returns
  split at returns <;> try contradiction
  split at returns <;> try contradiction
  split at returns <;> try contradiction
  split at returns <;> try contradiction
  split at returns <;> try contradiction
  split at returns <;> try contradiction
  cases returns
  simp

def State.toDistances {n : Nat} (state : State n) (source : Fin n) : Distances n where
  source := source
  distance := state.distance
  predecessor := state.predecessor

def finish {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (state : State n) : TimeM Cost (Result edges source) := do
  match state.lastUpdated with
  | none => pure (.distances (state.toDistances source))
  | some updated =>
      let some base ← localizeCycle state.predecessor n updated
        | pure (.distances (state.toDistances source))
      let some cycle ← collectCycle state.predecessor base n base []
        | pure (.distances (state.toDistances source))
      let some «prefix» ←
          collectPrefix state.discoveryPredecessor source (n - 1) base []
        | pure (.distances (state.toDistances source))
      match makeWitness? edges source base «prefix» cycle with
      | none => pure (.distances (state.toDistances source))
      | some witness => pure (.negativeCycle witness)

def bellmanFord {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    TimeM Cost (Result edges source) := do
  let state ← runPasses edges (n - 1) (initialState source)
  let state ← relaxEdges edges { state with lastUpdated := none }
  finish edges source state


end Internal

end Cslib.Algorithms.Lean.BellmanFord
