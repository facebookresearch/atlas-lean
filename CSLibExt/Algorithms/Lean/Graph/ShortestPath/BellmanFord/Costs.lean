/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Correctness
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Correctness

/-! # Bellman-Ford exact cost accounting -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BellmanFord

namespace Internal

theorem relaxEdges_relaxationChecks {n : Nat} (edges : List (Edge n))
    (state : State n) :
    (relaxEdges edges state).time.relaxationChecks = edges.length := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.time_bind, TimeM.time_tick,
        Cost.add_relaxationChecks]
      change 1 + (relaxEdges rest (relaxOne state edge)).time.relaxationChecks =
        rest.length + 1
      rw [induction]
      omega

theorem relaxEdges_cycleWitnessSteps {n : Nat} (edges : List (Edge n))
    (state : State n) :
    (relaxEdges edges state).time.cycleWitnessSteps = 0 := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest induction =>
      simp only [relaxEdges, TimeM.time_bind, TimeM.time_tick,
        Cost.add_cycleWitnessSteps, Nat.zero_add]
      exact induction _

theorem runPasses_relaxationChecks {n : Nat} (edges : List (Edge n))
    (passes : Nat) (state : State n) :
    (runPasses edges passes state).time.relaxationChecks = passes * edges.length := by
  induction passes generalizing state with
  | zero => simp [runPasses]
  | succ passes induction =>
      simp only [runPasses, TimeM.time_bind, Cost.add_relaxationChecks]
      rw [relaxEdges_relaxationChecks, induction]
      simp [Nat.succ_mul, Nat.add_comm]

theorem runPasses_cycleWitnessSteps {n : Nat} (edges : List (Edge n))
    (passes : Nat) (state : State n) :
    (runPasses edges passes state).time.cycleWitnessSteps = 0 := by
  induction passes generalizing state with
  | zero => simp [runPasses]
  | succ passes induction =>
      simp only [runPasses, TimeM.time_bind, Cost.add_cycleWitnessSteps]
      rw [relaxEdges_cycleWitnessSteps, induction]

theorem runPasses_nil_ret {n : Nat} (passes : Nat) (state : State n) :
    (runPasses [] passes state).ret = state := by
  induction passes generalizing state with
  | zero => rfl
  | succ passes induction =>
      simpa [runPasses, relaxEdges] using induction state

theorem localizeCycle_relaxationChecks {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (steps : Nat) (current : Fin n) :
    (localizeCycle predecessor steps current).time.relaxationChecks = 0 := by
  induction steps generalizing current with
  | zero => simp [localizeCycle]
  | succ steps induction =>
      simp only [localizeCycle, TimeM.time_bind, TimeM.time_tick,
        Cost.add_relaxationChecks, Nat.zero_add]
      cases predecessor.get current with
      | none => simp
      | some edge => exact induction edge.source

theorem localizeCycle_steps_le {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (steps : Nat) (current : Fin n) :
    (localizeCycle predecessor steps current).time.cycleWitnessSteps ≤ steps := by
  induction steps generalizing current with
  | zero => simp [localizeCycle]
  | succ steps induction =>
      simp only [localizeCycle, TimeM.time_bind, TimeM.time_tick,
        Cost.add_cycleWitnessSteps]
      cases predecessor.get current with
      | none => simp
      | some edge =>
          calc
            1 + (localizeCycle predecessor steps edge.source).time.cycleWitnessSteps ≤
                1 + steps := Nat.add_le_add_left (induction edge.source) 1
            _ = steps + 1 := Nat.add_comm _ _

theorem localizeCycle_steps_eq_of_ret_some {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (steps : Nat) (current base : Fin n)
    (returns : (localizeCycle predecessor steps current).ret = some base) :
    (localizeCycle predecessor steps current).time.cycleWitnessSteps = steps := by
  induction steps generalizing current with
  | zero => simp [localizeCycle]
  | succ steps induction =>
      cases predecessor_eq : predecessor.get current with
      | none => simp [localizeCycle, predecessor_eq] at returns
      | some edge =>
          have tail_returns :
              (localizeCycle predecessor steps edge.source).ret = some base := by
            simpa [localizeCycle, predecessor_eq] using returns
          simp only [localizeCycle, TimeM.time_bind, TimeM.time_tick,
            Cost.add_cycleWitnessSteps, predecessor_eq]
          rw [induction edge.source tail_returns]
          omega

theorem collectCycle_relaxationChecks {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (base : Fin n)
    (fuel : Nat) (current : Fin n) (path : List (Edge n)) :
    (collectCycle predecessor base fuel current path).time.relaxationChecks = 0 := by
  induction fuel generalizing current path with
  | zero => simp [collectCycle]
  | succ fuel induction =>
      simp only [collectCycle, TimeM.time_bind, TimeM.time_tick,
        Cost.add_relaxationChecks, Nat.zero_add]
      cases predecessor.get current with
      | none => simp
      | some edge =>
          by_cases closes : edge.source = base
          · simp [closes]
          · simp [closes, induction]

theorem collectCycle_steps_le {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (base : Fin n)
    (fuel : Nat) (current : Fin n) (path : List (Edge n)) :
    (collectCycle predecessor base fuel current path).time.cycleWitnessSteps ≤ fuel := by
  induction fuel generalizing current path with
  | zero => simp [collectCycle]
  | succ fuel induction =>
      simp only [collectCycle, TimeM.time_bind, TimeM.time_tick,
        Cost.add_cycleWitnessSteps]
      cases predecessor.get current with
      | none => simp
      | some edge =>
          by_cases closes : edge.source = base
          · simp [closes]
          · simp only [closes, ↓reduceIte]
            calc
              1 + (collectCycle predecessor base fuel edge.source
                  (edge :: path)).time.cycleWitnessSteps ≤ 1 + fuel :=
                Nat.add_le_add_left (induction edge.source (edge :: path)) 1
              _ = fuel + 1 := Nat.add_comm _ _

theorem collectCycle_length_eq_of_ret_some {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (base : Fin n)
    (fuel : Nat) (current : Fin n) (path output : List (Edge n))
    (returns : (collectCycle predecessor base fuel current path).ret = some output) :
    path.length + (collectCycle predecessor base fuel current path).time.cycleWitnessSteps =
      output.length := by
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
            simp [collectCycle, predecessor_eq, closes]
          · have tail_returns :
                (collectCycle predecessor base fuel edge.source (edge :: path)).ret =
                  some output := by
              simpa [collectCycle, predecessor_eq, closes] using returns
            have tail_length := induction edge.source (edge :: path) tail_returns
            simp only [collectCycle, TimeM.time_bind, TimeM.time_tick,
              Cost.add_cycleWitnessSteps, predecessor_eq, closes, ↓reduceIte]
            simp only [List.length_cons] at tail_length
            omega

theorem collectPrefix_relaxationChecks {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (source : Fin n)
    (fuel : Nat) (current : Fin n) (path : List (Edge n)) :
    (collectPrefix predecessor source fuel current path).time.relaxationChecks = 0 := by
  induction fuel generalizing current path with
  | zero =>
      by_cases done : current = source <;> simp [collectPrefix, done]
  | succ fuel induction =>
      by_cases done : current = source
      · simp [collectPrefix, done]
      · simp only [collectPrefix, done, ↓reduceIte, TimeM.time_bind, TimeM.time_tick,
          Cost.add_relaxationChecks, Nat.zero_add]
        cases predecessor.get current with
        | none => simp
        | some edge => exact induction edge.source (edge :: path)

theorem collectPrefix_steps_le {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (source : Fin n)
    (fuel : Nat) (current : Fin n) (path : List (Edge n)) :
    (collectPrefix predecessor source fuel current path).time.cycleWitnessSteps ≤ fuel := by
  induction fuel generalizing current path with
  | zero =>
      by_cases done : current = source <;> simp [collectPrefix, done]
  | succ fuel induction =>
      by_cases done : current = source
      · simp [collectPrefix, done]
      · simp only [collectPrefix, done, ↓reduceIte, TimeM.time_bind, TimeM.time_tick,
          Cost.add_cycleWitnessSteps]
        cases predecessor.get current with
        | none => simp
        | some edge =>
            calc
              1 + (collectPrefix predecessor source fuel edge.source
                  (edge :: path)).time.cycleWitnessSteps ≤ 1 + fuel :=
                Nat.add_le_add_left (induction edge.source (edge :: path)) 1
              _ = fuel + 1 := Nat.add_comm _ _

theorem collectPrefix_length_eq_of_ret_some {n : Nat}
    (predecessor : Vector (Option (Edge n)) n) (source : Fin n)
    (fuel : Nat) (current : Fin n) (path output : List (Edge n))
    (returns : (collectPrefix predecessor source fuel current path).ret = some output) :
    path.length + (collectPrefix predecessor source fuel current path).time.cycleWitnessSteps =
      output.length := by
  induction fuel generalizing current path with
  | zero =>
      by_cases done : current = source
      · have output_eq : output = path := by
          simpa [collectPrefix, done] using returns.symm
        subst output
        simp [collectPrefix, done]
      · simp [collectPrefix, done] at returns
  | succ fuel induction =>
      by_cases done : current = source
      · have output_eq : output = path := by
          simpa [collectPrefix, done] using returns.symm
        subst output
        simp [collectPrefix, done]
      · cases predecessor_eq : predecessor.get current with
        | none => simp [collectPrefix, done, predecessor_eq] at returns
        | some edge =>
            have tail_returns :
                (collectPrefix predecessor source fuel edge.source (edge :: path)).ret =
                  some output := by
              simpa [collectPrefix, done, predecessor_eq] using returns
            have tail_length := induction edge.source (edge :: path) tail_returns
            simp only [collectPrefix, done, ↓reduceIte, TimeM.time_bind, TimeM.time_tick,
              Cost.add_cycleWitnessSteps, predecessor_eq]
            simp only [List.length_cons] at tail_length
            omega

theorem finish_relaxationChecks {n : Nat} (edges : List (Edge n))
    (source : Fin n) (state : State n) :
    (finish edges source state).time.relaxationChecks = 0 := by
  cases updated_eq : state.lastUpdated with
  | none => simp [finish, updated_eq]
  | some updated =>
      cases base_eq : (localizeCycle state.predecessor n updated).ret with
      | none =>
          simp [finish, updated_eq, base_eq, localizeCycle_relaxationChecks]
      | some base =>
          cases cycle_eq : (collectCycle state.predecessor base n base []).ret with
          | none =>
              simp [finish, updated_eq, base_eq, cycle_eq,
                localizeCycle_relaxationChecks, collectCycle_relaxationChecks]
          | some cycle =>
              cases prefix_eq :
                  (collectPrefix state.discoveryPredecessor source (n - 1) base []).ret with
              | none =>
                  simp [finish, updated_eq, base_eq, cycle_eq, prefix_eq,
                    localizeCycle_relaxationChecks, collectCycle_relaxationChecks,
                    collectPrefix_relaxationChecks]
              | some «prefix» =>
                  cases make_eq : makeWitness? edges source base «prefix» cycle <;>
                    simp [finish, updated_eq, base_eq, cycle_eq, prefix_eq, make_eq,
                      localizeCycle_relaxationChecks, collectCycle_relaxationChecks,
                      collectPrefix_relaxationChecks]

theorem finish_steps_le_three_mul {n : Nat} (edges : List (Edge n))
    (source : Fin n) (state : State n) :
    (finish edges source state).time.cycleWitnessSteps ≤ 3 * n := by
  cases updated_eq : state.lastUpdated with
  | none => simp [finish, updated_eq]
  | some updated =>
      have localize_le := localizeCycle_steps_le state.predecessor n updated
      cases base_eq : (localizeCycle state.predecessor n updated).ret with
      | none =>
          simp only [finish, updated_eq, TimeM.time_bind, Cost.add_cycleWitnessSteps,
            base_eq, TimeM.time_pure, Cost.zero_cycleWitnessSteps, Nat.add_zero]
          omega
      | some base =>
          have cycle_le := collectCycle_steps_le state.predecessor base n base []
          cases cycle_eq : (collectCycle state.predecessor base n base []).ret with
          | none =>
              simp only [finish, updated_eq, TimeM.time_bind, Cost.add_cycleWitnessSteps,
                base_eq, cycle_eq, TimeM.time_pure, Cost.zero_cycleWitnessSteps, Nat.add_zero]
              omega
          | some cycle =>
              have prefix_le := collectPrefix_steps_le state.discoveryPredecessor source
                (n - 1) base []
              cases prefix_eq :
                  (collectPrefix state.discoveryPredecessor source (n - 1) base []).ret with
              | none =>
                  simp only [finish, updated_eq, TimeM.time_bind, Cost.add_cycleWitnessSteps,
                    base_eq, cycle_eq, prefix_eq, TimeM.time_pure,
                    Cost.zero_cycleWitnessSteps, Nat.add_zero]
                  omega
              | some «prefix» =>
                  cases make_eq : makeWitness? edges source base «prefix» cycle <;>
                    simp only [finish, updated_eq, TimeM.time_bind,
                      Cost.add_cycleWitnessSteps, base_eq, cycle_eq, prefix_eq, make_eq,
                      TimeM.time_pure, Cost.zero_cycleWitnessSteps, Nat.add_zero] <;>
                    omega

theorem finish_steps_eq_of_negativeCycle {n : Nat} (edges : List (Edge n))
    (source : Fin n) (state : State n) (witness : ReachableNegativeCycle edges source)
    (returns : (finish edges source state).ret = Result.negativeCycle witness) :
    (finish edges source state).time.cycleWitnessSteps =
      n + witness.cycle.length + witness.prefix.length := by
  cases updated_eq : state.lastUpdated with
  | none => simp [finish, updated_eq] at returns
  | some updated =>
      cases base_eq : (localizeCycle state.predecessor n updated).ret with
      | none => simp [finish, updated_eq, base_eq] at returns
      | some base =>
          cases cycle_eq : (collectCycle state.predecessor base n base []).ret with
          | none => simp [finish, updated_eq, base_eq, cycle_eq] at returns
          | some cycle =>
              cases prefix_eq :
                  (collectPrefix state.discoveryPredecessor source (n - 1) base []).ret with
              | none => simp [finish, updated_eq, base_eq, cycle_eq, prefix_eq] at returns
              | some «prefix» =>
                  cases make_eq : makeWitness? edges source base «prefix» cycle with
                  | none =>
                      simp [finish, updated_eq, base_eq, cycle_eq, prefix_eq, make_eq] at returns
                  | some found =>
                      have found_eq : found = witness := by
                        simpa [finish, updated_eq, base_eq, cycle_eq, prefix_eq, make_eq]
                          using returns
                      subst found
                      obtain ⟨_, prefix_field, cycle_field⟩ :=
                        makeWitness_fields edges source base «prefix» cycle witness make_eq
                      have localize_time := localizeCycle_steps_eq_of_ret_some
                        state.predecessor n updated base base_eq
                      have cycle_time := collectCycle_length_eq_of_ret_some
                        state.predecessor base n base [] cycle cycle_eq
                      have prefix_time := collectPrefix_length_eq_of_ret_some
                        state.discoveryPredecessor source (n - 1) base [] «prefix» prefix_eq
                      simp only [List.length_nil, Nat.zero_add] at cycle_time prefix_time
                      simp only [finish, updated_eq, TimeM.time_bind,
                        Cost.add_cycleWitnessSteps, base_eq, cycle_eq, prefix_eq, make_eq,
                        TimeM.time_pure, Cost.zero_cycleWitnessSteps, Nat.add_zero]
                      rw [localize_time, cycle_time, prefix_time, cycle_field, prefix_field]
                      omega

end Internal

open Internal

/-- Bellman-Ford checks every edge occurrence in all ordinary passes and the final pass. -/
public theorem bellmanFord_relaxationChecks {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    (bellmanFord edges source).time.relaxationChecks =
      (n - 1) * edges.length + edges.length := by
  simp only [bellmanFord, Internal.bellmanFord, TimeM.time_bind, Cost.add_relaxationChecks]
  rw [runPasses_relaxationChecks, relaxEdges_relaxationChecks,
    finish_relaxationChecks, Nat.add_zero]

/-- Because a source exists, the exact number of relaxation checks is `n * |edges|`. -/
public theorem bellmanFord_relaxationChecks_eq_mul {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (bellmanFord edges source).time.relaxationChecks = n * edges.length := by
  have n_pos : 0 < n := Nat.zero_lt_of_lt source.isLt
  rw [bellmanFord_relaxationChecks]
  calc
    (n - 1) * edges.length + edges.length = ((n - 1) + 1) * edges.length := by
      simp [Nat.add_mul]
    _ = n * edges.length := by
      congr 1
      omega

/-- Negative-cycle witness reconstruction uses at most three vertex-count passes. -/
public theorem bellmanFord_cycleWitnessSteps_le {n : Nat} (edges : List (Edge n))
    (source : Fin n) :
    (bellmanFord edges source).time.cycleWitnessSteps ≤ 3 * n := by
  simp only [bellmanFord, Internal.bellmanFord, TimeM.time_bind, Cost.add_cycleWitnessSteps]
  rw [runPasses_cycleWitnessSteps, relaxEdges_cycleWitnessSteps]
  simp only [Nat.zero_add]
  exact finish_steps_le_three_mul edges source _

/-- Successful runs perform no negative-cycle reconstruction steps. -/
public theorem bellmanFord_cycleWitnessSteps_eq_zero {n : Nat} (edges : List (Edge n))
    (source : Fin n) (result : Distances n)
    (hRun : (bellmanFord edges source).ret = Result.distances result) :
    (bellmanFord edges source).time.cycleWitnessSteps = 0 := by
  have final_none := afterFinal_none_of_bellmanFord_distances hRun
  simp only [bellmanFord, Internal.bellmanFord, TimeM.time_bind, Cost.add_cycleWitnessSteps]
  rw [runPasses_cycleWitnessSteps, relaxEdges_cycleWitnessSteps]
  simp only [Nat.zero_add]
  change (finish edges source (afterFinal edges source)).time.cycleWitnessSteps = 0
  simp [finish, final_none]

/-- A returned cycle is charged one step per localization, cycle, and prefix edge. -/
public theorem bellmanFord_cycleWitnessSteps_eq {n : Nat} (edges : List (Edge n))
    (source : Fin n) (witness : ReachableNegativeCycle edges source)
    (hRun : (bellmanFord edges source).ret = Result.negativeCycle witness) :
    (bellmanFord edges source).time.cycleWitnessSteps =
      n + witness.cycle.length + witness.prefix.length := by
  have finish_returns :
      (finish edges source
        (relaxEdges edges
          { (runPasses edges (n - 1) (initialState source)).ret with
            lastUpdated := none }).ret).ret = Result.negativeCycle witness := by
    simpa only [bellmanFord, Internal.bellmanFord, TimeM.ret_bind] using hRun
  simp only [bellmanFord, Internal.bellmanFord, TimeM.time_bind, Cost.add_cycleWitnessSteps]
  rw [runPasses_cycleWitnessSteps, relaxEdges_cycleWitnessSteps,
    finish_steps_eq_of_negativeCycle edges source _ witness finish_returns]
  simp

/-- The abstract event count is bounded by `4 * |V| * |E|`. -/
public theorem bellmanFord_total_le {n : Nat} (edges : List (Edge n)) (source : Fin n) :
    (bellmanFord edges source).time.total ≤ 4 * n * edges.length := by
  by_cases edges_nil : edges = []
  · subst edges
    have witness_zero :
        (bellmanFord ([] : List (Edge n)) source).time.cycleWitnessSteps = 0 := by
      simp only [bellmanFord, Internal.bellmanFord, TimeM.time_bind,
        Cost.add_cycleWitnessSteps]
      rw [runPasses_cycleWitnessSteps, relaxEdges_cycleWitnessSteps]
      simp [runPasses_nil_ret, relaxEdges, finish, initialState]
    unfold Cost.total
    rw [bellmanFord_relaxationChecks_eq_mul, witness_zero]
    simp
  · cases edges with
    | nil => contradiction
    | cons head tail =>
        have one_le_edge_count : 1 ≤ (head :: tail).length := by simp
        have vertex_le_product : n ≤ n * (head :: tail).length := by
          simpa using Nat.mul_le_mul_left n one_le_edge_count
        have witness_steps := bellmanFord_cycleWitnessSteps_le (head :: tail) source
        unfold Cost.total
        rw [bellmanFord_relaxationChecks_eq_mul]
        calc
          n * (head :: tail).length +
              (bellmanFord (head :: tail) source).time.cycleWitnessSteps ≤
              n * (head :: tail).length + 3 * n := Nat.add_le_add_left witness_steps _
          _ ≤ n * (head :: tail).length + 3 * (n * (head :: tail).length) := by omega
          _ = 4 * (n * (head :: tail).length) := by omega
          _ = 4 * n * (head :: tail).length := by simp [Nat.mul_assoc]

end Cslib.Algorithms.Lean.BellmanFord
