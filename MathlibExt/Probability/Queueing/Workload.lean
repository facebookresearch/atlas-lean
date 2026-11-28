/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Deterministic workload of a single-server queue

Workload is the total remaining service, not the number of customers. A unit-rate server
removes one unit of work per unit of time while there is work; each arrival adds its service
requirement. The local balance laws below are hypotheses about traces, not a derivation from
a model of scheduling. In particular they do not distinguish nonpreemptive service from
preemptive-resume service.

See I. Adan and J. Resing, [*Queueing Systems*](https://www.win.tue.nl/~iadan/queueing.pdf),
§9.4 for the workload observation and §9.2 for the comparison with preemptive-resume priority.
-/

open Filter

namespace MetaMathlibExt.Queueing

@[expose] public section

/-- The local workload laws of a work-conserving single server at unit rate. The initial
backlog is measured at time zero before any arrivals at zero. `postwork n` includes the demand
at index `n` but not any later indexed demands, even those at the same time. The real-time
observation `workload` is specified only at nonnegative times. In particular, at a time
with tied arrivals it observes the workload after the entire batch: earlier ties have empty
half-open gaps. -/
structure IsWorkConservingTrace (arrival demand : ℕ → ℝ) (initial : ℝ)
    (postwork : ℕ → ℝ) (workload : ℝ → ℝ) : Prop where
  arrival_mono : Monotone arrival
  arrival_zero_nonneg : 0 ≤ arrival 0
  arrival_tendsto : Tendsto arrival atTop atTop
  initial_nonneg : 0 ≤ initial
  demand_nonneg : ∀ n, 0 ≤ demand n
  postwork_zero : postwork 0 = max 0 (initial - arrival 0) + demand 0
  postwork_succ : ∀ n, postwork (n + 1) =
    max 0 (postwork n - (arrival (n + 1) - arrival n)) + demand (n + 1)
  workload_before_first : ∀ t, 0 ≤ t → t < arrival 0 → workload t = max 0 (initial - t)
  workload_on_gap : ∀ n t, arrival n ≤ t → t < arrival (n + 1) →
    workload t = max 0 (postwork n - (t - arrival n))

variable {arrival demand : ℕ → ℝ} {initial : ℝ}
  {postwork₁ postwork₂ : ℕ → ℝ} {workload₁ workload₂ : ℝ → ℝ}

/-- With the same arrival times, demands and initial backlog, the workloads immediately after
processing each indexed arrival agree, including intermediate values at simultaneous arrivals. -/
lemma workloadAtArrival_eq_of_same_arrivals
    (h₁ : IsWorkConservingTrace arrival demand initial postwork₁ workload₁)
    (h₂ : IsWorkConservingTrace arrival demand initial postwork₂ workload₂) :
    postwork₁ = postwork₂ := by
  funext n
  induction n with
  | zero => rw [h₁.postwork_zero, h₂.postwork_zero]
  | succ n ih => rw [h₁.postwork_succ, h₂.postwork_succ, ih]

/-- The real-time workloads of two work-conserving unit-rate traces with the same arrival times,
service demands and initial backlog agree at every `t ≥ 0`. At an arrival time, this is the
workload after all arrivals at that time. -/
lemma workload_eq_of_same_arrivals
    (h₁ : IsWorkConservingTrace arrival demand initial postwork₁ workload₁)
    (h₂ : IsWorkConservingTrace arrival demand initial postwork₂ workload₂) :
    Set.EqOn workload₁ workload₂ (Set.Ici 0) := by
  intro t ht
  obtain ⟨i, hi⟩ := tendsto_atTop_atTop.mp h₁.arrival_tendsto (t + 1)
  have hex : ∃ n, t < arrival n := ⟨i, (lt_add_of_pos_right t zero_lt_one).trans_le (hi i le_rfl)⟩
  have hnext := Nat.find_spec hex
  -- The first index strictly after `t` gives either the initial gap or the gap after the last tie.
  cases hj : Nat.find hex with
  | zero =>
    rw [hj] at hnext
    rw [h₁.workload_before_first t ht hnext, h₂.workload_before_first t ht hnext]
  | succ n =>
    rw [hj] at hnext
    have hn : n < Nat.find hex := by simpa only [hj] using Nat.lt_succ_self n
    have hprev : arrival n ≤ t := le_of_not_gt (Nat.find_min hex hn)
    rw [h₁.workload_on_gap n t hprev hnext, h₂.workload_on_gap n t hprev hnext,
      workloadAtArrival_eq_of_same_arrivals h₁ h₂]

/-- The busy times (nonnegative times with strictly positive workload) are the same for two
work-conserving unit-rate traces with the same arrival times, demands and initial backlog. -/
lemma busySet_eq_of_same_arrivals
    (h₁ : IsWorkConservingTrace arrival demand initial postwork₁ workload₁)
    (h₂ : IsWorkConservingTrace arrival demand initial postwork₂ workload₂) :
    {t : ℝ | 0 ≤ t ∧ 0 < workload₁ t} = {t : ℝ | 0 ≤ t ∧ 0 < workload₂ t} := by
  ext t
  change (0 ≤ t ∧ 0 < workload₁ t) ↔ (0 ≤ t ∧ 0 < workload₂ t)
  exact and_congr_right fun ht => by rw [workload_eq_of_same_arrivals h₁ h₂ ht]

end

end MetaMathlibExt.Queueing
