/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Periodic tasks and fixed-priority preemptive schedules

Discrete-time model of periodic hard-real-time tasks with priority-driven
preemptive scheduling, following Liu and Layland, "Scheduling Algorithms
for Multiprogramming in a Hard-Real-Time Environment" (J. ACM 20(1), 1973).

Representation decisions (modeling choices, not source claims):

- M1 Discrete time. Slot `t : ℕ` is the interval `[t, t + 1)`; periods, run
  times and phases are natural numbers. This is exact for integer data,
  while Liu and Layland use continuous time.
- M2 Run time and period. A task requires exactly `1 ≤ C` and `1 ≤ T` and
  nothing more. In particular `C ≤ T` is not required: a task with `C > T`
  is a legitimate (trivially infeasible) input the model must represent.
- M3 Phases. Task `i` has a release offset `phase ≥ 0`; request `k` of task
  `i` is released at `phase + k * T`.
- M4 Non-periodic tasks (initialization and failure-recovery routines) have
  no hard deadlines and are excluded from the model.
- M5 Equal priorities are broken deterministically by task index: priority
  values live in a linear order where smaller means more urgent, and each
  slot minimizes `(priority, index)` lexicographically. Task indices hence
  carry a `LinearOrder` wherever scheduling is defined.

## Main definitions

`PeriodicTask`, `TaskSet`, `Schedule`, `release`, `deadline`,
`receivedWork`, `IsLive`, `currentRequest`, `RequestOverflow`, `OverflowAt`,
`Feasible`, `firstOverflow`, `responseTime`, `PriorityRule`,
`IsFixedPriority`, `deadlineRule`, `produceSchedule`, `utilization`,
`hyperperiod`.

## Main results

`request_window_unique`, `currentRequest_spec`,
`receivedWork_stable_after_deadline`, `feasible_iff_forall_not_overflowAt`,
`overflowAt_of_agree_before`, `responseTime_of_fulfilled`,
`produceSchedule_spec`, `produceSchedule_idle_iff`, `receivedWork_mono`,
`Feasible.runTime_le_period`, `feasible_produceSchedule_iff_of_unique`.

The last two show that feasibility is neither vacuous nor automatic: a
feasible schedule needs every run-time to be at most its period, and for a
single task the priority-driven schedule is feasible exactly then.

## Implementation notes

`TaskSet`, `Schedule`, `release`, `deadline`, `currentRequest`,
`RequestOverflow`, `OverflowAt` and `PriorityRule`, which the documentation of
`Feasible` and `produceSchedule` states in full, and the helpers behind
`produceSchedule` (`livePairs`, `scheduleStep`, `producePrefix`) carry plain
comments rather than docstrings, so that they get no wiki pages of their own.

## References

* C. L. Liu and J. W. Layland, *Scheduling algorithms for multiprogramming in
  a hard-real-time environment*, J. ACM 20(1), 1973, 46–61: Section 3 (the
  assumptions, scheduling algorithms and priorities) and Section 4
  (deadlines, overflow and feasibility).
-/

@[expose] public section

namespace Cslib.Scheduling.RealTime

open scoped BigOperators

/-- **Periodic tasks.** A periodic task has a run-time `C ≥ 1`, a period `T ≥ 1` and a phase: its
request `k`, for `k = 0, 1, 2, …`, is made at slot `phase + k * T`, and its deadline is the time of
the next request, `phase + (k + 1) * T`. The run-time may exceed the period. -/
structure PeriodicTask where
  /-- Run time: slots of work needed to serve one request. -/
  C : ℕ
  /-- Period: slots between consecutive requests. -/
  T : ℕ
  /-- Release offset: the first request is released at this slot. -/
  phase : ℕ
  /-- Run time is positive. -/
  hC : 1 ≤ C
  /-- Period is positive. -/
  hT : 1 ≤ T

-- A task set: a finite family of tasks indexed by a finite type.
abbrev TaskSet (ι : Type*) [Fintype ι] := ι → PeriodicTask

-- A schedule assigns each slot at most one task, or idles (`none`).
abbrev Schedule (ι : Type*) := ℕ → Option ι

-- Release slot of request `k` of task `i`: `phase + k * T`.
def release {ι : Type*} [Fintype ι] (tasks : TaskSet ι) (i : ι) (k : ℕ) : ℕ :=
  (tasks i).phase + k * (tasks i).T

-- Deadline of request `k` of task `i`: `phase + (k + 1) * T`.
def deadline {ι : Type*} [Fintype ι] (tasks : TaskSet ι) (i : ι) (k : ℕ) : ℕ :=
  (tasks i).phase + (k + 1) * (tasks i).T

/-- **Work received by a request.** `receivedWork tasks sched i k t` is the number of slots `s < t`
from the release of request `k` of task `i` up to its deadline, `release ≤ s < deadline`, in which
the schedule runs task `i`. Slots at or after the deadline do not count, so the work stops growing
once the deadline passes. -/
def receivedWork {ι : Type*} [Fintype ι] [DecidableEq ι] (tasks : TaskSet ι)
    (sched : Schedule ι) (i : ι) (k t : ℕ) : ℕ :=
  ((Finset.Ico (release tasks i k) (min t (deadline tasks i k))).filter
    (fun s => sched s = some i)).card

/-- **Pending requests.** Request `k` of task `i` is live, or pending, at slot `t` under a schedule
if it has been made, `release ≤ t`, its deadline has not passed, `t < deadline`, and it has received
fewer than `C` slots of work before `t`. A request whose deadline passes before it receives `C`
slots of work is thus no longer live. -/
def IsLive {ι : Type*} [Fintype ι] [DecidableEq ι] (tasks : TaskSet ι)
    (sched : Schedule ι) (i : ι) (k t : ℕ) : Prop :=
  release tasks i k ≤ t ∧
    t < deadline tasks i k ∧ receivedWork tasks sched i k t < (tasks i).C

/-- Liveness of a request is decidable. -/
instance decIsLive {ι : Type*} [Fintype ι] [DecidableEq ι] (tasks : TaskSet ι)
    (sched : Schedule ι) (i : ι) (k t : ℕ) :
    Decidable (IsLive tasks sched i k t) := by
  unfold IsLive
  infer_instance

-- Request of task `i` whose window contains slot `t`, if `phase ≤ t`.
def currentRequest {ι : Type*} [Fintype ι] (tasks : TaskSet ι) (i : ι) (t : ℕ) :
    Option ℕ :=
  if t < (tasks i).phase then none
  else some ((t - (tasks i).phase) / (tasks i).T)

theorem request_window_unique {ι : Type*} [Fintype ι] (tasks : TaskSet ι) (i : ι)
    (t k₁ k₂ : ℕ)
    (h₁ : release tasks i k₁ ≤ t ∧ t < deadline tasks i k₁)
    (h₂ : release tasks i k₂ ≤ t ∧ t < deadline tasks i k₂) : k₁ = k₂ := by
  cases lt_trichotomy k₁ k₂ with
  | inl hlt =>
    have hle : k₁ + 1 ≤ k₂ := hlt
    have hmul : (k₁ + 1) * (tasks i).T ≤ k₂ * (tasks i).T :=
      Nat.mul_le_mul_right _ hle
    simp only [release, deadline] at h₁ h₂
    have hfalse : False := by omega
    exact False.elim hfalse
  | inr h =>
    cases h with
    | inl heq => exact heq
    | inr hgt =>
      have hle : k₂ + 1 ≤ k₁ := hgt
      have hmul : (k₂ + 1) * (tasks i).T ≤ k₁ * (tasks i).T :=
        Nat.mul_le_mul_right _ hle
      simp only [release, deadline] at h₁ h₂
      have hfalse : False := by omega
      exact False.elim hfalse

private theorem div_add_one_mul_self_lt (q T : ℕ) (hT : 0 < T) :
    q < (q / T + 1) * T := by
  have hmod := Nat.div_add_mod q T
  have hlt := Nat.mod_lt q hT
  have hrewrite : (q / T + 1) * T = T * (q / T) + T := by
    rw [Nat.add_mul, Nat.one_mul, mul_comm (q / T) T]
  rw [hrewrite]
  omega

theorem currentRequest_spec {ι : Type*} [Fintype ι] (tasks : TaskSet ι) (i : ι) (t k : ℕ)
    (h : (tasks i).phase ≤ t) :
    currentRequest tasks i t = some k ↔
      (release tasks i k ≤ t ∧ t < deadline tasks i k) := by
  have hT : 0 < (tasks i).T := by
    have hh := (tasks i).hT
    omega
  have hif : ¬ t < (tasks i).phase := by omega
  simp only [currentRequest, ite_eq_right hif]
  rw [Option.some_inj]
  constructor
  · intro hdiv
    have hle : k * (tasks i).T ≤ t - (tasks i).phase := by
      have hdm := Nat.div_mul_le_self (t - (tasks i).phase) (tasks i).T
      rw [hdiv] at hdm
      exact hdm
    have hlt : t - (tasks i).phase < (k + 1) * (tasks i).T := by
      have hub := div_add_one_mul_self_lt (t - (tasks i).phase) (tasks i).T hT
      rw [hdiv] at hub
      exact hub
    simp only [release, deadline]
    constructor
    · omega
    · omega
  · intro hwin
    simp only [release, deadline] at hwin
    have hle : k * (tasks i).T ≤ t - (tasks i).phase := by omega
    have hlt : t - (tasks i).phase < (k + 1) * (tasks i).T := by omega
    exact Nat.div_eq_of_lt_le hle hlt

theorem receivedWork_stable_after_deadline {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (sched : Schedule ι) (i : ι) (k t : ℕ)
    (h : deadline tasks i k ≤ t) :
    receivedWork tasks sched i k t =
      receivedWork tasks sched i k (deadline tasks i k) := by
  unfold receivedWork
  have hmin : min t (deadline tasks i k) = deadline tasks i k := by omega
  rw [hmin, min_self]

-- Request `k` of task `i` overflows: unfulfilled at its deadline.
def RequestOverflow {ι : Type*} [Fintype ι] [DecidableEq ι] (tasks : TaskSet ι)
    (sched : Schedule ι) (i : ι) (k : ℕ) : Prop :=
  receivedWork tasks sched i k (deadline tasks i k) < (tasks i).C

/-- Overflow of a request is decidable. -/
instance decRequestOverflow {ι : Type*} [Fintype ι] [DecidableEq ι] (tasks : TaskSet ι)
    (sched : Schedule ι) (i : ι) (k : ℕ) :
    Decidable (RequestOverflow tasks sched i k) := by
  unfold RequestOverflow
  infer_instance

-- An overflow occurs at `t`: `t` is the deadline of an unfulfilled request.
def OverflowAt {ι : Type*} [Fintype ι] [DecidableEq ι] (tasks : TaskSet ι)
    (sched : Schedule ι) (t : ℕ) : Prop :=
  ∃ i k, deadline tasks i k = t ∧ RequestOverflow tasks sched i k

/-- **Feasible schedules in the Liu–Layland periodic task model.** Time is discrete: slot `t` is
the interval `[t, t + 1)`. Each task `i` of a finite task set has a run-time `C ≥ 1`, a period
`T ≥ 1` and a phase; its request `k`, for `k = 0, 1, 2, …`, is made at time `phase + k * T`, and
its deadline is the time of the next request, `phase + (k + 1) * T`. A schedule executes at most
one task in each slot. A request is fulfilled if the schedule executes its task in at least `C` of
the slots from the request up to its deadline, and an overflow occurs at time `t` if `t` is the
deadline of an unfulfilled request. The schedule is feasible if every request is fulfilled, that
is, if no overflow ever occurs (`feasible_iff_forall_not_overflowAt`). -/
def Feasible {ι : Type*} [Fintype ι] [DecidableEq ι] (tasks : TaskSet ι)
    (sched : Schedule ι) : Prop :=
  ∀ i k, ¬ RequestOverflow tasks sched i k

/-- **The first overflow of a schedule.** `firstOverflow tasks sched` is `some t` for the least time
`t` at which an overflow occurs, that is, the least deadline of a request that receives fewer than
`C` slots of work by its deadline, and `none` if no overflow ever occurs. -/
noncomputable def firstOverflow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (sched : Schedule ι) : Option ℕ :=
  haveI : Decidable (∃ t, OverflowAt tasks sched t) :=
    Classical.propDecidable _
  haveI : DecidablePred (OverflowAt tasks sched) :=
    fun t => Classical.propDecidable (OverflowAt tasks sched t)
  if h : ∃ t, OverflowAt tasks sched t then some (Nat.find h) else none

theorem feasible_iff_forall_not_overflowAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (sched : Schedule ι) :
    Feasible tasks sched ↔ ∀ t, ¬ OverflowAt tasks sched t := by
  constructor
  · rintro h t ⟨i, k, -, hro⟩
    exact h i k hro
  · intro h i k hro
    exact h _ ⟨i, k, rfl, hro⟩

theorem firstOverflow_eq_some_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (sched : Schedule ι) (t : ℕ) :
    firstOverflow tasks sched = some t ↔
      (OverflowAt tasks sched t ∧ ∀ s, s < t → ¬ OverflowAt tasks sched s) := by
  classical
  unfold firstOverflow
  by_cases hex : ∃ t, OverflowAt tasks sched t
  · rw [dite_eq_left hex]
    constructor
    · intro hsome
      have hfind : Nat.find hex = t := Option.some_inj.mp hsome
      constructor
      · rw [← hfind]
        exact Nat.find_spec hex
      · intro s hs hPs
        have hle := Nat.find_min' hex hPs
        omega
    · intro hpair
      obtain ⟨hPt, hmin⟩ := hpair
      have hfind : Nat.find hex = t := by
        apply le_antisymm
        · exact Nat.find_min' hex hPt
        · by_contra hcon
          have hlt : Nat.find hex < t := lt_of_not_ge hcon
          have hspec := Nat.find_spec hex
          exact hmin _ hlt hspec
      rw [hfind]
  · rw [dite_eq_right hex]
    constructor
    · intro hnone
      simp at hnone
    · intro hpair
      obtain ⟨hPt, _⟩ := hpair
      exact absurd ⟨t, hPt⟩ hex

theorem firstOverflow_eq_none_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (sched : Schedule ι) :
    firstOverflow tasks sched = none ↔ Feasible tasks sched := by
  classical
  unfold firstOverflow
  by_cases hex : ∃ t, OverflowAt tasks sched t
  · rw [dite_eq_left hex]
    constructor
    · intro hsome
      simp at hsome
    · intro hfeas
      obtain ⟨t, hov⟩ := hex
      obtain ⟨i, k, _, hro⟩ := hov
      exact absurd hro (hfeas i k)
  · rw [dite_eq_right hex]
    constructor
    · intro _ i k hro
      exact hex ⟨deadline tasks i k, i, k, rfl, hro⟩
    · intro _
      rfl

private theorem receivedWork_of_agree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (s1 s2 : Schedule ι) (i : ι) (k t' : ℕ)
    (hag : ∀ s, s < t' → s1 s = s2 s) :
    receivedWork tasks s1 i k t' = receivedWork tasks s2 i k t' := by
  unfold receivedWork
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro s hs
  simp only [Finset.mem_Ico] at hs
  have hslt : s < t' := by omega
  rw [hag s hslt]

theorem overflowAt_of_agree_before {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (s1 s2 : Schedule ι) (t : ℕ)
    (h : ∀ s, s < t → s1 s = s2 s) :
    OverflowAt tasks s1 t ↔ OverflowAt tasks s2 t := by
  constructor
  · intro hov
    obtain ⟨i, k, heq, hro⟩ := hov
    refine ⟨i, k, heq, ?_⟩
    unfold RequestOverflow at hro ⊢
    have hag : ∀ s, s < deadline tasks i k → s1 s = s2 s := by
      intro s hs
      apply h
      omega
    have heq2 :=
      receivedWork_of_agree tasks s1 s2 i k (deadline tasks i k) hag
    omega
  · intro hov
    obtain ⟨i, k, heq, hro⟩ := hov
    refine ⟨i, k, heq, ?_⟩
    unfold RequestOverflow at hro ⊢
    have hag : ∀ s, s < deadline tasks i k → s2 s = s1 s := by
      intro s hs
      have hslt : s < t := by omega
      exact (h s hslt).symm
    have heq2 :=
      receivedWork_of_agree tasks s2 s1 i k (deadline tasks i k) hag
    omega

/-- **Response time of a request.** The response time of request `k` of task `i` under a schedule is
`t` minus the time of the request, where `t` is the first time by which the request has received
`C` slots of work, the end of the slot in which it receives the last of them. Slots at or after the
deadline of the request do not count, so a request that receives fewer than `C` slots of work by its
deadline has no response time. -/
noncomputable def responseTime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (sched : Schedule ι) (i : ι) (k : ℕ) : Option ℕ :=
  haveI : Decidable (∃ t, (tasks i).C ≤ receivedWork tasks sched i k t) :=
    Classical.propDecidable _
  if h : ∃ t, (tasks i).C ≤ receivedWork tasks sched i k t then
    some (Nat.find h - release tasks i k)
  else none

theorem responseTime_of_fulfilled {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (sched : Schedule ι) (i : ι) (k : ℕ) (t : ℕ)
    (hle : ∀ t', t' < t → receivedWork tasks sched i k t' < (tasks i).C)
    (hge : (tasks i).C ≤ receivedWork tasks sched i k t) :
    responseTime tasks sched i k = some (t - release tasks i k) := by
  classical
  have hex : ∃ t, (tasks i).C ≤ receivedWork tasks sched i k t := ⟨t, hge⟩
  unfold responseTime
  rw [dite_eq_left hex]
  have hfind : Nat.find hex = t := by
    apply le_antisymm
    · exact Nat.find_min' hex hge
    · by_contra hcon
      have hlt : Nat.find hex < t := lt_of_not_ge hcon
      have h1 := hle _ hlt
      have h2 := Nat.find_spec hex
      omega
  rw [hfind]

-- A priority rule maps (task index, request number) into a linear order.
abbrev PriorityRule (ι : Type*) (π : Type*) [LinearOrder π] := ι → ℕ → π

/-- **Fixed-priority rules.** A priority rule, which gives each request `k` of each task `i` a
priority `rule i k`, is fixed, or static, if all requests of each task have the same priority:
priorities are assigned to tasks once and for all. -/
def IsFixedPriority (ι π : Type*) [LinearOrder π]
    (rule : PriorityRule ι π) : Prop :=
  ∀ i k₁ k₂, rule i k₁ = rule i k₂

/-- **The deadline-driven priority rule.** The deadline-driven rule gives each request its deadline
as priority, so that, a smaller value being a higher priority, a request with an earlier deadline
has a higher priority. It is dynamic: the priorities of a task change from request to request. -/
def deadlineRule {ι : Type*} [Fintype ι] (tasks : TaskSet ι) : PriorityRule ι ℕ :=
  fun i k => deadline tasks i k

-- Live `(task, request)` pairs at slot `t` under a prefix schedule.
def livePairs {ι : Type*} [Fintype ι] [DecidableEq ι] (tasks : TaskSet ι)
    (pre : Schedule ι) (t : ℕ) : Finset (ι × ℕ) :=
  Finset.univ.biUnion (fun i => match currentRequest tasks i t with
    | none => ∅
    | some k => if IsLive tasks pre i k t then {(i, k)} else ∅)

-- Slot choice: least priority wins, ties broken by least task index.
def scheduleStep {ι : Type*} {π : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder π]
    (tasks : TaskSet ι) (rule : PriorityRule ι π) (pre : Schedule ι)
    (t : ℕ) : Option ι :=
  let pairs := livePairs tasks pre t
  match (pairs.image (fun p : ι × ℕ => rule p.1 p.2)).min with
  | none => none
  | some pmin =>
    match ((pairs.filter (fun p => rule p.1 p.2 = pmin)).image Prod.fst).min with
    | none => none
    | some i => some i

-- Prefix schedules: slots below `n` follow the priority rule.
def producePrefix {ι : Type*} {π : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder π]
    (tasks : TaskSet ι) (rule : PriorityRule ι π) : ℕ → Schedule ι
  | 0 => fun _ => none
  | n + 1 => let pre := producePrefix tasks rule n;
    Function.update pre n (scheduleStep tasks rule pre n)

/-- **Preemptive priority-driven schedules.** A priority rule gives each request `k` of each task
`i` a priority `rule i k` in a linearly ordered type, a smaller value being a higher priority. The
priority-driven schedule of the rule runs in each slot `t` the task of the live request of highest
priority, ties between equal priorities being broken by the least task index, and leaves slot `t`
idle only when no request is live at `t`. A request is live at `t` if it has been made, its
deadline has not passed and it has received fewer than `C` slots of work before `t`, so a request
whose deadline passes before it receives `C` slots is dropped. As the choice is made afresh in
every slot, a new request that outranks every live request preempts the running task at once,
while one that another live request outranks waits, even if it outranks the running task. This is
a preemptive, priority-driven scheduling algorithm in the sense of Liu and Layland, and it is
feasible for a task set if this schedule is feasible. -/
def produceSchedule {ι : Type*} {π : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder π]
    (tasks : TaskSet ι) (rule : PriorityRule ι π) : Schedule ι :=
  fun t => producePrefix tasks rule (t + 1) t

private theorem producePrefix_mono {ι : Type*} {π : Type*} [Fintype ι] [LinearOrder ι]
    [LinearOrder π] (tasks : TaskSet ι) (rule : PriorityRule ι π)
    (m n : ℕ) (hnm : n ≤ m) (s : ℕ) (hs : s < n) :
    producePrefix tasks rule n s = producePrefix tasks rule m s := by
  induction m generalizing n s with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    exact absurd hs (Nat.not_lt_zero s)
  | succ m ih =>
    by_cases heq : n = m + 1
    · subst heq
      rfl
    · have hnm' : n ≤ m := by omega
      have ih' := ih n hnm' s hs
      have hne : s ≠ m := by omega
      simp only [producePrefix]
      rw [Function.update_of_ne hne]
      exact ih'

private theorem producePrefix_agree {ι : Type*} {π : Type*} [Fintype ι] [LinearOrder ι]
    [LinearOrder π] (tasks : TaskSet ι) (rule : PriorityRule ι π)
    (t s : ℕ) (hs : s < t) :
    produceSchedule tasks rule s = producePrefix tasks rule t s := by
  simp only [produceSchedule]
  have hle : s + 1 ≤ t := by omega
  have hlt : s < s + 1 := by omega
  exact producePrefix_mono tasks rule t (s + 1) hle s hlt

private theorem produceSchedule_step {ι : Type*} {π : Type*} [Fintype ι] [LinearOrder ι]
    [LinearOrder π] (tasks : TaskSet ι) (rule : PriorityRule ι π) (t : ℕ) :
    produceSchedule tasks rule t =
      scheduleStep tasks rule (producePrefix tasks rule t) t := by
  simp only [produceSchedule, producePrefix]
  exact Function.update_self _ _ _

private theorem isLive_of_agree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (s1 s2 : Schedule ι) (t : ℕ)
    (hag : ∀ s, s < t → s1 s = s2 s) (i : ι) (k : ℕ) :
    IsLive tasks s1 i k t ↔ IsLive tasks s2 i k t := by
  unfold IsLive
  rw [receivedWork_of_agree tasks s1 s2 i k t hag]

private theorem currentRequest_of_isLive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (sched : Schedule ι) (i : ι) (k t : ℕ)
    (hlive : IsLive tasks sched i k t) :
    currentRequest tasks i t = some k := by
  unfold IsLive at hlive
  obtain ⟨hle, hlt, _⟩ := hlive
  have hleu : (tasks i).phase + k * (tasks i).T ≤ t := hle
  have hphase : (tasks i).phase ≤ t := by omega
  exact (currentRequest_spec tasks i t k hphase).mpr ⟨hle, hlt⟩

private theorem mem_livePairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (pre : Schedule ι) (t : ℕ) (j : ι) (l : ℕ) :
    (j, l) ∈ livePairs tasks pre t ↔
      (currentRequest tasks j t = some l ∧ IsLive tasks pre j l t) := by
  simp only [livePairs, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro hex
    obtain ⟨i, hi⟩ := hex
    revert hi
    cases hcr : currentRequest tasks i t with
    | none =>
      intro hi
      have hi' : (j, l) ∈ (∅ : Finset (ι × ℕ)) := hi
      exact absurd hi' (Finset.notMem_empty _)
    | some k =>
      intro hi
      have hi' : (j, l) ∈ (if IsLive tasks pre i k t then ({(i, k)} :
        Finset (ι × ℕ)) else ∅) := hi
      by_cases hlive : IsLive tasks pre i k t
      · rw [ite_eq_left hlive] at hi'
        simp only [Finset.mem_singleton, Prod.mk.injEq] at hi'
        obtain ⟨rfl, rfl⟩ := hi'
        exact ⟨hcr, hlive⟩
      · rw [ite_eq_right hlive] at hi'
        exact absurd hi' (Finset.notMem_empty _)
  · intro hpair
    obtain ⟨hcr, hlive⟩ := hpair
    refine ⟨j, ?_⟩
    rw [hcr]
    show (j, l) ∈ (if IsLive tasks pre j l t then ({(j, l)} :
      Finset (ι × ℕ)) else ∅)
    rw [ite_eq_left hlive]
    simp only [Finset.mem_singleton]

theorem produceSchedule_spec {ι : Type*} {π : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder π]
    (tasks : TaskSet ι) (rule : PriorityRule ι π) (t : ℕ) :
    (produceSchedule tasks rule t = none →
        ¬ ∃ i k, IsLive tasks (produceSchedule tasks rule) i k t) ∧
      (∀ i, produceSchedule tasks rule t = some i →
        ∃ k, IsLive tasks (produceSchedule tasks rule) i k t ∧
          currentRequest tasks i t = some k ∧
          ∀ j l, IsLive tasks (produceSchedule tasks rule) j l t →
            rule i k < rule j l ∨ (rule i k = rule j l ∧ i ≤ j)) := by
  have hstep := produceSchedule_step tasks rule t
  have hag : ∀ s, s < t → produceSchedule tasks rule s =
      producePrefix tasks rule t s :=
    fun s hs => producePrefix_agree tasks rule t s hs
  have hUp : ∀ i k, IsLive tasks (produceSchedule tasks rule) i k t ↔
      IsLive tasks (producePrefix tasks rule t) i k t :=
    fun i k => isLive_of_agree tasks (produceSchedule tasks rule)
      (producePrefix tasks rule t) t hag i k
  have hmem : ∀ j l, (j, l) ∈ livePairs tasks (producePrefix tasks rule t) t ↔
      (currentRequest tasks j t = some l ∧
        IsLive tasks (produceSchedule tasks rule) j l t) := by
    intro j l
    rw [mem_livePairs tasks (producePrefix tasks rule t) t j l]
    constructor
    · intro hpair
      obtain ⟨hcr, hlive⟩ := hpair
      exact ⟨hcr, (hUp j l).mpr hlive⟩
    · intro hpair
      obtain ⟨hcr, hlive⟩ := hpair
      exact ⟨hcr, (hUp j l).mp hlive⟩
  constructor
  · intro hnone
    rw [hstep] at hnone
    simp only [scheduleStep] at hnone
    split at hnone
    · rename_i hmin1
      intro hex
      obtain ⟨j, l, hlive⟩ := hex
      have hcr :=
        currentRequest_of_isLive tasks (produceSchedule tasks rule) j l t
          hlive
      have hmemjl := (hmem j l).mpr ⟨hcr, hlive⟩
      have hempty1 : (livePairs tasks (producePrefix tasks rule t) t).image
          (fun p : ι × ℕ => rule p.1 p.2) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        obtain ⟨b, hb⟩ := Finset.min_of_mem hx
        rw [hmin1] at hb
        exact WithTop.top_ne_coe hb
      have hempty : livePairs tasks (producePrefix tasks rule t) t = ∅ :=
        Finset.image_eq_empty.mp hempty1
      rw [hempty] at hmemjl
      exact absurd hmemjl (Finset.notMem_empty _)
    · rename_i pmin hmin1
      split at hnone
      · rename_i hmin2
        have hpmin_mem := Finset.mem_of_min hmin1
        obtain ⟨p, hpmem, hpeq⟩ := Finset.mem_image.mp hpmin_mem
        have hpeq' : rule p.1 p.2 = pmin := hpeq
        have hfilt_mem : p ∈ (livePairs tasks
            (producePrefix tasks rule t) t).filter
            (fun p => rule p.1 p.2 = pmin) :=
          Finset.mem_filter.mpr ⟨hpmem, hpeq'⟩
        have himg2_ne : (((livePairs tasks
            (producePrefix tasks rule t) t).filter
            (fun p => rule p.1 p.2 = pmin)).image Prod.fst).Nonempty :=
          Finset.image_nonempty.mpr ⟨p, hfilt_mem⟩
        obtain ⟨b, hb⟩ := Finset.min_of_nonempty himg2_ne
        rw [hmin2] at hb
        exact absurd hb WithTop.top_ne_coe
      · rename_i i' hmin2
        simp at hnone
  · intro i hi
    rw [hstep] at hi
    simp only [scheduleStep] at hi
    split at hi
    · rename_i hmin1
      simp at hi
    · rename_i pmin hmin1
      split at hi
      · rename_i hmin2
        simp at hi
      · rename_i i' hmin2
        have heq : i' = i := Option.some_inj.mp hi
        have heq' : i = i' := heq.symm
        subst heq'
        obtain ⟨q, hqmem, hqeq⟩ :=
          Finset.mem_image.mp (Finset.mem_of_min hmin2)
        obtain ⟨j', l'⟩ := q
        simp only [Finset.mem_filter] at hqmem
        obtain ⟨hqmem', hrule⟩ := hqmem
        have hji : j' = i := hqeq
        have hji' : i = j' := hji.symm
        subst hji'
        have hmem_i := (hmem i l').mp hqmem'
        obtain ⟨hcr_i, hlive_i⟩ := hmem_i
        refine ⟨l', hlive_i, hcr_i, ?_⟩
        intro j l hlive
        have hcr_j :=
          currentRequest_of_isLive tasks (produceSchedule tasks rule) j l t
            hlive
        have hmem_jl := (hmem j l).mpr ⟨hcr_j, hlive⟩
        have himg1_j : rule j l ∈ (livePairs tasks
            (producePrefix tasks rule t) t).image
            (fun p : ι × ℕ => rule p.1 p.2) :=
          Finset.mem_image.mpr ⟨(j, l), hmem_jl, rfl⟩
        have hle1 : pmin ≤ rule j l := Finset.min_le_of_eq himg1_j hmin1
        cases lt_trichotomy (rule i l') (rule j l) with
        | inl hlt => exact Or.inl hlt
        | inr h =>
          cases h with
          | inl heq =>
            have hrulej : rule j l = pmin := heq.symm.trans hrule
            have hfilt_j : (j, l) ∈ (livePairs tasks
                (producePrefix tasks rule t) t).filter
                (fun p => rule p.1 p.2 = pmin) :=
              Finset.mem_filter.mpr ⟨hmem_jl, hrulej⟩
            have himg2_j : j ∈ (((livePairs tasks
                (producePrefix tasks rule t) t).filter
                (fun p => rule p.1 p.2 = pmin)).image Prod.fst) :=
              Finset.mem_image.mpr ⟨(j, l), hfilt_j, rfl⟩
            have hle2 : i ≤ j := Finset.min_le_of_eq himg2_j hmin2
            exact Or.inr ⟨heq, hle2⟩
          | inr hgt =>
            have h2 : rule j l < pmin := by
              have hgt' := hgt
              rw [hrule] at hgt'
              exact hgt'
            have hlt : pmin < pmin := lt_of_le_of_lt hle1 h2
            exact absurd hlt (lt_irrefl pmin)

/-- **Processor utilization of a task set.** The utilization factor of a task set is the rational
number `U = ∑ᵢ Cᵢ / Tᵢ`, the sum over its tasks of run-time divided by period. -/
def utilization {ι : Type*} [Fintype ι] (tasks : TaskSet ι) : ℚ :=
  ∑ i, ((tasks i).C : ℚ) / ((tasks i).T : ℚ)

/-- **Hyperperiod of a task set.** The hyperperiod of a task set is the least common multiple of
the periods of its tasks, `1` for the empty task set. -/
def hyperperiod {ι : Type*} [Fintype ι] (tasks : TaskSet ι) : ℕ :=
  Finset.univ.lcm (fun i => (tasks i).T)

theorem produceSchedule_idle_iff {ι : Type*} {π : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder π]
    (tasks : TaskSet ι) (rule : PriorityRule ι π) (t : ℕ) :
    produceSchedule tasks rule t = none ↔
      ¬ ∃ i k, IsLive tasks (produceSchedule tasks rule) i k t := by
  constructor
  · exact (produceSchedule_spec tasks rule t).1
  · intro hnone
    cases hSi : produceSchedule tasks rule t with
    | none => rfl
    | some i =>
      obtain ⟨k, hlive, _, _⟩ := (produceSchedule_spec tasks rule t).2 i hSi
      exact absurd ⟨i, k, hlive⟩ hnone

theorem receivedWork_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (tasks : TaskSet ι)
    (sched : Schedule ι) (i : ι) (k t₁ t₂ : ℕ) (h : t₁ ≤ t₂) :
    receivedWork tasks sched i k t₁ ≤ receivedWork tasks sched i k t₂ := by
  unfold receivedWork
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  apply Finset.Ico_subset_Ico_right
  omega

private theorem deadline_sub_release {ι : Type*} [Fintype ι] (tasks : TaskSet ι) (i : ι)
    (k : ℕ) : deadline tasks i k - release tasks i k = (tasks i).T := by
  simp only [release, deadline, Nat.succ_mul]
  omega

private theorem receivedWork_le_period {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (sched : Schedule ι) (i : ι) (k t : ℕ) :
    receivedWork tasks sched i k t ≤ (tasks i).T := by
  unfold receivedWork
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Nat.card_Ico]
  have h := deadline_sub_release tasks i k
  omega

/-- **Feasibility needs every run-time to be at most its period.** If a schedule of a periodic
task set is feasible, then every task's run-time `C` is at most its period `T`. -/
theorem Feasible.runTime_le_period {ι : Type*} [Fintype ι] [DecidableEq ι] {tasks : TaskSet ι}
    {sched : Schedule ι} (h : Feasible tasks sched) (i : ι) : (tasks i).C ≤ (tasks i).T := by
  by_contra hlt
  exact h i 0 ((receivedWork_le_period tasks sched i 0 _).trans_lt (not_le.mp hlt))

/-- **Feasibility of a single periodic task.** For a task set with exactly one task, of run-time
`C` and period `T`, the priority-driven schedule of any priority rule is feasible exactly when
`C ≤ T`. -/
theorem feasible_produceSchedule_iff_of_unique {ι : Type*} {π : Type*} [Fintype ι]
    [LinearOrder ι] [Unique ι] [LinearOrder π] (tasks : TaskSet ι) (rule : PriorityRule ι π) :
    Feasible tasks (produceSchedule tasks rule) ↔ (tasks default).C ≤ (tasks default).T := by
  refine ⟨fun h => h.runTime_le_period default, fun hCT i k hro => ?_⟩
  obtain rfl : i = default := Unique.eq_default i
  -- An overflowing request is live, so scheduled, in every slot of its window.
  have hrun : ∀ s ∈ Finset.Ico (release tasks default k) (deadline tasks default k),
      produceSchedule tasks rule s = some default := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hlive : IsLive tasks (produceSchedule tasks rule) default k s :=
      ⟨hs.1, hs.2, (receivedWork_mono tasks _ default k s _ hs.2.le).trans_lt hro⟩
    cases hS : produceSchedule tasks rule s with
    | none => exact absurd ⟨default, k, hlive⟩ ((produceSchedule_idle_iff tasks rule s).mp hS)
    | some j => rw [Unique.eq_default j]
  unfold RequestOverflow receivedWork at hro
  rw [min_self, Finset.filter_true_of_mem hrun, Nat.card_Ico, deadline_sub_release] at hro
  omega

end Cslib.Scheduling.RealTime
