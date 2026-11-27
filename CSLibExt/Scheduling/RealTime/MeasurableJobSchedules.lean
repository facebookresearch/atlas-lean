/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone

/-!
# Measurable preemptive schedules on one processor

A finite family of independent jobs shares a single processor. An assignment at an instant is
one job or idle; jobs may be interrupted and resumed at no cost. Time and job parameters are
nonnegative reals. To measure execution with ordinary Lebesgue measure on the line, we represent
an assignment by its extension to the whole line, necessarily idle at every negative time.

Service through `t` counts only times strictly below `t`. It is not capped at the requirement
or the deadline. Completion is its first exact hit at or after release, not a time supplied by
the schedule. A job need not complete. Feasibility of an assignment requires every job to
complete by its own deadline; feasibility of the job family requires such an assignment to exist.

J. Goossens, S. Funk and S. Baruah, *Priority-driven scheduling of periodic task systems on
multiprocessors*, technical report TR01-024, §2.1, p. 4, give the job triple and its half-open
execution window. M. Sojka, *Deadline-driven scheduling* (22 November 2023), slide 7, describes
the independent, preemptible one-processor setting. The measure and first-hit conventions here
do not impose a priority policy.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace Cslib.Scheduling.RealTime

/-- An independent job needs `work` units of processor time in the half-open interval from its
nonnegative release to its absolute deadline. Zero work and a deadline at release are allowed. -/
structure Job where
  /-- First time at which the job may run. -/
  release : ℝ≥0
  /-- Required amount of processor time, possibly zero. -/
  work : ℝ≥0
  /-- Absolute time by which the required work is due. -/
  deadline : ℝ≥0
  /-- The execution window ends no earlier than release. -/
  release_le_deadline : release ≤ deadline

/-- A Lebesgue-measurable assignment of one processor to a family of `n` independent jobs or to
idle. It never runs a job before release, even at a single instant. The assignment is extended
by idle to negative times; neither meeting deadlines nor stopping after completion is required. -/
structure JobSchedule {n : ℕ} (jobs : Fin n → Job) where
  /-- The running job at each real time, or `none` when idle. -/
  assign : ℝ → Option (Fin n)
  /-- The assignment is Lebesgue measurable, with the discrete measurable space on outcomes. -/
  measurable_assign : @NullMeasurable ℝ (Option (Fin n)) _ ⊤ assign volume
  /-- Every instant assigned to a job is at or after its release. -/
  released : ∀ {t j}, assign t = some j → (jobs j).release ≤ t

namespace JobSchedule

variable {n : ℕ} {jobs : Fin n → Job} (σ : JobSchedule jobs) (j : Fin n)

/-- Accumulated service of job `j` through nonnegative time `t`: the Lebesgue measure of its
execution times in `[0,t)`, without capping the result at the required work. -/
noncomputable def service (t : ℝ≥0) : ℝ :=
  volume.real (Ico 0 (t : ℝ) ∩ σ.assign ⁻¹' {some j})

private theorem window_finite (a b : ℝ) :
    volume (Ico a b ∩ σ.assign ⁻¹' {some j}) ≠ ⊤ :=
  measure_ne_top_of_subset inter_subset_left (by simp)

/-- A job's accumulated service never decreases with time. -/
theorem service_mono : Monotone (σ.service j) := by
  intro s t hst
  apply measureReal_mono _ (σ.window_finite j 0 t)
  exact inter_subset_inter_left _ (Ico_subset_Ico_right hst)

/-- Between two ordered times the increase in service cannot exceed the elapsed time. -/
theorem service_sub_le {s t : ℝ≥0} (hst : s ≤ t) :
    σ.service j t - σ.service j s ≤ (t : ℝ) - s := by
  let A := Ico 0 (s : ℝ) ∩ σ.assign ⁻¹' {some j}
  let B := Ico (s : ℝ) (t : ℝ)
  have hsub : Ico 0 (t : ℝ) ∩ σ.assign ⁻¹' {some j} ⊆ A ∪ B := by
    rintro x ⟨⟨hx, hxt⟩, hj⟩
    by_cases hxs : x < s
    · exact Or.inl ⟨⟨hx, hxs⟩, hj⟩
    · exact Or.inr ⟨le_of_not_gt hxs, hxt⟩
  have hfin : volume (A ∪ B) ≠ ⊤ :=
    (measure_union_lt_top (σ.window_finite j 0 s).lt_top (by simp [B])).ne
  have h := (measureReal_mono hsub hfin).trans (measureReal_union_le A B)
  rw [show volume.real B = (t : ℝ) - s from Real.volume_real_Ico_of_le hst] at h
  exact sub_le_iff_le_add'.2 h

/-- The service of each job is 1-Lipschitz in real time. -/
theorem lipschitzWith_service : LipschitzWith 1 (σ.service j) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [NNReal.coe_one, one_mul]
  wlog hst : s ≤ t generalizing s t
  · simpa only [dist_comm] using this t s (le_of_not_ge hst)
  change |σ.service j s - σ.service j t| ≤ |(s : ℝ) - t|
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (σ.service_mono j hst)),
    abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))]
  exact σ.service_sub_le j hst

/-- Accumulated service is continuous, including at release and at interruption times. -/
theorem continuous_service : Continuous (σ.service j) := (σ.lipschitzWith_service j).continuous

/-- No service has accumulated at the instant a job is released. -/
@[simp] theorem service_release : σ.service j (jobs j).release = 0 := by
  have he : Ico 0 ((jobs j).release : ℝ) ∩ σ.assign ⁻¹' {some j} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro t ⟨⟨_, ht⟩, hj⟩
    exact ht.not_ge (σ.released hj)
  simp [service, he]

/-- The least time at or after release when service equals the job's required work. The value
is `none` if there is no such time, even if service approaches the requirement from below. -/
noncomputable def completion : Option ℝ≥0 := by
  classical
  let hits := {t : ℝ≥0 | (jobs j).release ≤ t ∧ σ.service j t = (jobs j).work}
  exact if hits.Nonempty then some (sInf hits) else none

/-- Completion returns `c` exactly when `c` is the least time at or after the job's release at
which its accumulated service equals its required work. -/
theorem completion_eq_some_iff {c : ℝ≥0} : σ.completion j = some c ↔
    IsLeast {t | (jobs j).release ≤ t ∧ σ.service j t = (jobs j).work} c := by
  classical
  let hits := {t : ℝ≥0 | (jobs j).release ≤ t ∧ σ.service j t = (jobs j).work}
  have hc : IsClosed hits :=
    isClosed_Ici.inter (isClosed_eq (σ.continuous_service j) continuous_const)
  change (if hits.Nonempty then some (sInf hits) else none) = some c ↔ IsLeast hits c
  split
  · rename_i h
    have hl := hc.isLeast_csInf h (OrderBot.bddBelow hits)
    rw [Option.some.injEq]
    exact ⟨fun he ↦ he ▸ hl, fun hm ↦ hl.unique hm⟩
  · rename_i h
    exact ⟨(fun he ↦ nomatch he), fun hl ↦ (h ⟨_, hl.1⟩).elim⟩

/-- Completion is absent exactly when the required work is never attained at or after release. -/
theorem completion_eq_none_iff : σ.completion j = none ↔
    ¬ ∃ t, (jobs j).release ≤ t ∧ σ.service j t = (jobs j).work := by
  classical
  let hits := {t : ℝ≥0 | (jobs j).release ≤ t ∧ σ.service j t = (jobs j).work}
  change (if hits.Nonempty then some (sInf hits) else none) = none ↔ ¬ hits.Nonempty
  by_cases h : hits.Nonempty
  · rw [ite_eq_left h]
    exact ⟨(fun he ↦ nomatch he), fun hn ↦ (hn h).elim⟩
  · rw [ite_eq_right h]
    exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩

/-- A job with no required work completes at release, even if the processor is idle. -/
theorem completion_of_work_eq_zero (h : (jobs j).work = 0) :
    σ.completion j = some (jobs j).release :=
  (σ.completion_eq_some_iff j).2 ⟨⟨le_rfl, by simp [h]⟩, fun _ ht ↦ ht.1⟩

/-- Job `j` has completed by `t` if its first time attaining its required service at or after
release exists and is no later than `t`. -/
def CompletedBy (t : ℝ≥0) : Prop := ∃ c, σ.completion j = some c ∧ c ≤ t

/-- A job has completed by `t` exactly when it has been released and has received at least its
required work by `t`, including when execution continues after completion. -/
theorem completedBy_iff {t : ℝ≥0} : σ.CompletedBy j t ↔
    (jobs j).release ≤ t ∧ (jobs j).work ≤ σ.service j t := by
  constructor
  · rintro ⟨c, hc, hct⟩
    obtain ⟨hr, he⟩ := ((σ.completion_eq_some_iff j).1 hc).1
    exact ⟨hr.trans hct, he ▸ σ.service_mono j hct⟩
  · rintro ⟨hr, hw⟩
    obtain ⟨x, ⟨hrx, hxt⟩, hx⟩ := intermediate_value_Icc hr (σ.continuous_service j).continuousOn
      (show (↑(jobs j).work : ℝ) ∈ Icc (σ.service j (jobs j).release) (σ.service j t) from
        ⟨by simp, hw⟩)
    cases hc : σ.completion j with
    | none => exact False.elim ((σ.completion_eq_none_iff j).1 hc ⟨x, hrx, hx⟩)
    | some c => exact ⟨c, hc, (((σ.completion_eq_some_iff j).1 hc).2 ⟨hrx, hx⟩).trans hxt⟩

/-- A job is active at `t` if it has been released and has not completed by `t`.
It may still be active after its deadline. -/
def Active (t : ℝ≥0) : Prop := (jobs j).release ≤ t ∧ ¬ σ.CompletedBy j t

/-- A job is active at `t` exactly when its release is no later than `t` and its accumulated
service through `t` is strictly less than its required work. -/
theorem active_iff {t : ℝ≥0} : σ.Active j t ↔
    (jobs j).release ≤ t ∧ σ.service j t < (jobs j).work := by
  rw [Active, σ.completedBy_iff]
  exact and_congr_right fun hr ↦ by simp [hr]

/-- A particular schedule is feasible if every job has completed by its own absolute deadline. -/
def Feasible : Prop := ∀ j, σ.CompletedBy j (jobs j).deadline

/-- A schedule is feasible exactly when each job receives at least its required work by its
deadline, counting only execution strictly before the deadline. -/
theorem feasible_iff : σ.Feasible ↔ ∀ j, (jobs j).work ≤ σ.service j (jobs j).deadline := by
  simp [Feasible, σ.completedBy_iff, Job.release_le_deadline]

end JobSchedule

/-- A finite family of independent jobs is feasible if there exists a measurable preemptive
one-processor schedule in which every job completes by its deadline. -/
def JobsFeasible {n : ℕ} (jobs : Fin n → Job) : Prop := ∃ σ : JobSchedule jobs, σ.Feasible

end Cslib.Scheduling.RealTime
