/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Scheduling.RealTime.MeasurableJobSchedules
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Examples of measurable one-processor job schedules

Two disjoint execution intervals of length `1/4` give a job its first half unit of service at
its deadline `1`. Other examples distinguish a pointwise assignment from positive service,
zero work from zero time available, and an idle schedule from an empty family of jobs.
-/

open MeasureTheory Set Cslib.Scheduling.RealTime
open scoped NNReal

namespace MeasurableJobSchedulesTests

private def idle {n : ℕ} (jobs : Fin n → Job) : JobSchedule jobs where
  assign _ := none
  measurable_assign := by
    let _ : MeasurableSpace (Option (Fin n)) := ⊤
    exact measurable_const.nullMeasurable
  released := by simp

example (jobs : Fin 0 → Job) : JobsFeasible jobs := ⟨idle jobs, fun j ↦ j.elim0⟩

example {n : ℕ} (jobs : Fin n → Job) (j : Fin n) (h : 0 < (jobs j).work) :
    (idle jobs).completion j = none := by
  apply ((idle jobs).completion_eq_none_iff j).2
  have hp : (0 : ℝ) < (jobs j).work := h
  simp [JobSchedule.service, idle, ne_of_lt hp]

example {n : ℕ} {jobs : Fin n → Job} (σ : JobSchedule jobs) (j : Fin n)
    (hd : (jobs j).deadline = (jobs j).release) :
    σ.CompletedBy j (jobs j).deadline ↔ (jobs j).work = 0 := by
  rw [σ.completedBy_iff, hd, σ.service_release, and_iff_right le_rfl]
  change (jobs j).work ≤ (0 : ℝ≥0) ↔ _
  exact le_bot_iff

private noncomputable def runOn (J : Job) (S : Set ℝ) (hm : MeasurableSet S)
    (hr : ∀ t ∈ S, (J.release : ℝ) ≤ t) : JobSchedule (fun _ : Fin 1 ↦ J) := by
  classical
  letI : MeasurableSpace (Option (Fin 1)) := ⊤
  exact {
    assign := fun t ↦ if t ∈ S then some 0 else none
    measurable_assign := (measurable_const.ite hm measurable_const).nullMeasurable
    released := by
      intro t j hj
      split at hj
      · exact hr t ‹_›
      · contradiction }

private theorem service_runOn (J : Job) (S : Set ℝ) (hm hr) (t : ℝ≥0) :
    (runOn J S hm hr).service 0 t = volume.real (Ico 0 (t : ℝ) ∩ S) := by
  classical
  unfold JobSchedule.service
  congr 2
  ext x
  by_cases h : x ∈ S <;> simp [runOn, h]

private noncomputable def job : Job :=
  ⟨1 / 4, 1 / 2, 1, by change (1 / 4 : ℝ) ≤ 1; norm_num⟩

private noncomputable def splitRun : JobSchedule (fun _ : Fin 1 ↦ job) :=
  runOn job (Ico (1 / 4) (1 / 2) ∪ Ico (3 / 4) 1) (measurableSet_Ico.union measurableSet_Ico)
    (by rintro t (h | h); exact h.1; exact le_trans (by norm_num [job]) h.1)

private theorem split_service (t : ℝ≥0) : splitRun.service 0 t =
    max (min (t : ℝ) (1 / 2) - 1 / 4) 0 + max (min (t : ℝ) 1 - 3 / 4) 0 := by
  rw [splitRun, service_runOn, inter_union_distrib_left, Ico_inter_Ico, Ico_inter_Ico]
  change volume.real (Ico (max 0 (1 / 4)) (min (t : ℝ) (1 / 2)) ∪
    Ico (max 0 (3 / 4)) (min (t : ℝ) 1)) = _
  rw [max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 4), max_eq_right (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  have hd : Disjoint (Ico (1 / 4 : ℝ) (min (t : ℝ) (1 / 2))) (Ico (3 / 4) (min (t : ℝ) 1)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h₁ := lt_of_lt_of_le hx.2 (min_le_right _ _)
    linarith [hy.1]
  rw [measureReal_union hd measurableSet_Ico (by simp) (by simp), Real.volume_real_Ico,
    Real.volume_real_Ico]

example : splitRun.completion 0 = some 1 := by
  apply (splitRun.completion_eq_some_iff 0).2
  refine ⟨⟨job.release_le_deadline, by norm_num [split_service, job]⟩, ?_⟩
  intro t ht
  have he := ht.2
  rw [split_service] at he
  change _ = (1 / 2 : ℝ) at he
  by_contra! hlt
  have h : (t : ℝ) < 1 := hlt
  rw [min_eq_left h.le] at he
  have h₁ : max (min (t : ℝ) (1 / 2) - 1 / 4) 0 ≤ 1 / 4 :=
    max_le (by linarith [min_le_right (t : ℝ) (1 / 2)]) (by norm_num)
  have h₂ : max ((t : ℝ) - 3 / 4) 0 < 1 / 4 := max_lt (by linarith) (by norm_num)
  linarith

-- Running exactly at release, but at no other instant, gives no work, even afterwards.
example (t : ℝ≥0) :
    (runOn job {(1 / 4 : ℝ)} (measurableSet_singleton _) (by simp [job])).service 0 t = 0 := by
  rw [service_runOn]
  exact measureReal_mono_null inter_subset_right (by simp [measureReal_def]) (by simp)

-- An execution at time zero cannot be inserted as a harmless null-set modification here.
example (σ : JobSchedule (fun _ : Fin 1 ↦ job)) : σ.assign 0 ≠ some 0 := by
  intro hj
  have := σ.released hj
  norm_num [job] at this

end MeasurableJobSchedulesTests
