/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Deadline-driven (EDF) feasibility (Liu-Layland Theorems 6-7)
-/

module

public import CSLibExt.Scheduling.RealTime.PeriodicTasks
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Deadline-driven (EDF) feasibility

Completed proofs of Liu-Layland Theorems 6 and 7 over the discrete
provider model in `CSLibExt.Scheduling.RealTime.PeriodicTasks`.

Source: C. L. Liu and J. W. Layland, "Scheduling Algorithms for
Multiprogramming in a Hard-Real-Time Environment", J. ACM 20(1), 1973,
Section 6. Theorem 6: under the deadline-driven algorithm there is no idle
time before an overflow. Theorem 7: the deadline-driven algorithm is
feasible if and only if total utilization is at most one.

Discrete-model adaptations: Theorem 6 is stated over the busy window
before the first overflow, since with nonzero phases the slots before the
first release are idle even before any overflow occurs, so the no-idle
claim starts from `windowStart`; the hyperperiod reduction is stated as a
bounded-overflow witness for overfull systems, with the bound using
`maxPhase` plus whole hyperperiods, since a hyperperiod-only first-overflow
bound is not valid for phased tasks in this discrete model.

## Main definitions

`maxPhase`, `insideRequests`, `windowStart`.

## Main results

`windowStart_le`, `edf_no_idle_before_overflow`,
`edf_window_serves_early_deadlines`, `period_dvd_hyperperiod`,
`hyperperiod_pos`, `release_add_hyperperiod`, `deadline_add_hyperperiod`,
`overflow_of_util_gt_one`, `edf_window_served_eq_length`,
`overflow_of_demand_exceeds`, `inside_demand_le_util_mul_window`,
`edf_feasible_iff_util_le_one`.
-/

@[expose] public section

namespace Cslib.Scheduling.RealTime

/-- Maximum release offset over a task set (`0` when there are no tasks). -/
def maxPhase {ι : Type*} [Fintype ι] (tasks : TaskSet ι) : ℕ :=
  match (Finset.univ.image (fun i => (tasks i).phase)).max with
  | none => 0
  | some m => m

/-- Requests whose windows lie fully inside `[a, b)`. -/
def insideRequests {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (a b : ℕ) : Finset (ι × ℕ) :=
  Finset.univ.biUnion (fun i =>
    ((Finset.range b).filter (fun k =>
      a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).image
      (fun k => (i, k)))

/-- Start of the busy window before `T`: one past the last slot below `T`
with no live request of deadline at most `T` (`0` if every slot has one). -/
noncomputable def windowStart {ι : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq ι] (tasks : TaskSet ι) (T : ℕ) : ℕ :=
  haveI : DecidablePred (fun s =>
      ¬ ∃ i k, IsLive tasks (produceSchedule tasks (deadlineRule tasks)) i k s ∧
        deadline tasks i k ≤ T) :=
    fun _ => Classical.propDecidable _
  match ((Finset.range T).filter (fun s =>
      ¬ ∃ i k, IsLive tasks (produceSchedule tasks (deadlineRule tasks)) i k s ∧
        deadline tasks i k ≤ T)).max with
  | none => 0
  | some m => m + 1

theorem windowStart_le {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    (tasks : TaskSet ι) (T : ℕ) : windowStart tasks T ≤ T := by
  unfold windowStart
  split
  · exact Nat.zero_le T
  · rename_i m hm
    have hmem := Finset.mem_of_max hm
    simp only [Finset.mem_filter, Finset.mem_range] at hmem
    obtain ⟨hlt, _⟩ := hmem
    omega

private theorem windowStart_contra {ι : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq ι] (tasks : TaskSet ι) (T s : ℕ)
    (hlo : windowStart tasks T ≤ s) (hhi : s < T)
    (hcon : ¬ ∃ i k, IsLive tasks (produceSchedule tasks (deadlineRule tasks))
      i k s ∧ deadline tasks i k ≤ T) : False := by
  letI : DecidablePred (fun s =>
      ¬ ∃ i k, IsLive tasks (produceSchedule tasks (deadlineRule tasks)) i k s ∧
        deadline tasks i k ≤ T) :=
    fun _ => Classical.propDecidable _
  have hsrange : s ∈ Finset.range T := Finset.mem_range.mpr hhi
  have hs_mem : s ∈ (Finset.range T).filter (fun s =>
      ¬ ∃ i k, IsLive tasks (produceSchedule tasks (deadlineRule tasks)) i k s ∧
        deadline tasks i k ≤ T) :=
    Finset.mem_filter.mpr ⟨hsrange, hcon⟩
  obtain ⟨b, hb⟩ := Finset.max_of_mem hs_mem
  cases hmax : ((Finset.range T).filter (fun s =>
      ¬ ∃ i k, IsLive tasks (produceSchedule tasks (deadlineRule tasks)) i k s ∧
        deadline tasks i k ≤ T)).max with
  | bot =>
    rw [hmax] at hb
    exact absurd hb WithBot.bot_ne_coe
  | coe m =>
    have hwm : windowStart tasks T = m + 1 := by
      unfold windowStart
      rw [hmax]
    have hsm : s ≤ m := Finset.le_max_of_eq hs_mem hmax
    rw [hwm] at hlo
    omega

private theorem isLive_congr {ι : Type*} {fi : Fintype ι} {d1 d2 : DecidableEq ι}
    (tasks : @TaskSet ι fi) (sched : Schedule ι) (i : ι) (k t : ℕ) :
    @IsLive ι fi d1 tasks sched i k t ↔ @IsLive ι fi d2 tasks sched i k t := by
  have h : d1 = d2 := Subsingleton.elim _ _
  subst h
  rfl

private theorem slot_serves_inside {ι : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq ι] (tasks : TaskSet ι) (T s : ℕ)
    (hlo : windowStart tasks T ≤ s) (hhi : s < T) (i : ι)
    (hs : produceSchedule tasks (deadlineRule tasks) s = some i) :
    ∃ k, currentRequest tasks i s = some k ∧
      IsLive tasks (produceSchedule tasks (deadlineRule tasks)) i k s ∧
      deadline tasks i k ≤ T ∧ windowStart tasks T ≤ release tasks i k := by
  obtain ⟨k, hliveLO, hcr, hopt⟩ :=
    (produceSchedule_spec tasks (deadlineRule tasks) s).2 i hs
  have hlive : IsLive tasks (produceSchedule tasks (deadlineRule tasks)) i k s :=
    (isLive_congr tasks (produceSchedule tasks (deadlineRule tasks)) i k s).mp
      hliveLO
  have hex : ∃ j l, IsLive tasks (produceSchedule tasks (deadlineRule tasks))
      j l s ∧ deadline tasks j l ≤ T := by
    by_contra hcon
    exact windowStart_contra tasks T s hlo hhi hcon
  obtain ⟨j, l, hlive2, hdlT⟩ := hex
  have hopt2 : deadline tasks i k < deadline tasks j l ∨
      (deadline tasks i k = deadline tasks j l ∧ i ≤ j) :=
    hopt j l ((isLive_congr tasks (produceSchedule tasks (deadlineRule tasks))
      j l s).mpr hlive2)
  have hdl : deadline tasks i k ≤ T := by
    cases hopt2 with
    | inl hlt => omega
    | inr heq =>
      obtain ⟨heq2, _⟩ := heq
      omega
  have hrel : windowStart tasks T ≤ release tasks i k := by
    by_contra hcon
    have hlt : release tasks i k < windowStart tasks T := not_le.mp hcon
    obtain ⟨_, ht, hC⟩ := hlive
    letI : DecidablePred (fun s =>
        ¬ ∃ i k, IsLive tasks (produceSchedule tasks (deadlineRule tasks)) i k s ∧
          deadline tasks i k ≤ T) :=
      fun _ => Classical.propDecidable _
    cases hmax : ((Finset.range T).filter (fun s =>
        ¬ ∃ i k, IsLive tasks (produceSchedule tasks (deadlineRule tasks)) i k s ∧
          deadline tasks i k ≤ T)).max with
    | bot =>
      have hw0 : windowStart tasks T = 0 := by
        unfold windowStart
        rw [hmax]
      rw [hw0] at hlt
      omega
    | coe m =>
      have hwm : windowStart tasks T = m + 1 := by
        unfold windowStart
        rw [hmax]
      have hmem := Finset.mem_of_max hmax
      rw [Finset.mem_filter, Finset.mem_range] at hmem
      obtain ⟨_, hnone⟩ := hmem
      rw [hwm] at hlo hlt
      have hlive_at_m : IsLive tasks (produceSchedule tasks (deadlineRule tasks))
          i k m := by
        unfold IsLive
        refine ⟨?_, ?_, ?_⟩
        · omega
        · omega
        · exact lt_of_le_of_lt
            (receivedWork_mono tasks (produceSchedule tasks (deadlineRule tasks))
              i k m s (by omega)) hC
      exact hnone ⟨i, k, hlive_at_m, hdl⟩
  exact ⟨k, hcr, hlive, hdl, hrel⟩

private theorem mem_insideRequests {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (a b : ℕ) (p : ι × ℕ)
    (hp : p ∈ insideRequests tasks a b) :
    ∃ i k, p = (i, k) ∧ k < b ∧ a ≤ release tasks i k ∧
      deadline tasks i k ≤ b := by
  unfold insideRequests at hp
  rw [Finset.mem_biUnion] at hp
  obtain ⟨i, _, himg⟩ := hp
  rw [Finset.mem_image] at himg
  obtain ⟨k, hk, heq⟩ := himg
  rw [Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨hkT, ha, hb⟩ := hk
  exact ⟨i, k, heq.symm, hkT, ha, hb⟩

private theorem demand_le_window_of_fulfilled {ι : Type*} [Fintype ι]
    [DecidableEq ι] (tasks : TaskSet ι) (sched : Schedule ι) (a b : ℕ)
    (hful : ∀ p ∈ insideRequests tasks a b, (tasks p.1).C ≤
      receivedWork tasks sched p.1 p.2 (deadline tasks p.1 p.2)) :
    (insideRequests tasks a b).sum (fun p => (tasks p.1).C) ≤ b - a := by
  have h1 : (insideRequests tasks a b).sum (fun p => (tasks p.1).C) ≤
      (insideRequests tasks a b).sum (fun p =>
        ((Finset.Ico (release tasks p.1 p.2) (deadline tasks p.1 p.2)).filter
          (fun s => sched s = some p.1)).card) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨i, k, rfl, _, _, _⟩ := mem_insideRequests tasks a b p hp
    have hC : (tasks i).C ≤
        receivedWork tasks sched i k (deadline tasks i k) :=
      hful (i, k) hp
    have hrw : receivedWork tasks sched i k (deadline tasks i k) =
        ((Finset.Ico (release tasks i k) (deadline tasks i k)).filter
          (fun s => sched s = some i)).card := by
      unfold receivedWork
      rw [min_self]
    rw [hrw] at hC
    exact hC
  have hdisj : Set.PairwiseDisjoint (↑(insideRequests tasks a b)) (fun (p : ι × ℕ) =>
      (Finset.Ico (release tasks p.1 p.2) (deadline tasks p.1 p.2)).filter
        (fun s => sched s = some p.1)) := by
    intro p₁ _ p₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs1 hs2
    rw [Finset.mem_filter] at hs1 hs2
    obtain ⟨hsIco1, hsch1⟩ := hs1
    obtain ⟨hsIco2, hsch2⟩ := hs2
    rw [Finset.mem_Ico] at hsIco1 hsIco2
    have htask : p₁.1 = p₂.1 :=
      Option.some_inj.mp (hsch1.symm.trans hsch2)
    rw [← htask] at hsIco2
    have hreq : p₁.2 = p₂.2 :=
      request_window_unique tasks p₁.1 s p₁.2 p₂.2 hsIco1 hsIco2
    obtain ⟨a1, b1⟩ := p₁
    obtain ⟨a2, b2⟩ := p₂
    have htask' : a1 = a2 := htask
    have hreq' : b1 = b2 := hreq
    apply hne
    rw [htask', hreq']
  have hcard : ((insideRequests tasks a b).biUnion (fun p =>
      (Finset.Ico (release tasks p.1 p.2) (deadline tasks p.1 p.2)).filter
        (fun s => sched s = some p.1))).card =
      (insideRequests tasks a b).sum (fun p =>
        ((Finset.Ico (release tasks p.1 p.2) (deadline tasks p.1 p.2)).filter
          (fun s => sched s = some p.1)).card) := by
    rw [Finset.card_biUnion hdisj]
  have hsub : (insideRequests tasks a b).biUnion (fun p =>
      (Finset.Ico (release tasks p.1 p.2) (deadline tasks p.1 p.2)).filter
        (fun s => sched s = some p.1)) ⊆ Finset.Ico a b := by
    intro s hs
    rw [Finset.mem_biUnion] at hs
    obtain ⟨p, hpmem, hsSp⟩ := hs
    obtain ⟨i, k, rfl, _, ha, hb⟩ := mem_insideRequests tasks a b p hpmem
    simp only [] at hsSp
    rw [Finset.mem_filter] at hsSp
    obtain ⟨hsIco, _⟩ := hsSp
    rw [Finset.mem_Ico] at hsIco ⊢
    obtain ⟨h1, h2⟩ := hsIco
    omega
  calc (insideRequests tasks a b).sum (fun p => (tasks p.1).C)
      ≤ (insideRequests tasks a b).sum (fun p =>
        ((Finset.Ico (release tasks p.1 p.2) (deadline tasks p.1 p.2)).filter
          (fun s => sched s = some p.1)).card) := h1
    _ = ((insideRequests tasks a b).biUnion (fun p =>
        (Finset.Ico (release tasks p.1 p.2) (deadline tasks p.1 p.2)).filter
          (fun s => sched s = some p.1))).card := hcard.symm
    _ ≤ (Finset.Ico a b).card := Finset.card_le_card hsub
    _ = b - a := Nat.card_Ico a b

private theorem fiber_sum_eq_card_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (i : ι) (a b : ℕ) :
    (((Finset.range b).filter
        (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).image
        (fun k => (i, k))).sum (fun p => (tasks p.1).C) =
      (((Finset.range b).filter
        (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).card) *
        (tasks i).C := by
  have hinj : Set.InjOn (fun (k : ℕ) => (i, k)) ↑((Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)) := by
    intro x _ y _ hxy
    exact congrArg Prod.snd hxy
  rw [Finset.sum_image hinj]
  show ((Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).sum
      (fun _ => (tasks i).C) =
    (((Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).card) *
      (tasks i).C
  rw [Finset.sum_const, Nat.nsmul_eq_mul]

private theorem fiber_card_mul_period_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (tasks : TaskSet ι) (i : ι) (a b : ℕ) :
    (((Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).card) *
      (tasks i).T ≤ b - a := by
  have hdisj : Set.PairwiseDisjoint (↑((Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)))
      (fun k => Finset.Ico (release tasks i k) (deadline tasks i k)) := by
    intro k₁ _ k₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs1 hs2
    rw [Finset.mem_Ico] at hs1 hs2
    exact hne (request_window_unique tasks i s k₁ k₂ hs1 hs2)
  have hcard : (((Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).biUnion
      (fun k => Finset.Ico (release tasks i k) (deadline tasks i k))).card =
      ((Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).sum
      (fun k => (Finset.Ico (release tasks i k) (deadline tasks i k)).card) := by
    rw [Finset.card_biUnion hdisj]
  have hsub : (((Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).biUnion
      (fun k => Finset.Ico (release tasks i k) (deadline tasks i k))) ⊆
      Finset.Ico a b := by
    intro s hs
    rw [Finset.mem_biUnion] at hs
    obtain ⟨k, hkmem, hsIco⟩ := hs
    rw [Finset.mem_filter, Finset.mem_range] at hkmem
    obtain ⟨_, ha, hb⟩ := hkmem
    rw [Finset.mem_Ico] at hsIco ⊢
    obtain ⟨h1, h2⟩ := hsIco
    omega
  have hper : ∀ k ∈ (Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b),
      (Finset.Ico (release tasks i k) (deadline tasks i k)).card =
        (tasks i).T := by
    intro k _
    rw [Nat.card_Ico]
    unfold release deadline
    have hring : (k + 1) * (tasks i).T =
        k * (tasks i).T + (tasks i).T := by ring
    omega
  have hsum : ((Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).sum
      (fun k => (Finset.Ico (release tasks i k) (deadline tasks i k)).card) ≤
      b - a := by
    rw [← hcard]
    calc (((Finset.range b).filter
        (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).biUnion
        (fun k => Finset.Ico (release tasks i k) (deadline tasks i k))).card
        ≤ (Finset.Ico a b).card := Finset.card_le_card hsub
      _ = b - a := Nat.card_Ico a b
  have hconst : ((Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).sum
      (fun k => (Finset.Ico (release tasks i k) (deadline tasks i k)).card) =
      (((Finset.range b).filter
      (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).card) *
        (tasks i).T := by
    rw [Finset.sum_congr rfl (fun k hk => hper k hk)]
    rw [Finset.sum_const, Nat.nsmul_eq_mul]
  omega

private theorem card_mul_le_window_mul_util (A c t W : ℕ) (h : A * t ≤ W)
    (ht : 0 < t) :
    ((A * c : ℕ) : ℚ) ≤ ((W : ℕ) : ℚ) * (((c : ℕ) : ℚ) / ((t : ℕ) : ℚ)) := by
  have h' : (A : ℚ) * (t : ℚ) ≤ (W : ℚ) := by
    rw [← Nat.cast_mul]
    exact Nat.cast_le.mpr h
  have htpos : (0 : ℚ) < (t : ℚ) := Nat.cast_pos.mpr ht
  have hcpos : (0 : ℚ) ≤ (c : ℚ) := Nat.cast_nonneg _
  rw [Nat.cast_mul, ← mul_div_assoc, le_div_iff₀ htpos]
  calc (A : ℚ) * (c : ℚ) * (t : ℚ) = ((A : ℚ) * (t : ℚ)) * (c : ℚ) := by ring
    _ ≤ (W : ℚ) * (c : ℚ) := mul_le_mul_of_nonneg_right h' hcpos

theorem edf_no_idle_before_overflow {ι : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq ι] (tasks : TaskSet ι) (T : ℕ)
    (hT : firstOverflow tasks (produceSchedule tasks (deadlineRule tasks)) =
      some T)
    (s : ℕ) (hlo : windowStart tasks T ≤ s) (hhi : s < T) :
    produceSchedule tasks (deadlineRule tasks) s ≠ none := by
  clear hT
  intro hcon
  have hnone :=
    (produceSchedule_idle_iff tasks (deadlineRule tasks) s).mp hcon
  have hcon2 : ¬ ∃ i k, IsLive tasks (produceSchedule tasks (deadlineRule tasks))
      i k s ∧ deadline tasks i k ≤ T := by
    intro hex
    obtain ⟨i, k, h1, _⟩ := hex
    exact hnone ⟨i, k, (isLive_congr tasks
      (produceSchedule tasks (deadlineRule tasks)) i k s).mpr h1⟩
  exact windowStart_contra tasks T s hlo hhi hcon2

theorem edf_window_serves_early_deadlines {ι : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq ι] (tasks : TaskSet ι) (T : ℕ)
    (hT : firstOverflow tasks (produceSchedule tasks (deadlineRule tasks)) =
      some T)
    (s : ℕ) (hlo : windowStart tasks T ≤ s) (hhi : s < T) (i : ι)
    (hs : produceSchedule tasks (deadlineRule tasks) s = some i) :
    ∃ k, currentRequest tasks i s = some k ∧ deadline tasks i k ≤ T := by
  clear hT
  obtain ⟨k, hcr, _, hdl, _⟩ := slot_serves_inside tasks T s hlo hhi i hs
  exact ⟨k, hcr, hdl⟩

theorem period_dvd_hyperperiod {ι : Type*} [Fintype ι] (tasks : TaskSet ι)
    (i : ι) : (tasks i).T ∣ hyperperiod tasks := by
  unfold hyperperiod
  exact Finset.dvd_lcm (Finset.mem_univ i)

theorem hyperperiod_pos {ι : Type*} [Fintype ι] (tasks : TaskSet ι) :
    1 ≤ hyperperiod tasks := by
  have : DecidableEq ι := fun a b => Classical.propDecidable _
  rw [Nat.one_le_iff_ne_zero]
  unfold hyperperiod
  have hall : ∀ s : Finset ι, s.lcm (fun i => (tasks i).T) ≠ 0 := by
    intro s
    refine Finset.induction ?_ ?_ s
    · rw [Finset.lcm_empty]
      exact one_ne_zero
    · intro a s ha ih
      rw [Finset.lcm_insert]
      change lcm ((tasks a).T) (s.lcm (fun i => (tasks i).T)) ≠ 0
      intro hcon
      rw [lcm_eq_zero_iff] at hcon
      cases hcon with
      | inl hz =>
        have hT := (tasks a).hT
        omega
      | inr hz => exact ih hz
  exact hall Finset.univ

theorem release_add_hyperperiod {ι : Type*} [Fintype ι] (tasks : TaskSet ι)
    (i : ι) (k : ℕ) :
    release tasks i (k + hyperperiod tasks / (tasks i).T) =
      release tasks i k + hyperperiod tasks := by
  have hT : (tasks i).T ∣ hyperperiod tasks := period_dvd_hyperperiod tasks i
  have hdiv : hyperperiod tasks / (tasks i).T * (tasks i).T =
      hyperperiod tasks :=
    Nat.div_mul_cancel hT
  have hexpand : (k + hyperperiod tasks / (tasks i).T) * (tasks i).T =
      k * (tasks i).T + hyperperiod tasks := by
    rw [Nat.add_mul, hdiv]
  unfold release
  omega

theorem deadline_add_hyperperiod {ι : Type*} [Fintype ι] (tasks : TaskSet ι)
    (i : ι) (k : ℕ) :
    deadline tasks i (k + hyperperiod tasks / (tasks i).T) =
      deadline tasks i k + hyperperiod tasks := by
  have hT : (tasks i).T ∣ hyperperiod tasks := period_dvd_hyperperiod tasks i
  have hdiv : hyperperiod tasks / (tasks i).T * (tasks i).T =
      hyperperiod tasks :=
    Nat.div_mul_cancel hT
  have hexpand : (k + hyperperiod tasks / (tasks i).T + 1) * (tasks i).T =
      (k + 1) * (tasks i).T + hyperperiod tasks := by
    have heq : k + hyperperiod tasks / (tasks i).T + 1 =
        (k + 1) + hyperperiod tasks / (tasks i).T := by omega
    rw [heq, Nat.add_mul, hdiv]
  unfold deadline
  omega

private theorem phase_le_maxPhase {ι : Type*} [Fintype ι] (tasks : TaskSet ι)
    (i : ι) : (tasks i).phase ≤ maxPhase tasks := by
  have hmem : (tasks i).phase ∈ Finset.univ.image (fun i => (tasks i).phase) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  obtain ⟨b, hb⟩ := Finset.max_of_mem hmem
  cases hmax : (Finset.univ.image (fun i => (tasks i).phase)).max with
  | bot =>
    rw [hmax] at hb
    exact absurd hb WithBot.bot_ne_coe
  | coe m =>
    have hle : (tasks i).phase ≤ m := Finset.le_max_of_eq hmem hmax
    have heq : maxPhase tasks = m := by unfold maxPhase; rw [hmax]
    rw [heq]
    exact hle

private theorem hyper_mul_div_eq (H T C q : ℕ) (hH : H = q * T) (hT : 1 ≤ T) :
    (H : ℚ) * ((C : ℚ) / (T : ℚ)) = (((q * C : ℕ)) : ℚ) := by
  have hTpos : (0 : ℚ) < (T : ℚ) := Nat.cast_pos.mpr (by omega)
  have hT0 : (T : ℚ) ≠ 0 := ne_of_gt hTpos
  have hHc : (H : ℚ) = (q : ℚ) * (T : ℚ) := by
    have h : ((q * T : ℕ) : ℚ) = (H : ℚ) := by rw [hH]
    rw [Nat.cast_mul] at h
    exact h.symm
  rw [hHc, Nat.cast_mul, mul_comm ((q : ℚ) * (T : ℚ)) _, div_mul_eq_mul_div,
    div_eq_iff hT0]
  ring

private theorem fiber_card_ge {ι : Type*} [Fintype ι]
    (tasks : TaskSet ι) (i : ι) (M q : ℕ)
    (hM : 1 ≤ M) (hqH : hyperperiod tasks = q * (tasks i).T) (hq : 1 ≤ q) :
    M * q - 1 ≤
      ((Finset.range (maxPhase tasks + M * hyperperiod tasks)).filter
        (fun k => maxPhase tasks ≤ release tasks i k ∧
          deadline tasks i k ≤ maxPhase tasks + M * hyperperiod tasks)).card := by
  set φ := (tasks i).phase with hφdef
  set T := (tasks i).T with hTdef
  set a := maxPhase tasks with hadef
  have hT : 1 ≤ T := (tasks i).hT
  have hφ : φ ≤ a := phase_le_maxPhase tasks i
  set D := (a - φ) / T with hDdef
  set k0 : ℕ := D + 1 with hk0def
  set L := M * q - 1 with hLdef
  have hdm : T * D + (a - φ) % T = a - φ := Nat.div_add_mod (a - φ) T
  have hmlt : (a - φ) % T < T := Nat.mod_lt (a - φ) (by omega)
  have hMq : 1 ≤ M * q := by simpa using Nat.mul_le_mul hM hq
  have hLM : L + 1 = M * q := Nat.sub_add_cancel hMq
  have hH : M * q * T = M * hyperperiod tasks := by
    have h1 : q * T = hyperperiod tasks := hqH.symm
    calc M * q * T = M * (q * T) := by ring
      _ = M * hyperperiod tasks := by rw [h1]
  have hexpand : k0 * T = T * D + T := by rw [hk0def]; ring
  have hlower : a ≤ φ + k0 * T := by omega
  have hupper : φ + k0 * T ≤ a + T := by omega
  have hmem : ∀ j, j < L →
      k0 + j ∈ (Finset.range (a + M * hyperperiod tasks)).filter
        (fun k => a ≤ release tasks i k ∧
          deadline tasks i k ≤ a + M * hyperperiod tasks) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range]
    set k := k0 + j with hkdef
    have hj1 : j + 1 ≤ L := hj
    have hkj : k + 1 + 1 ≤ k0 + M * q := by omega
    have hkk0 : k0 * T ≤ k * T := Nat.mul_le_mul_right _ (by omega)
    have hrel : a ≤ release tasks i k := by
      have h1 : a ≤ φ + k * T := by omega
      exact h1
    have hdead : deadline tasks i k ≤ a + M * hyperperiod tasks := by
      have hkmul : (k + 1) * T + T ≤ k0 * T + M * q * T := by
        calc (k + 1) * T + T = (k + 1 + 1) * T := by ring
          _ ≤ (k0 + M * q) * T := Nat.mul_le_mul_right _ hkj
          _ = k0 * T + M * q * T := by ring
      have h2 : φ + (k + 1) * T ≤ a + M * hyperperiod tasks := by omega
      exact h2
    have hkb : k < a + M * hyperperiod tasks := by
      have h1 : k + 1 ≤ (k + 1) * T := by
        calc k + 1 = (k + 1) * 1 := by ring
          _ ≤ (k + 1) * T := Nat.mul_le_mul_left _ hT
      have h2 : φ + (k + 1) * T ≤ a + M * hyperperiod tasks := hdead
      omega
    exact ⟨hkb, hrel, hdead⟩
  have hinj : Function.Injective (fun j => k0 + j) := by
    intro x y h
    dsimp only at h
    omega
  have hsub : (Finset.range L).image (fun j => k0 + j) ⊆
      (Finset.range (a + M * hyperperiod tasks)).filter
        (fun k => a ≤ release tasks i k ∧
          deadline tasks i k ≤ a + M * hyperperiod tasks) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [Finset.mem_range] at hj
    exact hmem j hj
  calc L = ((Finset.range L).image (fun j => k0 + j)).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    _ ≤ ((Finset.range (a + M * hyperperiod tasks)).filter
        (fun k => a ≤ release tasks i k ∧
          deadline tasks i k ≤ a + M * hyperperiod tasks)).card :=
      Finset.card_le_card hsub

private theorem inside_demand_eq_sum_fiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (a b : ℕ) :
    (insideRequests tasks a b).sum (fun p => (tasks p.1).C) =
      (Finset.univ : Finset ι).sum (fun i =>
        (((Finset.range b).filter
          (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).card) *
          (tasks i).C) := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) (fun i =>
      ((Finset.range b).filter
        (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).image
        (fun k => (i, k))) := by
    intro i _ j _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_image] at hp1 hp2
    obtain ⟨k₁, _, heq1⟩ := hp1
    obtain ⟨k₂, _, heq2⟩ := hp2
    have hpair : (i, k₁) = (j, k₂) := heq1.trans heq2.symm
    exact hne (congrArg Prod.fst hpair)
  unfold insideRequests
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro i _
  exact fiber_sum_eq_card_mul tasks i a b

theorem overflow_of_util_gt_one {ι : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq ι] (tasks : TaskSet ι) (hU : 1 < utilization tasks) :
    ∃ t, t ≤ maxPhase tasks +
          ((Finset.univ.sum (fun i => (tasks i).C) + 1) * hyperperiod tasks) ∧
      OverflowAt tasks (produceSchedule tasks (deadlineRule tasks)) t := by
  by_contra hcon
  set S := Finset.univ.sum (fun i => (tasks i).C) with hSdef
  set M := S + 1 with hMdef
  set H := hyperperiod tasks with hHdef
  set a := maxPhase tasks with hadef
  set W := M * H with hWdef
  set b := a + W with hbdef
  set K := Finset.univ.sum (fun i => (H / (tasks i).T) * (tasks i).C) with hKdef
  have hM : 1 ≤ M := by omega
  have hHpos : 1 ≤ H := hyperperiod_pos tasks
  have hq1 : ∀ i, 1 ≤ H / (tasks i).T := by
    intro i
    have hTpos : 0 < (tasks i).T := by
      have h := (tasks i).hT
      omega
    have hle : (tasks i).T ≤ H :=
      Nat.le_of_dvd (by omega) (period_dvd_hyperperiod tasks i)
    exact (Nat.le_div_iff_mul_le hTpos).mpr (by omega)
  have hfib : ∀ i ∈ (Finset.univ : Finset ι),
      M * (H / (tasks i).T) - 1 ≤
        (((Finset.range b).filter
          (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).card) := by
    intro i _
    have hdiv := period_dvd_hyperperiod tasks i
    have hqH : H = (H / (tasks i).T) * (tasks i).T :=
      (Nat.div_mul_cancel hdiv).symm
    exact fiber_card_ge tasks i M (H / (tasks i).T) hM hqH (hq1 i)
  have hdecomp : (insideRequests tasks a b).sum (fun p => (tasks p.1).C) =
      (Finset.univ : Finset ι).sum (fun i =>
        (((Finset.range b).filter
          (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).card) *
          (tasks i).C) :=
    inside_demand_eq_sum_fiber tasks a b
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      (M * (H / (tasks i).T) - 1) * (tasks i).C ≤
        (((Finset.range b).filter
          (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).card) *
          (tasks i).C := by
    intro i hi
    exact Nat.mul_le_mul_right _ (hfib i hi)
  have hcast : ∀ i ∈ (Finset.univ : Finset ι),
      ((((M * (H / (tasks i).T) - 1) * (tasks i).C : ℕ)) : ℚ) =
        (M : ℚ) * ((H / (tasks i).T : ℕ) : ℚ) * ((tasks i).C : ℚ) -
          ((tasks i).C : ℚ) := by
    intro i _
    have h1 : 1 ≤ M * (H / (tasks i).T) := by
      simpa using Nat.mul_le_mul hM (hq1 i)
    rw [Nat.cast_mul, Nat.cast_sub h1]
    push_cast
    ring
  have hKcast : (K : ℚ) =
      Finset.univ.sum (fun i => (((H / (tasks i).T) * (tasks i).C : ℕ) : ℚ)) := by
    rw [hKdef, Nat.cast_sum]
  have hsumlo : (Finset.univ.sum
      (fun i => ((((M * (H / (tasks i).T) - 1) * (tasks i).C : ℕ)) : ℚ))) =
      (M : ℚ) * (K : ℚ) - (S : ℚ) := by
    calc (Finset.univ.sum
            (fun i => ((((M * (H / (tasks i).T) - 1) * (tasks i).C : ℕ)) : ℚ)))
          = Finset.univ.sum (fun i => (M : ℚ) * ((H / (tasks i).T : ℕ) : ℚ) *
              ((tasks i).C : ℚ) - ((tasks i).C : ℚ)) :=
            Finset.sum_congr rfl hcast
        _ = Finset.univ.sum (fun i => (M : ℚ) * ((H / (tasks i).T : ℕ) : ℚ) *
              ((tasks i).C : ℚ)) -
              Finset.univ.sum (fun i => ((tasks i).C : ℚ)) :=
            Finset.sum_sub_distrib _ _
        _ = (M : ℚ) * (K : ℚ) - (S : ℚ) := by
            congr 1
            · rw [hKcast, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [Nat.cast_mul]
              ring
            · rw [hSdef, Nat.cast_sum]
  have hdemand_ge : (M : ℚ) * (K : ℚ) - (S : ℚ) ≤
      (((insideRequests tasks a b).sum (fun p => (tasks p.1).C) : ℕ) : ℚ) := by
    rw [← hsumlo, hdecomp, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.cast_le.mpr (hterm i hi)
  have hKU : (K : ℚ) = (H : ℚ) * utilization tasks := by
    rw [hKcast]
    unfold utilization
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hdiv := period_dvd_hyperperiod tasks i
    have hqH : H = (H / (tasks i).T) * (tasks i).T :=
      (Nat.div_mul_cancel hdiv).symm
    exact (hyper_mul_div_eq H (tasks i).T (tasks i).C (H / (tasks i).T) hqH
      (tasks i).hT).symm
  have hKH : H < K := by
    have hHpos' : (0 : ℚ) < (H : ℚ) := Nat.cast_pos.mpr (by omega)
    have hlt : (H : ℚ) * 1 < (H : ℚ) * utilization tasks :=
      mul_lt_mul_of_pos_left hU hHpos'
    rw [mul_one, ← hKU] at hlt
    exact Nat.cast_lt.mp hlt
  have hWlt : W < (insideRequests tasks a b).sum (fun p => (tasks p.1).C) := by
    have hMpos : (0 : ℚ) < (M : ℚ) := Nat.cast_pos.mpr (by omega)
    have hKS : (H : ℚ) + 1 ≤ (K : ℚ) := by
      have h : (((H + 1 : ℕ)) : ℚ) ≤ (K : ℚ) := Nat.cast_le.mpr hKH
      rwa [Nat.cast_add, Nat.cast_one] at h
    have h3 : (M : ℚ) * ((H : ℚ) + 1) ≤ (M : ℚ) * (K : ℚ) :=
      mul_le_mul_of_nonneg_left hKS (le_of_lt hMpos)
    have hMS : (M : ℚ) = (S : ℚ) + 1 := by
      rw [hMdef]
      push_cast
      ring
    have h3' : (M : ℚ) * (H : ℚ) + (M : ℚ) ≤ (M : ℚ) * (K : ℚ) := by
      have h := h3
      rwa [mul_add, mul_one] at h
    have h4 : (M : ℚ) * (H : ℚ) + ((S : ℚ) + 1) ≤ (M : ℚ) * (K : ℚ) := by
      rw [← hMS]
      exact h3'
    have h5 : (M : ℚ) * (H : ℚ) < (M : ℚ) * (K : ℚ) - (S : ℚ) := by
      rw [lt_sub_iff_add_lt]
      calc (M : ℚ) * (H : ℚ) + (S : ℚ)
          < (M : ℚ) * (H : ℚ) + (S : ℚ) + 1 := lt_add_one _
        _ = (M : ℚ) * (H : ℚ) + ((S : ℚ) + 1) := by ring
        _ ≤ (M : ℚ) * (K : ℚ) := h4
    have hW : ((W : ℕ) : ℚ) = (M : ℚ) * (H : ℚ) := by
      rw [hWdef, Nat.cast_mul]
    have h6 : ((W : ℕ) : ℚ) <
        (((insideRequests tasks a b).sum (fun p => (tasks p.1).C) : ℕ) : ℚ) := by
      rw [hW]
      exact lt_of_lt_of_le h5 hdemand_ge
    exact Nat.cast_lt.mp h6
  have hba : b - a = W := by omega
  have hlt : b - a < (insideRequests tasks a b).sum (fun p => (tasks p.1).C) := by
    rw [hba]
    exact hWlt
  have hful : ∀ p ∈ insideRequests tasks a b, (tasks p.1).C ≤
      receivedWork tasks (produceSchedule tasks (deadlineRule tasks)) p.1 p.2
        (deadline tasks p.1 p.2) := by
    intro p hp
    obtain ⟨i, k, rfl, _, _, hb⟩ := mem_insideRequests tasks a b p hp
    by_contra hlt2
    have hlt' : receivedWork tasks (produceSchedule tasks (deadlineRule tasks)) i k
        (deadline tasks i k) < (tasks i).C := not_le.mp hlt2
    have hov : OverflowAt tasks (produceSchedule tasks (deadlineRule tasks))
        (deadline tasks i k) := ⟨i, k, rfl, hlt'⟩
    exact hcon ⟨deadline tasks i k, hb, hov⟩
  have hle := demand_le_window_of_fulfilled tasks
    (produceSchedule tasks (deadlineRule tasks)) a b hful
  omega

theorem edf_window_served_eq_length {ι : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq ι] (tasks : TaskSet ι) (T : ℕ)
    (hT : firstOverflow tasks (produceSchedule tasks (deadlineRule tasks)) =
      some T) :
    (insideRequests tasks (windowStart tasks T) T).sum (fun p =>
          receivedWork tasks (produceSchedule tasks (deadlineRule tasks)) p.1
            p.2 T) =
      T - windowStart tasks T := by
  have hper : ∀ p ∈ insideRequests tasks (windowStart tasks T) T,
      receivedWork tasks (produceSchedule tasks (deadlineRule tasks)) p.1
        p.2 T =
        (((Finset.Ico (windowStart tasks T) T).filter (fun s =>
          produceSchedule tasks (deadlineRule tasks) s = some p.1 ∧
            currentRequest tasks p.1 s = some p.2))).card := by
    intro p hp
    obtain ⟨i, k, rfl, _, ha, hb⟩ := mem_insideRequests tasks
      (windowStart tasks T) T p hp
    have hstab : receivedWork tasks (produceSchedule tasks (deadlineRule tasks))
        i k T =
        (((Finset.Ico (release tasks i k) (deadline tasks i k)).filter
          (fun s => produceSchedule tasks (deadlineRule tasks) s = some i))).card := by
      rw [receivedWork_stable_after_deadline tasks
        (produceSchedule tasks (deadlineRule tasks)) i k T hb]
      unfold receivedWork
      rw [min_self]
    have hset : ((Finset.Ico (release tasks i k) (deadline tasks i k)).filter
          (fun s => produceSchedule tasks (deadlineRule tasks) s = some i)) =
        ((Finset.Ico (windowStart tasks T) T).filter (fun s =>
          produceSchedule tasks (deadlineRule tasks) s = some i ∧
            currentRequest tasks i s = some k)) := by
      rw [Finset.ext_iff]
      intro s
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · intro hs
        obtain ⟨hsIco, hsched⟩ := hs
        obtain ⟨hr1, hr2⟩ := hsIco
        have hlo : windowStart tasks T ≤ s := by omega
        have hhi : s < T := by omega
        obtain ⟨k', hcr', hlive', _, _⟩ :=
          slot_serves_inside tasks T s hlo hhi i hsched
        obtain ⟨hr1', hr2', _⟩ := hlive'
        have hkk : k' = k :=
          request_window_unique tasks i s k' k ⟨hr1', hr2'⟩ ⟨hr1, hr2⟩
        have hcr : currentRequest tasks i s = some k := by
          rw [← hkk]
          exact hcr'
        exact ⟨⟨hlo, hhi⟩, hsched, hcr⟩
      · intro hs
        obtain ⟨hsIco, hsched, hcr⟩ := hs
        obtain ⟨hw1, hw2⟩ := hsIco
        obtain ⟨k', hcr', hlive', _, _⟩ :=
          slot_serves_inside tasks T s hw1 hw2 i hsched
        have hkk : k' = k := Option.some_inj.mp (hcr'.symm.trans hcr)
        obtain ⟨hr1, hr2, _⟩ := hlive'
        rw [hkk] at hr1 hr2
        exact ⟨⟨hr1, hr2⟩, hsched⟩
    rw [hstab]
    exact congrArg Finset.card hset
  have hdisj : Set.PairwiseDisjoint
      (↑(insideRequests tasks (windowStart tasks T) T)) (fun (p : ι × ℕ) =>
        (Finset.Ico (windowStart tasks T) T).filter (fun s =>
          produceSchedule tasks (deadlineRule tasks) s = some p.1 ∧
            currentRequest tasks p.1 s = some p.2)) := by
    intro p₁ _ p₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs1 hs2
    rw [Finset.mem_filter] at hs1 hs2
    obtain ⟨_, hsch1, hcr1⟩ := hs1
    obtain ⟨_, hsch2, hcr2⟩ := hs2
    obtain ⟨a1, b1⟩ := p₁
    obtain ⟨a2, b2⟩ := p₂
    have htask' : a1 = a2 := Option.some_inj.mp (hsch1.symm.trans hsch2)
    rw [htask'] at hcr1
    have hreq' : b1 = b2 := Option.some_inj.mp (hcr1.symm.trans hcr2)
    apply hne
    rw [htask', hreq']
  have hcard : ((insideRequests tasks (windowStart tasks T) T).biUnion
      (fun p => (Finset.Ico (windowStart tasks T) T).filter (fun s =>
        produceSchedule tasks (deadlineRule tasks) s = some p.1 ∧
          currentRequest tasks p.1 s = some p.2))).card =
      (insideRequests tasks (windowStart tasks T) T).sum (fun p =>
        (((Finset.Ico (windowStart tasks T) T).filter (fun s =>
          produceSchedule tasks (deadlineRule tasks) s = some p.1 ∧
            currentRequest tasks p.1 s = some p.2))).card) := by
    rw [Finset.card_biUnion hdisj]
  have hunion : (insideRequests tasks (windowStart tasks T) T).biUnion
      (fun p => (Finset.Ico (windowStart tasks T) T).filter (fun s =>
        produceSchedule tasks (deadlineRule tasks) s = some p.1 ∧
          currentRequest tasks p.1 s = some p.2)) =
      Finset.Ico (windowStart tasks T) T := by
    rw [Finset.ext_iff]
    intro s
    constructor
    · intro hs
      rw [Finset.mem_biUnion] at hs
      obtain ⟨p, _, hsG⟩ := hs
      rw [Finset.mem_filter] at hsG
      exact hsG.1
    · intro hs
      rw [Finset.mem_Ico] at hs
      obtain ⟨hw1, hw2⟩ := hs
      have hbusy := edf_no_idle_before_overflow tasks T hT s hw1 hw2
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists.mp hbusy
      obtain ⟨k, hcr, _, hdl, hrel⟩ :=
        slot_serves_inside tasks T s hw1 hw2 i hi.symm
      have hkT : k < T := by
        have hTi : 1 ≤ (tasks i).T := (tasks i).hT
        have hle : k + 1 ≤ (tasks i).T * (k + 1) := by
          have hmul := Nat.mul_le_mul_right (k + 1) hTi
          rw [Nat.one_mul] at hmul
          exact hmul
        have hcomm : (k + 1) * (tasks i).T = (tasks i).T * (k + 1) :=
          mul_comm _ _
        unfold deadline at hdl
        omega
      have hmem : (i, k) ∈ insideRequests tasks (windowStart tasks T) T := by
        unfold insideRequests
        rw [Finset.mem_biUnion]
        refine ⟨i, Finset.mem_univ i, ?_⟩
        rw [Finset.mem_image]
        refine ⟨k, ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hkT, hrel, hdl⟩
      have hsG : s ∈ (Finset.Ico (windowStart tasks T) T).filter (fun s =>
          produceSchedule tasks (deadlineRule tasks) s = some i ∧
            currentRequest tasks i s = some k) := by
        rw [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨hw1, hw2⟩, hi.symm, hcr⟩
      exact Finset.mem_biUnion.mpr ⟨(i, k), hmem, hsG⟩
  have hsum : (insideRequests tasks (windowStart tasks T) T).sum (fun p =>
          receivedWork tasks (produceSchedule tasks (deadlineRule tasks)) p.1
            p.2 T) =
      (insideRequests tasks (windowStart tasks T) T).sum (fun p =>
        (((Finset.Ico (windowStart tasks T) T).filter (fun s =>
          produceSchedule tasks (deadlineRule tasks) s = some p.1 ∧
            currentRequest tasks p.1 s = some p.2))).card) :=
    Finset.sum_congr rfl (fun p hp => hper p hp)
  rw [hsum, ← hcard, hunion, Nat.card_Ico]

theorem overflow_of_demand_exceeds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (sched : Schedule ι) (a b : ℕ)
    (h : b - a < (insideRequests tasks a b).sum (fun p => (tasks p.1).C)) :
    ∃ t, t ≤ b ∧ OverflowAt tasks sched t := by
  by_contra hcon
  have hful : ∀ p ∈ insideRequests tasks a b, (tasks p.1).C ≤
      receivedWork tasks sched p.1 p.2 (deadline tasks p.1 p.2) := by
    intro p hp
    obtain ⟨i, k, rfl, _, _, hb⟩ := mem_insideRequests tasks a b p hp
    by_contra hlt
    have hlt' : receivedWork tasks sched i k (deadline tasks i k) <
        (tasks i).C := not_le.mp hlt
    have hov : OverflowAt tasks sched (deadline tasks i k) := ⟨i, k, rfl, hlt'⟩
    exact hcon ⟨deadline tasks i k, hb, hov⟩
  have hle := demand_le_window_of_fulfilled tasks sched a b hful
  omega

theorem inside_demand_le_util_mul_window {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : TaskSet ι) (a b : ℕ) :
    ((insideRequests tasks a b).sum (fun p => (tasks p.1).C) : ℚ) ≤
      ((b - a : ℕ) : ℚ) * utilization tasks := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) (fun i =>
      ((Finset.range b).filter
        (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).image
        (fun k => (i, k))) := by
    intro i _ j _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_image] at hp1 hp2
    obtain ⟨k₁, _, heq1⟩ := hp1
    obtain ⟨k₂, _, heq2⟩ := hp2
    have hpair : (i, k₁) = (j, k₂) := heq1.trans heq2.symm
    exact hne (congrArg Prod.fst hpair)
  have hsum : (insideRequests tasks a b).sum (fun p => (tasks p.1).C) =
      (Finset.univ : Finset ι).sum (fun i =>
        ((Finset.range b).filter
          (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).card *
          (tasks i).C) := by
    unfold insideRequests
    rw [Finset.sum_biUnion hdisj]
    apply Finset.sum_congr rfl
    intro i _
    exact fiber_sum_eq_card_mul tasks i a b
  rw [← Nat.cast_sum, hsum, Nat.cast_sum]
  have hper : ∀ i ∈ (Finset.univ : Finset ι),
      ((((Finset.range b).filter
        (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).card *
        (tasks i).C : ℕ) : ℚ) ≤
        ((b - a : ℕ) : ℚ) * ((((tasks i).C : ℕ) : ℚ) / (((tasks i).T : ℕ) : ℚ)) := by
    intro i _
    have hTi : 1 ≤ (tasks i).T := (tasks i).hT
    have hpos : 0 < (tasks i).T := by omega
    exact card_mul_le_window_mul_util _ _ _ _
      (fiber_card_mul_period_le tasks i a b) hpos
  have hmul : (Finset.univ : Finset ι).sum (fun i =>
        ((b - a : ℕ) : ℚ) * ((((tasks i).C : ℕ) : ℚ) / (((tasks i).T : ℕ) : ℚ))) =
      ((b - a : ℕ) : ℚ) * utilization tasks := by
    unfold utilization
    simp only [Finset.mul_sum]
  calc ((Finset.univ : Finset ι).sum (fun i =>
            ((((Finset.range b).filter
              (fun k => a ≤ release tasks i k ∧ deadline tasks i k ≤ b)).card *
              (tasks i).C : ℕ) : ℚ)))
        ≤ (Finset.univ : Finset ι).sum (fun i =>
            ((b - a : ℕ) : ℚ) * ((((tasks i).C : ℕ) : ℚ) / (((tasks i).T : ℕ) : ℚ))) :=
          Finset.sum_le_sum hper
      _ = ((b - a : ℕ) : ℚ) * utilization tasks := hmul

private theorem receivedWork_le_C {ι : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq ι] (tasks : TaskSet ι) (i : ι) (k t : ℕ) :
    receivedWork tasks (produceSchedule tasks (deadlineRule tasks)) i k t ≤
      (tasks i).C := by
  induction t with
  | zero =>
    unfold receivedWork
    have hsub : ((Finset.Ico (release tasks i k)
        (min 0 (deadline tasks i k))).filter
        (fun s => produceSchedule tasks (deadlineRule tasks) s = some i)) ⊆
        ∅ := by
      intro s hs
      rw [Finset.mem_filter, Finset.mem_Ico] at hs
      obtain ⟨⟨_, hlt⟩, _⟩ := hs
      exact False.elim (by omega)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_empty] at hcard
    exact le_trans hcard (Nat.zero_le _)
  | succ t ih =>
    by_cases h : (produceSchedule tasks (deadlineRule tasks) t = some i ∧
      release tasks i k ≤ t ∧ t < deadline tasks i k)
    · obtain ⟨hsched, hrel, hdead⟩ := h
      obtain ⟨k', hliveLO, -, -⟩ :=
        (produceSchedule_spec tasks (deadlineRule tasks) t).2 i hsched
      have hlive' : IsLive tasks (produceSchedule tasks (deadlineRule tasks))
          i k' t :=
        (isLive_congr tasks (produceSchedule tasks (deadlineRule tasks))
          i k' t).mp hliveLO
      obtain ⟨hrel', hdead', hC'⟩ := hlive'
      have hkk : k = k' :=
        (request_window_unique tasks i t k' k ⟨hrel', hdead'⟩ ⟨hrel, hdead⟩).symm
      subst hkk
      have hstep : receivedWork tasks
          (produceSchedule tasks (deadlineRule tasks)) i k (t + 1) =
          receivedWork tasks (produceSchedule tasks (deadlineRule tasks))
            i k t + 1 := by
        unfold receivedWork
        have e1 : min (t + 1) (deadline tasks i k) = t + 1 := by omega
        have e2 : min t (deadline tasks i k) = t := by omega
        rw [e1, e2]
        have hset : ((Finset.Ico (release tasks i k) (t + 1)).filter
            (fun s => produceSchedule tasks (deadlineRule tasks) s = some i)) =
            insert t ((Finset.Ico (release tasks i k) t).filter
              (fun s => produceSchedule tasks (deadlineRule tasks) s = some i)) := by
          rw [Finset.ext_iff]
          intro s
          simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert]
          constructor
          · intro hhh
            obtain ⟨⟨hr1, hs1⟩, hsc⟩ := hhh
            by_cases heq : s = t
            · exact Or.inl heq
            · exact Or.inr ⟨⟨hr1, by omega⟩, hsc⟩
          · intro hhh
            cases hhh with
            | inl heq =>
              subst heq
              exact ⟨⟨hrel, by omega⟩, hsched⟩
            | inr hmm =>
              obtain ⟨⟨hr1, hs1⟩, hsc⟩ := hmm
              exact ⟨⟨hr1, by omega⟩, hsc⟩
        have hnot : t ∉ (Finset.Ico (release tasks i k) t).filter
            (fun s => produceSchedule tasks (deadlineRule tasks) s = some i) := by
          intro hmem
          rw [Finset.mem_filter, Finset.mem_Ico] at hmem
          obtain ⟨⟨_, hlt⟩, _⟩ := hmem
          omega
        rw [hset, Finset.card_insert_of_notMem hnot]
      omega
    · have hstep : receivedWork tasks
          (produceSchedule tasks (deadlineRule tasks)) i k (t + 1) =
          receivedWork tasks (produceSchedule tasks (deadlineRule tasks))
            i k t := by
        unfold receivedWork
        by_cases hdt : t < deadline tasks i k
        · have e1 : min (t + 1) (deadline tasks i k) = t + 1 := by omega
          have e2 : min t (deadline tasks i k) = t := by omega
          rw [e1, e2]
          by_cases hrel : release tasks i k ≤ t
          · have hset : ((Finset.Ico (release tasks i k) (t + 1)).filter
                (fun s => produceSchedule tasks (deadlineRule tasks) s = some i)) =
                (Finset.Ico (release tasks i k) t).filter
                  (fun s => produceSchedule tasks (deadlineRule tasks) s = some i) := by
              rw [Finset.ext_iff]
              intro s
              simp only [Finset.mem_filter, Finset.mem_Ico]
              constructor
              · intro hhh
                obtain ⟨⟨hr1, hs1⟩, hsc⟩ := hhh
                by_cases heq : s = t
                · subst heq
                  exact absurd ⟨hsc, hrel, hdt⟩ h
                · exact ⟨⟨hr1, by omega⟩, hsc⟩
              · intro hhh
                obtain ⟨⟨hr1, hs1⟩, hsc⟩ := hhh
                exact ⟨⟨hr1, by omega⟩, hsc⟩
            rw [hset]
          · have hset : ((Finset.Ico (release tasks i k) (t + 1)).filter
                (fun s => produceSchedule tasks (deadlineRule tasks) s = some i)) =
                (Finset.Ico (release tasks i k) t).filter
                  (fun s => produceSchedule tasks (deadlineRule tasks) s = some i) := by
              rw [Finset.ext_iff]
              intro s
              simp only [Finset.mem_filter, Finset.mem_Ico]
              constructor
              · intro hhh
                obtain ⟨⟨hr1, hs1⟩, _⟩ := hhh
                exact False.elim (by omega)
              · intro hhh
                obtain ⟨⟨hr1, hs1⟩, _⟩ := hhh
                exact False.elim (by omega)
            rw [hset]
        · have e1 : min (t + 1) (deadline tasks i k) =
            deadline tasks i k := by omega
          have e2 : min t (deadline tasks i k) = deadline tasks i k := by omega
          rw [e1, e2]
      omega

private theorem overflow_mem_inside {ι : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq ι] (tasks : TaskSet ι) (T : ℕ) (i : ι) (k : ℕ)
    (hdead : deadline tasks i k = T)
    (hov : RequestOverflow tasks (produceSchedule tasks (deadlineRule tasks))
      i k) :
    (i, k) ∈ insideRequests tasks (windowStart tasks T) T := by
  have hTi : 1 ≤ (tasks i).T := (tasks i).hT
  have hle : k + 1 ≤ (tasks i).T * (k + 1) := by
    have hmul := Nat.mul_le_mul_right (k + 1) hTi
    rw [Nat.one_mul] at hmul
    exact hmul
  have hkT : k < T := by
    have hcomm : (k + 1) * (tasks i).T = (tasks i).T * (k + 1) :=
      mul_comm _ _
    have hdead' := hdead
    unfold deadline at hdead'
    omega
  have hrel : windowStart tasks T ≤ release tasks i k := by
    by_contra hcon
    have hlt : release tasks i k < windowStart tasks T := not_le.mp hcon
    have hC : receivedWork tasks (produceSchedule tasks (deadlineRule tasks))
        i k T < (tasks i).C := by
      have hrw := hov
      unfold RequestOverflow at hrw
      rwa [hdead] at hrw
    letI : DecidablePred (fun s =>
        ¬ ∃ i k, IsLive tasks (produceSchedule tasks (deadlineRule tasks)) i k s ∧
          deadline tasks i k ≤ T) :=
      fun _ => Classical.propDecidable _
    cases hmax : ((Finset.range T).filter (fun s =>
        ¬ ∃ i k, IsLive tasks (produceSchedule tasks (deadlineRule tasks)) i k s ∧
          deadline tasks i k ≤ T)).max with
    | bot =>
      have hw0 : windowStart tasks T = 0 := by
        unfold windowStart
        rw [hmax]
      rw [hw0] at hlt
      omega
    | coe m =>
      have hwm : windowStart tasks T = m + 1 := by
        unfold windowStart
        rw [hmax]
      have hmem := Finset.mem_of_max hmax
      rw [Finset.mem_filter, Finset.mem_range] at hmem
      obtain ⟨hmT, hnone⟩ := hmem
      rw [hwm] at hlt
      have hlive_at_m : IsLive tasks (produceSchedule tasks (deadlineRule tasks))
          i k m := by
        unfold IsLive
        refine ⟨?_, ?_, ?_⟩
        · omega
        · omega
        · exact lt_of_le_of_lt
            (receivedWork_mono tasks (produceSchedule tasks (deadlineRule tasks))
              i k m T (by omega)) hC
      exact hnone ⟨i, k, hlive_at_m, hdead.le⟩
  unfold insideRequests
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  rw [Finset.mem_image]
  refine ⟨k, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨hkT, hrel, hdead.le⟩

theorem edf_feasible_iff_util_le_one {ι : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq ι] (tasks : TaskSet ι) :
    Feasible tasks (produceSchedule tasks (deadlineRule tasks)) ↔
      utilization tasks ≤ 1 := by
  constructor
  · intro hfeas
    by_contra hcon
    have hgt : 1 < utilization tasks := lt_of_not_ge hcon
    obtain ⟨t, -, hov⟩ := overflow_of_util_gt_one tasks hgt
    obtain ⟨i, k, -, hro⟩ := hov
    exact (hfeas i k) hro
  · intro hU
    by_contra hcon
    have hnone : firstOverflow tasks
        (produceSchedule tasks (deadlineRule tasks)) ≠ none := by
      intro h
      exact hcon ((firstOverflow_eq_none_iff tasks
        (produceSchedule tasks (deadlineRule tasks))).mp h)
    obtain ⟨T, hT⟩ := Option.ne_none_iff_exists.mp hnone
    have hovT := ((firstOverflow_eq_some_iff tasks
      (produceSchedule tasks (deadlineRule tasks)) T).mp hT.symm).1
    obtain ⟨iw, kw, hdeadw, hrow⟩ := hovT
    have hmemw : (iw, kw) ∈ insideRequests tasks (windowStart tasks T) T :=
      overflow_mem_inside tasks T iw kw hdeadw hrow
    have hserved := edf_window_served_eq_length tasks T hT.symm
    have hdemand := inside_demand_le_util_mul_window tasks
      (windowStart tasks T) T
    have hhub : ((T - windowStart tasks T : ℕ) : ℚ) * utilization tasks ≤
        ((T - windowStart tasks T : ℕ) : ℚ) := by
      have h := mul_le_mul_of_nonneg_left hU
        (Nat.cast_nonneg (T - windowStart tasks T))
      rwa [mul_one] at h
    have hleQ := le_trans hdemand hhub
    rw [← Nat.cast_sum] at hleQ
    have hnat : (insideRequests tasks (windowStart tasks T) T).sum
        (fun p => (tasks p.1).C) ≤ T - windowStart tasks T :=
      Nat.cast_le.mp hleQ
    have hstrict : (insideRequests tasks (windowStart tasks T) T).sum
          (fun p => receivedWork tasks
            (produceSchedule tasks (deadlineRule tasks)) p.1 p.2 T) <
          (insideRequests tasks (windowStart tasks T) T).sum
            (fun p => (tasks p.1).C) := by
      apply Finset.sum_lt_sum
      · intro p hp
        obtain ⟨i, k, rfl, -, -, -⟩ :=
          mem_insideRequests tasks (windowStart tasks T) T p hp
        exact receivedWork_le_C tasks i k T
      · refine ⟨(iw, kw), hmemw, ?_⟩
        show receivedWork tasks (produceSchedule tasks (deadlineRule tasks))
          iw kw T < (tasks iw).C
        have hstab := receivedWork_stable_after_deadline tasks
          (produceSchedule tasks (deadlineRule tasks)) iw kw T hdeadw.le
        rw [hstab]
        exact hrow
    omega

end Cslib.Scheduling.RealTime
