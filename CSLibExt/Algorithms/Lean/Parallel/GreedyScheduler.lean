/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Parallel.Brent

/-!
# Greedy schedulers: `p T ≤ n + (p - 1) D`

A *greedy* schedule never leaves a ready task waiting while a processor is idle
(`Schedule.Greedy`). For unit-time tasks such a schedule on `p` processors takes `T` steps with
`p T ≤ n + (p - 1) D`, where `n` is the work and `D` the span: this is the unit-task case of
Graham's analysis of list scheduling (Graham, *Bounds for certain multiprocessing anomalies*,
Bell System Tech. J. 45, 1966), and it implies the bound `T_P ≤ T_1 / P + T_∞` of CLRS, third
edition, Theorem 27.1.

Main results:

* `Schedule.incomplete_lt_depth`: in a greedy schedule, fewer than `depth v` incomplete steps
  (steps with fewer than `p` tasks) precede the step of task `v`: at the last incomplete step
  before it, `v` was not ready, so one of its predecessors had not finished.
* `Schedule.mul_complete_le`: complete steps number at most `n / p`;
  `Schedule.one_le_load`: a greedy schedule runs at least one task in every step.
* `Schedule.greedy_length_le` (**the greedy bound**): `p T ≤ n + (p - 1) D`;
  `Schedule.greedy_length` (CLRS Theorem 27.1): `p T ≤ n + p D`, that is `T ≤ n / p + D`.

## Cost model

As in `Brent.lean`: unit-time tasks on identical processors, scheduling overhead free.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Parallel.Brent

variable {n : ℕ} {G : Dag n} {p : ℕ}

/-- The tasks run in step `t`. -/
def Schedule.load (S : Schedule G p) (t : ℕ) : ℕ := (Finset.univ.filter fun v => S.time v = t).card

/-- A task is *ready* at step `t` if it has not run yet and all its predecessors ran earlier. -/
def Schedule.Ready (S : Schedule G p) (t : ℕ) (v : Fin n) : Prop :=
  t < S.time v ∧ ∀ u ∈ G.preds v, S.time u < t

/-- A schedule is *greedy* if a step leaves a ready task waiting only when all `p` processors are
busy. -/
def Schedule.Greedy (S : Schedule G p) : Prop := ∀ t v, S.Ready t v → S.load t = p

/-- Greediness only constrains the steps of the schedule: a task is never ready at or after the
last step. -/
theorem Schedule.greedy_iff (S : Schedule G p) :
    S.Greedy ↔ ∀ t < S.length, ∀ v, S.Ready t v → S.load t = p := by
  constructor
  · exact fun h t _ v hv => h t v hv
  · intro h t v hv
    exact h t (hv.1.trans (S.time_lt_length v)) v hv

instance (S : Schedule G p) (t : ℕ) (v : Fin n) : Decidable (S.Ready t v) := by
  unfold Schedule.Ready; infer_instance

/-- Greediness is decidable, so concrete schedules can be checked by `decide`. -/
instance (S : Schedule G p) : Decidable S.Greedy :=
  decidable_of_iff _ S.greedy_iff.symm

/-- The number of incomplete steps (fewer than `p` tasks) before step `t`. -/
def Schedule.incomplete (S : Schedule G p) (t : ℕ) : ℕ :=
  ((Finset.range t).filter fun s => S.load s < p).card

theorem Schedule.incomplete_mono (S : Schedule G p) {s t : ℕ} (h : s ≤ t) :
    S.incomplete s ≤ S.incomplete t :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

/-- **Each incomplete step advances the critical path**: in a greedy schedule, fewer than
`depth v` incomplete steps precede the step of task `v`. -/
theorem Schedule.incomplete_lt_depth (S : Schedule G p) (hS : S.Greedy) :
    ∀ (t : ℕ) (v : Fin n), S.time v = t → S.incomplete t < depth G v := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v hvt
    set I := (Finset.range t).filter fun s => S.load s < p with hI
    by_cases hne : I.Nonempty
    · -- the last incomplete step before `t`
      set s := I.max' hne
      have hsI : s ∈ I := I.max'_mem hne
      have hst : s < t := Finset.mem_range.1 (Finset.mem_filter.1 hsI).1
      have hsload : S.load s < p := (Finset.mem_filter.1 hsI).2
      -- `v` was not ready at step `s`, so a predecessor ran at `s` or later
      have hnr : ¬ S.Ready s v := fun hr => by have := hS s v hr; omega
      obtain ⟨u, hu, hus⟩ : ∃ u ∈ G.preds v, s ≤ S.time u := by
        by_contra hall
        push Not at hall
        exact hnr ⟨by omega, hall⟩
      have hut : S.time u < t := hvt ▸ S.prec v u hu
      have ihu := ih (S.time u) hut u rfl
      have hdep := depth_lt_of_mem G hu
      -- the incomplete steps before `t` are those before `s`, and `s`
      have hsplit : S.incomplete t = S.incomplete s + 1 := by
        unfold Schedule.incomplete
        rw [← hI]
        have : I = ((Finset.range s).filter fun s' => S.load s' < p) ∪ {s} := by
          ext s'
          simp only [hI, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
            Finset.mem_singleton]
          constructor
          · rintro ⟨h1, h2⟩
            by_cases h : s' < s
            · exact Or.inl ⟨h, h2⟩
            · right
              have : s' ≤ s := I.le_max' s' (Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2⟩)
              omega
          · rintro (⟨h1, h2⟩ | rfl)
            · exact ⟨by omega, h2⟩
            · exact ⟨hst, hsload⟩
        rw [this, Finset.card_union_of_disjoint (by simp), Finset.card_singleton]
      have := S.incomplete_mono hus
      omega
    · have : S.incomplete t = 0 := by
        unfold Schedule.incomplete
        rw [← hI, Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty]
      have := one_le_depth G v
      omega

theorem Schedule.load_le (S : Schedule G p) (t : ℕ) : S.load t ≤ p := S.cap t

/-- The loads of the steps add up to the work. -/
theorem Schedule.sum_load (S : Schedule G p) :
    ∑ t ∈ Finset.range S.length, S.load t = n := by
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.range S.length)
    (f := S.time) fun v _ => Finset.mem_range.2 (S.time_lt_length v)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

/-- Complete steps (all `p` processors busy) number at most `n / p`. -/
theorem Schedule.mul_complete_le (S : Schedule G p) :
    p * ((Finset.range S.length).filter fun s => ¬ S.load s < p).card ≤ n := by
  calc p * ((Finset.range S.length).filter fun s => ¬ S.load s < p).card
      = ∑ _s ∈ (Finset.range S.length).filter (fun s => ¬ S.load s < p), p := by
        rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
    _ = ∑ s ∈ (Finset.range S.length).filter (fun s => ¬ S.load s < p), S.load s :=
        Finset.sum_congr rfl fun s hs => by
          have := (Finset.mem_filter.1 hs).2
          have := S.load_le s
          omega
    _ ≤ ∑ s ∈ Finset.range S.length, S.load s :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = n := S.sum_load

/-- In a greedy schedule there are at most `span` incomplete steps. -/
theorem Schedule.incomplete_length_le (S : Schedule G p) (hS : S.Greedy) :
    S.incomplete S.length ≤ span G := by
  rcases Nat.eq_zero_or_pos S.length with h0 | hpos
  · rw [h0]; simp [Schedule.incomplete]
  · -- a task runs in the last step
    obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup (s := Finset.univ)
      (Finset.univ_nonempty_iff.2 ⟨(Classical.choice (by
        by_contra hn
        have : S.length = 0 := by
          unfold Schedule.length
          rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hn), Finset.sup_empty]
          rfl
        omega) : Fin n)⟩) (fun v => S.time v + 1)
    have hlast : S.time v + 1 = S.length := hv.symm
    have hlt := S.incomplete_lt_depth hS (S.time v) v rfl
    have hstep : S.incomplete S.length ≤ S.incomplete (S.time v) + 1 := by
      unfold Schedule.incomplete
      rw [← hlast, Finset.range_add_one, Finset.filter_insert]
      split_ifs
      · exact Finset.card_insert_le _ _
      · exact Nat.le_succ _
    have := depth_le_span G v
    omega

/-- Before the last step some task is still to run. -/
theorem Schedule.exists_le_time (S : Schedule G p) {t : ℕ} (ht : t < S.length) :
    ∃ v, t ≤ S.time v := by
  obtain ⟨v, -, hv⟩ := (Finset.lt_sup_iff (f := fun v => S.time v + 1)).1 ht
  exact ⟨v, by omega⟩

/-- **A greedy schedule never idles**: every step before the last runs at least one task. A task
that runs last among those not yet run by step `t` has all its predecessors done, so it is ready,
and a greedy step with a ready task is full. -/
theorem Schedule.one_le_load (S : Schedule G p) (hS : S.Greedy) {t : ℕ} (ht : t < S.length) :
    1 ≤ S.load t := by
  by_contra h0
  have hload : S.load t = 0 := by omega
  obtain ⟨w, hw⟩ := S.exists_le_time ht
  obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun v => t ≤ S.time v)
    S.time ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩⟩
  have hvt : t ≤ S.time v := (Finset.mem_filter.1 hv).2
  have hne : S.time v ≠ t := fun h => by
    have : v ∈ Finset.univ.filter fun u => S.time u = t :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
    have := Finset.card_pos.2 ⟨v, this⟩
    unfold Schedule.load at hload
    omega
  have hready : S.Ready t v := by
    refine ⟨by omega, fun u hu => ?_⟩
    by_contra hut
    have := hmin u (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩)
    have := S.prec v u hu
    omega
  have hp := hS t v hready
  have hcap : 1 ≤ p := by
    have h1 := S.cap (S.time v)
    have : 0 < (Finset.univ.filter fun u => S.time u = S.time v).card :=
      Finset.card_pos.2 ⟨v, by simp⟩
    omega
  omega

/-- **The greedy scheduling bound** (the unit-task case of Graham's list-scheduling argument,
Graham, *Bounds for certain multiprocessing anomalies*, Bell System Tech. J. 45, 1966): a greedy
schedule on `p` processors takes `T` steps with `p T ≤ n + (p - 1) D`. Complete steps hold `p`
tasks, the at most `D` incomplete ones at least one each. -/
theorem Schedule.greedy_length_le (S : Schedule G p) (hS : S.Greedy) :
    p * S.length ≤ n + (p - 1) * span G := by
  set I := ((Finset.range S.length).filter fun s => S.load s < p).card
  set C := ((Finset.range S.length).filter fun s => ¬ S.load s < p).card
  have hsplit : I + C = S.length := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.range S.length)
      (p := fun s => S.load s < p)
    rwa [Finset.card_range] at this
  have hI : I ≤ span G := S.incomplete_length_le hS
  -- the work covers `p` per complete step and `1` per incomplete step
  have hwork : p * C + I ≤ n := by
    rw [← S.sum_load, ← Finset.sum_filter_add_sum_filter_not (Finset.range S.length)
      (fun s => S.load s < p)]
    have hc :
        ∑ s ∈ (Finset.range S.length).filter (fun s => ¬ S.load s < p), S.load s = p * C := by
      rw [Finset.sum_const_nat fun s hs => (show S.load s = p by
        have := (Finset.mem_filter.1 hs).2; have := S.load_le s; omega), Nat.mul_comm]
    have hi : I ≤ ∑ s ∈ (Finset.range S.length).filter (fun s => S.load s < p), S.load s :=
      calc I = ∑ s ∈ (Finset.range S.length).filter (fun s => S.load s < p), 1 :=
            Finset.card_eq_sum_ones _
        _ ≤ _ := Finset.sum_le_sum fun s hs =>
            S.one_le_load hS (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)
    omega
  rcases Nat.eq_zero_or_pos p with hp | hp
  · simp [hp]
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have : (q + 1) * S.length = (q + 1) * C + I + q * I := by
      rw [← hsplit, Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.one_mul]
      omega
    have := Nat.mul_le_mul_left q hI
    simp only [Nat.add_sub_cancel]
    omega

/-- **CLRS Theorem 27.1** (third edition): a greedy schedule takes `T ≤ n / p + D` steps,
`p T ≤ n + p D`; a weakening of `greedy_length_le`. -/
theorem Schedule.greedy_length (S : Schedule G p) (hS : S.Greedy) :
    p * S.length ≤ n + p * span G :=
  (S.greedy_length_le hS).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le p 1)) n)

end Cslib.Algorithms.Lean.Parallel.Brent
