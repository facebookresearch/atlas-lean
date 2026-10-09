/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.MinMax
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Nat.Defs

import Init.Data.List.MinMaxIdx

/-!
# Deterministic hiring

The strict-improvement hiring scan from CLRS, fourth edition, Section 5.1,
pages 126-128. A missing manager is below every candidate, including negative
qualities. Ties keep the earlier manager and incur no hiring fee.

The `TimeM` cost is the pair of interview and hire events from this execution.
It is not a claim about comparisons, RAM operations, or bit complexity.
Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

@[no_expose] private def interview {α : Type u} [LinearOrder α]
    (state : Option (α × Nat) × Array Nat) (candidate : α × Nat) :
    TimeM (Nat × Nat) (Option (α × Nat) × Array Nat) := do
  tick (1, 0)
  let winner := List.argAux (fun new old : α × Nat => old.1 < new.1) state.1 candidate
  if winner.map Prod.snd == some candidate.2 then
    tick (0, 1)
    pure (winner, state.2.push candidate.2)
  else
    pure (winner, state.2)

private lemma interview_eq {α : Type u} [LinearOrder α]
    (state : Option (α × Nat) × Array Nat) (candidate : α × Nat) :
    interview state candidate =
      let winner := List.argAux (fun new old : α × Nat => old.1 < new.1) state.1 candidate
      ⟨(winner, if winner.map Prod.snd == some candidate.2 then
          state.2.push candidate.2 else state.2),
        (1, if winner.map Prod.snd == some candidate.2 then 1 else 0)⟩ := by
  dsimp only [interview]
  split <;> rfl

private lemma fold_manager {α : Type u} [LinearOrder α]
    (candidates : List (α × Nat)) (state : Option (α × Nat) × Array Nat) :
    (candidates.foldlM (interview (α := α)) state).ret.1 =
      candidates.foldl (List.argAux (fun new old : α × Nat => old.1 < new.1)) state.1 := by
  induction candidates generalizing state with
  | nil => rfl
  | cons candidate candidates ih =>
      simp only [List.foldlM_cons, ret_bind, ih, List.foldl_cons]
      rw [interview_eq]

private lemma fold_fees {α : Type u} [LinearOrder α]
    (candidates : List (α × Nat)) (state : Option (α × Nat) × Array Nat) :
    (candidates.foldlM (interview (α := α)) state).time.1 = candidates.length ∧
      state.2.size + (candidates.foldlM (interview (α := α)) state).time.2 =
        (candidates.foldlM (interview (α := α)) state).ret.2.size := by
  induction candidates generalizing state with
  | nil => simp
  | cons candidate candidates ih =>
      rw [List.foldlM_cons, interview_eq]
      dsimp only
      split
      · have h := ih (List.argAux (fun new old : α × Nat => old.1 < new.1)
          state.1 candidate, state.2.push candidate.2)
        simp only [time_bind, ret_bind, Prod.fst_add, Prod.snd_add,
          Array.size_push, List.length_cons] at *
        omega
      · have h := ih (List.argAux (fun new old : α × Nat => old.1 < new.1)
          state.1 candidate, state.2)
        simp only [time_bind, ret_bind, Prod.fst_add, Prod.snd_add, List.length_cons] at *
        omega

/-- Interview candidates in order and hire only strict improvements.
The manager and chronological hire indices are zero-based; the fee pair counts
interviews and hires in the same indexed fold. -/
public def hireAssistant {α : Type u} [LinearOrder α] (xs : List α) :
    TimeM (Nat × Nat) (Option Nat × List Nat) :=
  let state : TimeM (Nat × Nat) (Option (α × Nat) × Array Nat) :=
    xs.zipIdx.foldlM (interview (α := α)) (none, #[])
  ⟨(state.ret.1.map Prod.snd, state.ret.2.toList), state.time⟩

private lemma indexed_argmax {α : Type u} [LinearOrder α] (xs : List α)
    (h : xs ≠ []) :
    xs.zipIdx.argmax Prod.fst = some (xs.maxOn id h, xs.maxIdxOn id h) := by
  induction xs using List.reverseRecOn with
  | nil => exact False.elim (h rfl)
  | append_singleton xs a ih =>
      by_cases hx : xs = []
      · subst xs
        simp
      · rw [List.zipIdx_append]
        simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add]
        rw [List.argmax_concat, ih hx]
        dsimp only
        rw [List.maxOn_append hx (by simp), List.maxIdxOn_append hx (by simp)]
        simp only [List.maxOn_singleton, List.maxIdxOn_singleton, id_eq, Nat.add_zero]
        rw [maxOn_eq_max (f := id) Iff.rfl]
        by_cases ha : a ≤ xs.maxOn id hx
        · simp only [ha, not_lt.mpr ha, ite_false, ite_true, max_eq_left ha]
        · simp only [ha, lt_of_not_ge ha, ite_false, ite_true,
            max_eq_right (lt_of_not_ge ha).le]

/-- The returned manager is the canonical earliest maximum index. -/
public theorem hireAssistant_ret {α : Type u} [LinearOrder α] (xs : List α) :
    (hireAssistant xs).ret.1 = xs.maxIdxOn? id := by
  change Option.map Prod.snd
    (xs.zipIdx.foldlM (interview (α := α)) (none, #[])).ret.1 = _
  rw [fold_manager]
  change (xs.zipIdx.argmax Prod.fst).map Prod.snd = _
  by_cases h : xs = []
  · subst xs
    simp
  · rw [indexed_argmax xs h, List.maxIdxOn?_eq_some_maxIdxOn h]
    rfl

private lemma fresh_hire_iff {α : Type u} [LinearOrder α] (xs : List α) (a : α) :
    ((List.argAux (fun new old : α × Nat => old.1 < new.1)
        (xs.zipIdx.argmax Prod.fst) (a, xs.length)).map Prod.snd == some xs.length) = true ↔
      xs.all (fun b => decide (b < a)) = true := by
  by_cases hx : xs = []
  · subst xs
    simp [List.argAux]
  · rw [indexed_argmax xs hx]
    have hi := List.maxIdxOn_lt_length (f := id) hx
    have hm : xs.maxOn id hx < a ↔ ∀ b ∈ xs, b < a := by
      constructor
      · intro ha b hb
        have hb' : b ≤ xs.maxOn id hx := by
          simpa only [List.maxOn_id] using List.le_max_of_mem hb
        exact lt_of_le_of_lt hb' ha
      · intro ha
        exact ha _ List.maxOn_mem
    simp only [List.argAux, hm, List.all_eq_true, decide_eq_true_eq]
    split <;> simp_all [Nat.ne_of_lt hi]

private def records {α : Type u} [LinearOrder α] (xs : List α) : List Nat :=
  (xs.zipIdx.filter (fun p => (xs.take p.2).all (fun a => decide (a < p.1)))).map Prod.snd

private lemma records_append {α : Type u} [LinearOrder α] (xs : List α) (a : α) :
    records (xs ++ [a]) = records xs ++
      if xs.all (fun b => decide (b < a)) then [xs.length] else [] := by
  have hfilter :
      xs.zipIdx.filter (fun p => ((xs ++ [a]).take p.2).all (fun b => decide (b < p.1))) =
        xs.zipIdx.filter (fun p => (xs.take p.2).all (fun b => decide (b < p.1))) := by
    apply List.filter_congr
    intro p hp
    have hi : p.2 < xs.length := by simpa using List.snd_lt_of_mem_zipIdx hp
    rw [List.take_append_of_le_length hi.le]
  simp only [records, List.zipIdx_append, List.zipIdx_cons, List.zipIdx_nil,
    Nat.zero_add, List.filter_append, hfilter, List.map_append]
  simp only [List.filter_cons, List.filter_nil]
  rw [List.take_append_of_le_length (Nat.le_refl xs.length), List.take_length]
  split <;> simp_all

private lemma fold_history {α : Type u} [LinearOrder α] (xs : List α) :
    (xs.zipIdx.foldlM (interview (α := α)) (none, #[])).ret.2.toList = records xs := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs a ih =>
      rw [List.zipIdx_append, List.foldlM_append]
      simp only [Nat.zero_add, List.zipIdx_cons, List.zipIdx_nil, List.foldlM_cons,
        List.foldlM_nil, ret_bind, ret_pure]
      rw [interview_eq]
      dsimp only
      rw [fold_manager]
      change (if ((List.argAux (fun new old : α × Nat => old.1 < new.1)
          (xs.zipIdx.argmax Prod.fst) (a, xs.length)).map Prod.snd == some xs.length)
          then (xs.zipIdx.foldlM (interview (α := α)) (none, #[])).ret.2.push xs.length
          else (xs.zipIdx.foldlM (interview (α := α)) (none, #[])).ret.2).toList = _
      rw [records_append]
      by_cases h : xs.all (fun b => decide (b < a)) = true
      · have hc := (fresh_hire_iff xs a).mpr h
        simp only [hc, h, ite_true, Array.toList_push, ih]
      · have hc := mt (fresh_hire_iff xs a).mp h
        simp [hc, h, ih]

/-- The actual chronological history consists exactly of strict prefix records. -/
public theorem hireAssistant_hires {α : Type u} [LinearOrder α] (xs : List α) :
    (hireAssistant xs).ret.2 =
      (xs.zipIdx.filter (fun p => (xs.take p.2).all (fun a => decide (a < p.1)))).map
        Prod.snd := by
  exact fold_history xs

/-- The fee pair counts interviews and the actual chronological hiring history. -/
public theorem hireAssistant_time {α : Type u} [LinearOrder α] (xs : List α) :
    (hireAssistant xs).time = (xs.length, (hireAssistant xs).ret.2.length) := by
  have h := fold_fees xs.zipIdx (none, #[])
  simpa [hireAssistant, Prod.ext_iff] using h

/-- Empty input interviews and hires nobody and returns no manager. -/
public theorem hireAssistant_nil {α : Type u} [LinearOrder α] :
    hireAssistant ([] : List α) = ⟨(none, []), (0, 0)⟩ := by
  simp [hireAssistant]
  rfl

/-- The first candidate is hired regardless of its quality. -/
public theorem hireAssistant_singleton {α : Type u} [LinearOrder α] (a : α) :
    hireAssistant [a] = ⟨(some 0, [0]), (1, 1)⟩ := by
  simp [hireAssistant, List.zipIdx, List.foldlM, interview_eq, List.argAux]

/-- A nonempty input makes at least one hire and at most one per interview. -/
public theorem hireAssistant_hire_bounds {α : Type u} [LinearOrder α] (xs : List α)
    (h : xs ≠ []) :
    1 ≤ (hireAssistant xs).time.2 ∧ (hireAssistant xs).time.2 ≤ xs.length := by
  rw [hireAssistant_time, hireAssistant_hires]
  constructor
  · cases xs with
    | nil => exact False.elim (h rfl)
    | cons a xs =>
        simp only [List.zipIdx_cons, List.filter_cons, List.take_zero,
          List.all_nil, ite_true, List.map_cons, List.length_cons]
        omega
  · simpa only [List.length_map, List.length_zipIdx] using
      List.length_filter_le
        (fun p : α × Nat => (xs.take p.2).all (fun a => decide (a < p.1))) xs.zipIdx

private lemma increasing_records {α : Type u} [LinearOrder α] (xs : List α)
    (h : xs.Pairwise (· < ·)) : records xs = List.range xs.length := by
  have hf : xs.zipIdx.filter
      (fun p => (xs.take p.2).all (fun a => decide (a < p.1))) = xs.zipIdx := by
    apply List.filter_eq_self.mpr
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    simp only [List.getElem_zipIdx, Nat.zero_add]
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨j, hj, hb⟩ := List.mem_iff_getElem.mp hb
    have hj' : j < min i xs.length := by simpa only [List.length_take] using hj
    have hji : j < i := lt_of_lt_of_le hj' (Nat.min_le_left _ _)
    have hjxs : j < xs.length := lt_of_lt_of_le hj' (Nat.min_le_right _ _)
    have hb' : xs[j] = b := by simpa only [List.getElem_take] using hb
    simpa only [decide_eq_true_eq, ← hb'] using
      (List.pairwise_iff_getElem.mp h j i hjxs (by simpa using hi) hji)
  rw [records, hf]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

/-- Every candidate in a strictly increasing input is hired, including empty input. -/
public theorem hireAssistant_increasing {α : Type u} [LinearOrder α] (xs : List α)
    (h : xs.Pairwise (· < ·)) :
    (hireAssistant xs).ret.2 = List.range xs.length ∧
      (hireAssistant xs).time = (xs.length, xs.length) := by
  have hr : (hireAssistant xs).ret.2 = List.range xs.length := by
    rw [hireAssistant_hires]
    exact increasing_records xs h
  exact ⟨hr, by rw [hireAssistant_time, hr, List.length_range]⟩

end Cslib.Algorithms.Lean.TimeM
