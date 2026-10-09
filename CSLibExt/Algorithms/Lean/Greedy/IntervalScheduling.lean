/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Cslib.Algorithms.Lean.Sort.Merge
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.Nat.Log

import all Cslib.Algorithms.Lean.MergeSort.MergeSort
import all Cslib.Algorithms.Lean.Sort.Merge
import all Init.Data.List.Sort.Basic
import Mathlib.Data.List.Sort

/-!
# Unweighted interval scheduling

Activities occupy closed-open intervals, so touching endpoints are compatible.
`intervalSchedule` sorts arbitrary input by finish time using CSLib's merge sort,
then selects each activity starting after the last selected finish.

The cost counts one comparison per finish comparison in the sort and one start/finish
comparison per scan candidate after the first. Endpoint projection and list operations are free.
The input is converted to an array once per sort so indexed payload access during comparison and
recovery is constant-time and remains outside the abstract comparison count.

The activity-selection source is CLRS, *Introduction to Algorithms*, fourth edition,
section 15.1. Endpoint types are generalized to linear orders and list subpermutations preserve
activity occurrences. Optimality requires strictly positive duration.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u v

variable {ι : Type u} {τ : Type v} [LinearOrder τ]

/-- Two closed-open activities are compatible when one finishes before the other starts. -/
def IntervalCompatible (start finish : ι → τ) (a b : ι) : Prop :=
  finish a ≤ start b ∨ finish b ≤ start a

/-- Compatibility is symmetric. -/
theorem IntervalCompatible.symm {start finish : ι → τ} {a b : ι}
    (h : IntervalCompatible start finish a b) : IntervalCompatible start finish b a :=
  Or.symm h

/-- An earliest-finish schedule, obtained by sorting by finish time and scanning once. -/
def intervalSchedule (start finish : ι → τ) (xs : List ι) : TimeM Nat (List ι) :=
  let rec scan (lastFinish : τ) : List ι → TimeM Nat (List ι)
    | [] => pure []
    | a :: rest => do
      ✓ if lastFinish ≤ start a then
        return a :: (← scan (finish a) rest)
      else
        scan lastFinish rest
  let values := xs.toArray
  let indices : TimeM Nat (List (Fin values.size)) :=
    List.mergeSortM (List.finRange values.size) (fun a b =>
      (⟨decide (finish values[a] ≤ finish values[b]), 1⟩ : TimeM Nat Bool))
  -- CSLib's monadic sort is universe-zero; sort array indices, then recover their payloads.
  let sorted := indices.ret.map fun i => values[i]
  let selection : TimeM Nat (List ι) :=
    match sorted with
    | [] => pure []
    | a :: rest => do return a :: (← scan (finish a) rest)
  ⟨selection.ret, indices.time + selection.time⟩

private def scanFrom (start finish : ι → τ) (lastFinish : τ) : List ι → TimeM Nat (List ι)
  | [] => pure []
  | a :: xs => do
    ✓ if lastFinish ≤ start a then
      return a :: (← scanFrom start finish (finish a) xs)
    else
      scanFrom start finish lastFinish xs

private theorem scan_time (start finish : ι → τ) (xs : List ι) (lastFinish : τ) :
    (scanFrom start finish lastFinish xs).time = xs.length := by
  induction xs generalizing lastFinish with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : lastFinish ≤ start a <;> simp [scanFrom, h, ih, Nat.add_comm]

private theorem scan_sublist (start finish : ι → τ) (xs : List ι) (lastFinish : τ) :
    (scanFrom start finish lastFinish xs).ret.Sublist xs := by
  induction xs generalizing lastFinish with
  | nil => exact List.Sublist.refl _
  | cons a xs ih =>
    by_cases h : lastFinish ≤ start a
    · simpa [scanFrom, h] using (ih (finish a)).cons_cons a
    · simpa [scanFrom, h] using (ih lastFinish).cons a

private theorem scan_lower (start finish : ι → τ) (xs : List ι) (lastFinish : τ)
    (hproper : ∀ a ∈ xs, start a < finish a) :
    ∀ a ∈ (scanFrom start finish lastFinish xs).ret, lastFinish ≤ start a := by
  induction xs generalizing lastFinish with
  | nil => simp [scanFrom]
  | cons a xs ih =>
    have ha := hproper a (by simp)
    have htail : ∀ b ∈ xs, start b < finish b := fun b hb => hproper b (by simp [hb])
    by_cases h : lastFinish ≤ start a
    · simp only [scanFrom, h, ↓reduceIte, ret_bind, ret_pure, List.mem_cons]
      intro b hb
      rcases hb with rfl | hb
      · exact h
      · exact le_trans (le_trans h ha.le) (ih (finish a) htail b hb)
    · simpa [scanFrom, h] using ih lastFinish htail

private theorem scan_feasible (start finish : ι → τ) (xs : List ι) (lastFinish : τ)
    (hproper : ∀ a ∈ xs, start a < finish a) :
    List.Pairwise (IntervalCompatible start finish) (scanFrom start finish lastFinish xs).ret := by
  induction xs generalizing lastFinish with
  | nil => simp [scanFrom]
  | cons a xs ih =>
    have htail : ∀ b ∈ xs, start b < finish b := fun b hb => hproper b (by simp [hb])
    by_cases h : lastFinish ≤ start a
    · simp only [scanFrom, h, ↓reduceIte, ret_bind, ret_pure]
      exact List.pairwise_cons.mpr
        ⟨fun b hb => Or.inl (scan_lower start finish xs (finish a) htail b hb),
          ih (finish a) htail⟩
    · simpa [scanFrom, h] using ih lastFinish htail

private def sortFinish (finish : ι → τ) (xs : List ι) : TimeM Nat (List ι) :=
  let values := xs.toArray
  let indices : TimeM Nat (List (Fin values.size)) :=
    List.mergeSortM (List.finRange values.size) (fun a b =>
      (⟨decide (finish values[a] ≤ finish values[b]), 1⟩ : TimeM Nat Bool))
  ⟨indices.ret.map fun i => values[i], indices.time⟩

private theorem sortFinish_perm (finish : ι → τ) (xs : List ι) :
    (sortFinish finish xs).ret.Perm xs := by
  simp only [sortFinish, ret_mergeSortM]
  have hrecover :
      (List.finRange xs.toArray.size).map (fun i => xs.toArray[i]) = xs :=
    List.map_get_finRange xs
  simpa only [hrecover] using
    (List.mergeSort_perm (List.finRange xs.toArray.size)
      (fun a b => decide (finish xs.toArray[a] ≤ finish xs.toArray[b]))).map
        (fun i => xs.toArray[i])

private theorem sortFinish_sorted (finish : ι → τ) (xs : List ι) :
    List.Pairwise (fun a b => finish a ≤ finish b) (sortFinish finish xs).ret := by
  simp only [sortFinish, ret_mergeSortM, List.pairwise_map]
  have hs := List.pairwise_mergeSort
    (le := fun a b : Fin xs.toArray.size =>
      decide (finish xs.toArray[a] ≤ finish xs.toArray[b]))
    (fun a b c hab hbc => by
      simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
    (fun a b => by
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using
        le_total (finish xs.toArray[a]) (finish xs.toArray[b]))
    (List.finRange xs.toArray.size)
  simpa using hs

private theorem chronological (start finish : ι → τ) (xs : List ι)
    (hproper : ∀ a ∈ xs, start a < finish a)
    (hsorted : List.Pairwise (fun a b => finish a ≤ finish b) xs)
    (hcompatible : List.Pairwise (IntervalCompatible start finish) xs) :
    List.Pairwise (fun a b => finish a ≤ start b) xs := by
  apply List.Pairwise.imp_of_mem _ (hsorted.and hcompatible)
  intro a b ha hb h
  rcases h.2 with hab | hba
  · exact hab
  · exact False.elim ((not_le_of_gt (hproper a ha)) (le_trans h.1 hba))

private theorem remove_rejected (start : ι → τ) (lastFinish : τ) (a : ι) (xs ys : List ι)
    (ha : ¬lastFinish ≤ start a) (hsub : ys.Subperm (a :: xs))
    (hadmit : ∀ b ∈ ys, lastFinish ≤ start b) : ys.Subperm xs := by
  -- Filtering removes the rejected occurrence without requiring equality on activities.
  let p : ι → Bool := fun b => decide (lastFinish ≤ start b)
  have hself : ys.filter p = ys := List.filter_eq_self.mpr fun b hb => by
    simpa [p] using hadmit b hb
  have hfilter : ys.Subperm (xs.filter p) := by
    simpa [hself, p, ha] using hsub.filter p
  exact hfilter.trans List.filter_sublist.subperm

private theorem remove_first (start finish : ι → τ) (a b : ι) (xs ys : List ι)
    (ha : start a < finish a) (hfinish : finish a ≤ finish b)
    (hsub : (b :: ys).Subperm (a :: xs))
    (hchron : List.Pairwise (fun x y => finish x ≤ start y) (b :: ys)) :
    ys.Subperm xs ∧ ∀ c ∈ ys, finish a ≤ start c := by
  have hadmit : ∀ c ∈ ys, finish a ≤ start c :=
    fun c hc => le_trans hfinish (List.rel_of_pairwise_cons hchron hc)
  have hsubtail := (List.sublist_cons_self b ys).subperm.trans hsub
  have hres := remove_rejected start (finish a) a xs ys (not_le_of_gt ha) hsubtail hadmit
  exact ⟨hres, hadmit⟩

private theorem scan_optimal (start finish : ι → τ) (xs : List ι)
    (hproper : ∀ a ∈ xs, start a < finish a)
    (hsorted : List.Pairwise (fun a b => finish a ≤ finish b) xs)
    (lastFinish : τ) (ys : List ι) (hsub : ys.Subperm xs)
    (hcompatible : List.Pairwise (IntervalCompatible start finish) ys)
    (hadmit : ∀ a ∈ ys, lastFinish ≤ start a) :
    ys.length ≤ (scanFrom start finish lastFinish xs).ret.length := by
  induction xs generalizing lastFinish ys with
  | nil => simp [List.subperm_nil.mp hsub, scanFrom]
  | cons a xs ih =>
    have ha := hproper a (by simp)
    have hp : ∀ b ∈ xs, start b < finish b := fun b hb => hproper b (by simp [hb])
    have hs := List.Pairwise.of_cons hsorted
    by_cases h : lastFinish ≤ start a
    · simp only [scanFrom, h, ↓reduceIte, ret_bind, ret_pure, List.length_cons]
      let zs := (sortFinish finish ys).ret
      have hperm : zs.Perm ys := sortFinish_perm finish ys
      have hzsub : zs.Subperm (a :: xs) := hperm.subperm.trans hsub
      have hzproper : ∀ b ∈ zs, start b < finish b :=
        fun b hb => hproper b (hzsub.subset hb)
      have hzcompatible : List.Pairwise (IntervalCompatible start finish) zs :=
        hperm.symm.pairwise hcompatible (fun h => h.symm)
      have hzchron := chronological start finish zs hzproper
        (sortFinish_sorted finish ys) hzcompatible
      have hzlength : zs.length = ys.length := hperm.length_eq
      cases hz : zs with
      | nil => simp [hz] at hzlength; omega
      | cons b bs =>
        have hab : finish a ≤ finish b := by
          have hb : b ∈ a :: xs := hzsub.subset (by simp [hz])
          rcases List.mem_cons.mp hb with rfl | hb
          · exact le_rfl
          · exact List.rel_of_pairwise_cons hsorted hb
        have hres := remove_first start finish a b xs bs ha hab
          (by simpa [hz] using hzsub) (by simpa [hz] using hzchron)
        have hbscompatible : List.Pairwise (IntervalCompatible start finish) bs := by
          simpa [hz] using hzcompatible.tail
        have hi := ih hp hs (finish a) bs hres.1 hbscompatible hres.2
        simp [hz] at hzlength
        omega
    · simp only [scanFrom, h, ↓reduceIte, ret_bind]
      exact ih hp hs lastFinish ys (remove_rejected start lastFinish a xs ys h hsub hadmit)
        hcompatible hadmit

private def selectSorted (start finish : ι → τ) : List ι → TimeM Nat (List ι)
  | [] => pure []
  | a :: xs => do return a :: (← scanFrom start finish (finish a) xs)

private theorem selection_optimal (start finish : ι → τ) (xs : List ι)
    (hproper : ∀ a ∈ xs, start a < finish a)
    (hsorted : List.Pairwise (fun a b => finish a ≤ finish b) xs)
    (ys : List ι) (hsub : ys.Subperm xs)
    (hcompatible : List.Pairwise (IntervalCompatible start finish) ys) :
    ys.length ≤ (selectSorted start finish xs).ret.length := by
  cases xs with
  | nil => simp [List.subperm_nil.mp hsub, selectSorted]
  | cons a xs =>
    simp only [selectSorted, ret_bind, ret_pure, List.length_cons]
    let zs := (sortFinish finish ys).ret
    have hperm : zs.Perm ys := sortFinish_perm finish ys
    have hzsub : zs.Subperm (a :: xs) := hperm.subperm.trans hsub
    have hzproper : ∀ b ∈ zs, start b < finish b :=
      fun b hb => hproper b (hzsub.subset hb)
    have hzcompatible : List.Pairwise (IntervalCompatible start finish) zs :=
      hperm.symm.pairwise hcompatible (fun h => h.symm)
    have hzchron := chronological start finish zs hzproper
      (sortFinish_sorted finish ys) hzcompatible
    have hzlength : zs.length = ys.length := hperm.length_eq
    cases hz : zs with
    | nil => simp [hz] at hzlength; omega
    | cons b bs =>
      have hab : finish a ≤ finish b := by
        have hb : b ∈ a :: xs := hzsub.subset (by simp [hz])
        rcases List.mem_cons.mp hb with rfl | hb
        · exact le_rfl
        · exact List.rel_of_pairwise_cons hsorted hb
      have ha := hproper a (by simp)
      have hp : ∀ c ∈ xs, start c < finish c := fun c hc => hproper c (by simp [hc])
      have hres := remove_first start finish a b xs bs ha hab
        (by simpa [hz] using hzsub) (by simpa [hz] using hzchron)
      have hbscompatible : List.Pairwise (IntervalCompatible start finish) bs := by
        simpa [hz] using hzcompatible.tail
      have hi := scan_optimal start finish xs hp hsorted.tail (finish a) bs
        hres.1 hbscompatible hres.2
      simp [hz] at hzlength
      omega

private theorem selection_correct (start finish : ι → τ) (xs : List ι)
    (hproper : ∀ a ∈ xs, start a < finish a)
    (hsorted : List.Pairwise (fun a b => finish a ≤ finish b) xs) :
    (selectSorted start finish xs).ret.Subperm xs ∧
      List.Pairwise (IntervalCompatible start finish) (selectSorted start finish xs).ret ∧
      ∀ ys, ys.Subperm xs → List.Pairwise (IntervalCompatible start finish) ys →
        ys.length ≤ (selectSorted start finish xs).ret.length := by
  refine ⟨?_, ?_, selection_optimal start finish xs hproper hsorted⟩
  · cases xs with
    | nil => exact List.Subperm.refl _
    | cons a xs =>
      simpa [selectSorted] using (scan_sublist start finish xs (finish a)).cons_cons a |>.subperm
  · cases xs with
    | nil => simp [selectSorted]
    | cons a xs =>
      have hp : ∀ b ∈ xs, start b < finish b := fun b hb => hproper b (by simp [hb])
      simp only [selectSorted, ret_bind, ret_pure]
      exact List.pairwise_cons.mpr
        ⟨fun b hb => Or.inl (scan_lower start finish xs (finish a) hp b hb),
          scan_feasible start finish xs (finish a) hp⟩

private theorem selection_time (start finish : ι → τ) (xs : List ι) :
    (selectSorted start finish xs).time = xs.length - 1 := by
  cases xs <;> simp [selectSorted, scan_time]

private theorem generic_merge_time {α : Type} (xs ys : List α) (cmp : α → α → Bool) :
    (List.mergeM xs ys (fun a b => (⟨cmp a b, 1⟩ : TimeM Nat Bool))).time ≤
      xs.length + ys.length := by
  fun_induction List.mergeM with grind

private theorem mergeSortRec_succ_succ (n : Nat) : timeMergeSortRec (n + 2) =
    timeMergeSortRec ((n + 2) / 2) + timeMergeSortRec ((n + 1) / 2 + 1) + (n + 2) := by
  -- The pinned CSLib module does not export this generated recurrence equation.
  unfold timeMergeSortRec
  rw [WellFounded.Nat.fix_eq]
  congr 2

private theorem generic_mergeSort_time {α : Type} (xs : List α) (cmp : α → α → Bool) :
    (List.mergeSortM xs (fun a b => (⟨cmp a b, 1⟩ : TimeM Nat Bool))).time ≤
      timeMergeSortRec xs.length := by
  fun_induction List.mergeSortM with
  | case1 | case2 => grind [timeMergeSortRec]
  | case3 _ _ _ _ ih2 ih1 =>
    simp only [time_bind]
    grw [generic_merge_time]
    simp only [ret_mergeSortM, List.length_mergeSort]
    simp only [List.length_cons]
    rw [mergeSortRec_succ_succ]
    grind

private theorem sortFinish_time (finish : ι → τ) (xs : List ι) :
    (sortFinish finish xs).time ≤ xs.length * Nat.clog 2 xs.length := by
  have h := generic_mergeSort_time (List.finRange xs.toArray.size)
    (fun a b => decide (finish xs.toArray[a] ≤ finish xs.toArray[b]))
  have hsize : xs.toArray.size = xs.length := by rfl
  have hcost : (sortFinish finish xs).time ≤ timeMergeSortRec xs.length := by
    simpa only [sortFinish, List.length_finRange, hsize] using h
  exact hcost.trans (timeMergeSortRec_le xs.length)

private theorem intervalSchedule_scan_eq (start finish : ι → τ) (xs : List ι)
    (lastFinish : τ) :
    intervalSchedule.scan start finish lastFinish xs = scanFrom start finish lastFinish xs := by
  induction xs generalizing lastFinish with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : lastFinish ≤ start a <;> simp [intervalSchedule.scan, scanFrom, h, ih]

private theorem intervalSchedule_eq (start finish : ι → τ) (xs : List ι) :
    intervalSchedule start finish xs =
      ⟨(selectSorted start finish (sortFinish finish xs).ret).ret,
        (sortFinish finish xs).time +
          (selectSorted start finish (sortFinish finish xs).ret).time⟩ := by
  unfold intervalSchedule sortFinish
  simp only [intervalSchedule_scan_eq]
  rfl

/-- The output preserves input occurrences, is feasible, and has maximum cardinality
among all feasible subpermutations of the input. Strictly positive durations are required. -/
theorem intervalSchedule_correct (start finish : ι → τ) (xs : List ι)
    (hproper : ∀ a ∈ xs, start a < finish a) :
    (intervalSchedule start finish xs).ret.Subperm xs ∧
      List.Pairwise (IntervalCompatible start finish) (intervalSchedule start finish xs).ret ∧
      ∀ ys, ys.Subperm xs → List.Pairwise (IntervalCompatible start finish) ys →
        ys.length ≤ (intervalSchedule start finish xs).ret.length := by
  rw [intervalSchedule_eq]
  have hperm := sortFinish_perm finish xs
  have hp : ∀ a ∈ (sortFinish finish xs).ret, start a < finish a :=
    fun a ha => hproper a (hperm.subset ha)
  have hc := selection_correct start finish (sortFinish finish xs).ret hp
    (sortFinish_sorted finish xs)
  exact ⟨hc.1.trans hperm.subperm, hc.2.1,
    fun ys hsub hcompatible => hc.2.2 ys (hsub.trans hperm.symm.subperm) hcompatible⟩

/-- At most `n * ⌈log₂ n⌉ + (n - 1)` comparisons are charged for `n` input occurrences. -/
theorem intervalSchedule_time (start finish : ι → τ) (xs : List ι) :
    (intervalSchedule start finish xs).time ≤
      xs.length * Nat.clog 2 xs.length + (xs.length - 1) := by
  rw [intervalSchedule_eq]
  simpa only [selection_time, (sortFinish_perm finish xs).length_eq] using
    Nat.add_le_add_right (sortFinish_time finish xs)
      ((selectSorted start finish (sortFinish finish xs).ret).time)

end Cslib.Algorithms.Lean.TimeM
