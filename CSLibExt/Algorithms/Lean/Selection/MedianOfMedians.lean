/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Selection.MedianOfMedians.Groups
public import CSLibExt.Algorithms.Lean.Selection.MedianOfMedians.Discard
public import CSLibExt.Algorithms.Lean.Selection.Quickselect
public import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Basic

/-!
# Median-of-medians selection

This module formalizes selection from MIT 6.046J, Spring 2015, Lecture 2,
pages 4 and 5. Ranks are zero based; three-way partitioning retains duplicates.
The bounded base case reuses deterministic quickselect, and larger inputs use
recursive medians of groups of five.

One `TimeM` tick counts one order comparison. The actual comparison counter is
at most eighty times the input length. List construction, rank checks and
recursion are free in this model; no machine-time or workspace bound is claimed.
-/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

/-- Select using recursive group-median pivots and a bounded quickselect base case. -/
def medianOfMedians {α : Type u} [LinearOrder α] (xs : List α) (k : Nat) :
    TimeM Nat (Option α) :=
  let rec loop : Nat → List α → Nat → TimeM Nat (Option α)
    | 0, _, _ => pure none
    | fuel + 1, ys, rank =>
        if ys.length ≤ 140 then quickselect ys rank else do
          let medians ← medianOfMediansGroups ys
          let pivot ← loop fuel medians (medians.length / 2)
          match pivot with
          | none => pure none
          | some x => do
              let parts ← partition3 x ys
              if rank < parts.below.length then
                loop fuel parts.below rank
              else if rank < parts.below.length + parts.equal.length then
                pure (some x)
              else
                loop fuel parts.above (rank - (parts.below.length + parts.equal.length))
  if k < xs.length then loop xs.length xs k else pure none

/-- Inputs in the fixed base range use the canonical timed quickselect exactly. -/
theorem medianOfMedians_eq_quickselect_of_length_le {α : Type u} [LinearOrder α]
    (xs : List α) (k : Nat) (hlen : xs.length ≤ 140) :
    medianOfMedians xs k = quickselect xs k := by
  cases xs with
  | nil => simp [medianOfMedians, quickselect]
  | cons x xs =>
      have hlen' : xs.length + 1 ≤ 140 := by simpa using hlen
      by_cases hk : k < xs.length + 1
      · simp [medianOfMedians, medianOfMedians.loop, hk, hlen']
      · simp [medianOfMedians, quickselect, hk]

/-- An out-of-range rank returns immediately with zero comparison charges. -/
theorem medianOfMedians_eq_pure_none_of_length_le_rank {α : Type u} [LinearOrder α]
    (xs : List α) (k : Nat) (hk : xs.length ≤ k) :
    medianOfMedians xs k = pure none := by
  simp [medianOfMedians, Nat.not_lt.mpr hk]

/-- The fixed base range fits the final eighty-comparisons-per-occurrence budget. -/
theorem medianOfMedians_base_time {α : Type u} [LinearOrder α]
    (xs : List α) (k : Nat) (hlen : xs.length ≤ 140) :
    (medianOfMedians xs k).time ≤ 80 * xs.length := by
  rw [medianOfMedians_eq_quickselect_of_length_le xs k hlen]
  have hcost := quickselect_time xs k
  have hsub : xs.length - 1 ≤ 139 := by omega
  have hmul := Nat.mul_le_mul_left xs.length hsub
  omega

/-- Successful base-case selection satisfies the duplicate-safe rank specification. -/
theorem medianOfMedians_base_correct {α : Type u} [LinearOrder α]
    {xs : List α} {k : Nat} {x : α} (hlen : xs.length ≤ 140)
    (hresult : (medianOfMedians xs k).ret = some x) :
    x ∈ xs ∧ xs.countP (fun y => decide (y < x)) ≤ k ∧
      k < xs.countP (fun y => decide (y ≤ x)) := by
  rw [medianOfMedians_eq_quickselect_of_length_le xs k hlen] at hresult
  exact quickselect_correct hresult

private theorem medianOfMedians_below_rank {α : Type u} [LinearOrder α]
    (pivot : α) (xs : List α) (k : Nat) (x : α)
    (hx : x ∈ (partition3 pivot xs).ret.below ∧
      (partition3 pivot xs).ret.below.countP (fun y => decide (y < x)) ≤ k ∧
      k < (partition3 pivot xs).ret.below.countP (fun y => decide (y ≤ x))) :
    x ∈ xs ∧ xs.countP (fun y => decide (y < x)) ≤ k ∧
      k < xs.countP (fun y => decide (y ≤ x)) := by
  have hparts := partition3_correct pivot xs
  have hxp := hparts.2.1 x hx.1
  have hlt := partition3_countP_eq_below pivot xs (fun y => decide (y < x))
    (fun y hy => by simp [hparts.2.2.1 y hy, not_lt_of_ge hxp.le])
    (fun y hy => by
      have hxy : x ≤ y := le_trans hxp.le (hparts.2.2.2 y hy).le
      simp [not_lt_of_ge hxy])
  have hle := partition3_countP_eq_below pivot xs (fun y => decide (y ≤ x))
    (fun y hy => by simp [hparts.2.2.1 y hy, not_le_of_gt hxp])
    (fun y hy => by
      have hxy : x < y := lt_trans hxp (hparts.2.2.2 y hy)
      simp [not_le_of_gt hxy])
  refine ⟨hparts.1.mem_iff.mp (by simp [hx.1]), ?_, ?_⟩
  · rw [hlt]
    exact hx.2.1
  · rw [hle]
    exact hx.2.2

private theorem medianOfMedians_above_rank {α : Type u} [LinearOrder α]
    (pivot : α) (xs : List α) (k : Nat) (x : α)
    (hk : (partition3 pivot xs).ret.below.length +
      (partition3 pivot xs).ret.equal.length ≤ k)
    (hx : x ∈ (partition3 pivot xs).ret.above ∧
      (partition3 pivot xs).ret.above.countP (fun y => decide (y < x)) ≤
        k - ((partition3 pivot xs).ret.below.length + (partition3 pivot xs).ret.equal.length) ∧
      k - ((partition3 pivot xs).ret.below.length + (partition3 pivot xs).ret.equal.length) <
        (partition3 pivot xs).ret.above.countP (fun y => decide (y ≤ x))) :
    x ∈ xs ∧ xs.countP (fun y => decide (y < x)) ≤ k ∧
      k < xs.countP (fun y => decide (y ≤ x)) := by
  have hparts := partition3_correct pivot xs
  have hpx := hparts.2.2.2 x hx.1
  have hlt := partition3_countP_eq_block_add_above pivot xs (fun y => decide (y < x))
    (fun y hy => by simp [(hparts.2.1 y hy).trans hpx])
    (fun y hy => by simp [hparts.2.2.1 y hy, hpx])
  have hle := partition3_countP_eq_block_add_above pivot xs (fun y => decide (y ≤ x))
    (fun y hy => by simp [((hparts.2.1 y hy).trans hpx).le])
    (fun y hy => by simp [hparts.2.2.1 y hy, hpx.le])
  refine ⟨hparts.1.mem_iff.mp (by simp [hx.1]), ?_, ?_⟩
  · omega
  · omega

private theorem medianOfMedians_equal_rank {α : Type u} [LinearOrder α]
    (pivot : α) (xs : List α) (k : Nat) (hpivot : pivot ∈ xs)
    (hbelow : (partition3 pivot xs).ret.below.length ≤ k)
    (hequal : k < (partition3 pivot xs).ret.below.length +
      (partition3 pivot xs).ret.equal.length) :
    pivot ∈ xs ∧ xs.countP (fun y => decide (y < pivot)) ≤ k ∧
      k < xs.countP (fun y => decide (y ≤ pivot)) := by
  refine ⟨hpivot, ?_, ?_⟩
  · rw [partition3_count_lt]
    exact hbelow
  · rw [partition3_count_le]
    exact hequal

private theorem medianOfMedians_loop_correct_step {α : Type u} [LinearOrder α]
    (fuel : Nat)
    (hrec : ∀ (ys : List α) (rank : Nat) (y : α),
      (medianOfMedians.loop fuel ys rank).ret = some y →
      y ∈ ys ∧ ys.countP (fun z => decide (z < y)) ≤ rank ∧
        rank < ys.countP (fun z => decide (z ≤ y)))
    (xs : List α) (k : Nat) (x : α)
    (hresult : (medianOfMedians.loop (fuel + 1) xs k).ret = some x) :
    x ∈ xs ∧ xs.countP (fun y => decide (y < x)) ≤ k ∧
      k < xs.countP (fun y => decide (y ≤ x)) := by
  by_cases hbase : xs.length ≤ 140
  · simp only [medianOfMedians.loop, ite_eq_left hbase] at hresult
    exact quickselect_correct hresult
  · simp only [medianOfMedians.loop, ite_eq_right hbase, ret_bind] at hresult
    split at hresult
    · simp only [ret_pure] at hresult
      cases hresult
    · rename_i pivot hpivot
      have hpinput := medianOfMediansGroups_mem (hrec _ _ _ hpivot).1
      simp only [ret_bind] at hresult
      by_cases hbelow : k < (partition3 pivot xs).ret.below.length
      · simp only [ite_eq_left hbelow] at hresult
        exact medianOfMedians_below_rank pivot xs k x (hrec _ _ _ hresult)
      · simp only [ite_eq_right hbelow] at hresult
        by_cases hequal : k < (partition3 pivot xs).ret.below.length +
            (partition3 pivot xs).ret.equal.length
        · simp only [ite_eq_left hequal, ret_pure, Option.some.injEq] at hresult
          subst x
          exact medianOfMedians_equal_rank pivot xs k hpinput (by omega) hequal
        · simp only [ite_eq_right hequal] at hresult
          exact medianOfMedians_above_rank pivot xs k x (by omega) (hrec _ _ _ hresult)

private theorem medianOfMedians_loop_correct {α : Type u} [LinearOrder α] (fuel : Nat) :
    ∀ (xs : List α) (k : Nat) (x : α),
      (medianOfMedians.loop fuel xs k).ret = some x →
      x ∈ xs ∧ xs.countP (fun y => decide (y < x)) ≤ k ∧
        k < xs.countP (fun y => decide (y ≤ x)) := by
  induction fuel with
  | zero =>
      intro xs k x hresult
      simp [medianOfMedians.loop] at hresult
  | succ fuel ih =>
      intro xs k x hresult
      exact medianOfMedians_loop_correct_step fuel ih xs k x hresult

/-- Every successful return satisfies the rank specification, including duplicates. -/
theorem medianOfMedians_correct {α : Type u} [LinearOrder α]
    {xs : List α} {k : Nat} {x : α} (hresult : (medianOfMedians xs k).ret = some x) :
    x ∈ xs ∧ xs.countP (fun y => decide (y < x)) ≤ k ∧
      k < xs.countP (fun y => decide (y ≤ x)) := by
  by_cases hk : k < xs.length
  · simp only [medianOfMedians, ite_eq_left hk] at hresult
    exact medianOfMedians_loop_correct xs.length xs k x hresult
  · simp [medianOfMedians, hk] at hresult

private theorem medianOfMedians_partition_length_lt {α : Type u} [LinearOrder α]
    (pivot : α) (xs : List α) (hpivot : pivot ∈ xs) :
    (partition3 pivot xs).ret.below.length < xs.length ∧
      (partition3 pivot xs).ret.above.length < xs.length := by
  have hequal : pivot ∈ (partition3 pivot xs).ret.equal := by
    rw [partition3_equal_eq_filter]
    simp [hpivot]
  have hpos : 0 < (partition3 pivot xs).ret.equal.length := by
    cases h : (partition3 pivot xs).ret.equal with
    | nil => simp [h] at hequal
    | cons y ys => simp
  have hlength := partition3_length pivot xs
  omega

private theorem medianOfMedians_quickselect_exists {α : Type u} [LinearOrder α]
    (xs : List α) (k : Nat) (hk : k < xs.length) :
    ∃ x, (quickselect xs k).ret = some x := by
  cases hresult : (quickselect xs k).ret with
  | none =>
      have hlength := (quickselect_eq_none_iff xs k).mp hresult
      omega
  | some x => exact ⟨x, rfl⟩

private theorem medianOfMedians_partition_exists {α : Type u} [LinearOrder α]
    (fuel : Nat)
    (hrec : ∀ (ys : List α) (rank : Nat), ys.length ≤ fuel → rank < ys.length →
      ∃ y, (medianOfMedians.loop fuel ys rank).ret = some y)
    (pivot : α) (xs : List α) (k : Nat) (hpivot : pivot ∈ xs)
    (hsize : xs.length ≤ fuel + 1) (hk : k < xs.length) :
    let parts := (partition3 pivot xs).ret
    ∃ x, (if k < parts.below.length then medianOfMedians.loop fuel parts.below k
      else if k < parts.below.length + parts.equal.length then pure (some pivot)
      else medianOfMedians.loop fuel parts.above
        (k - (parts.below.length + parts.equal.length))).ret = some x := by
  dsimp only
  have hstrict := medianOfMedians_partition_length_lt pivot xs hpivot
  have hlength := partition3_length pivot xs
  by_cases hbelow : k < (partition3 pivot xs).ret.below.length
  · obtain ⟨x, hx⟩ := hrec (partition3 pivot xs).ret.below k (by omega) hbelow
    exact ⟨x, by simpa only [ite_eq_left hbelow] using hx⟩
  · by_cases hequal : k < (partition3 pivot xs).ret.below.length +
        (partition3 pivot xs).ret.equal.length
    · exact ⟨pivot, by simp only [ite_eq_right hbelow, ite_eq_left hequal, ret_pure]⟩
    · obtain ⟨x, hx⟩ := hrec (partition3 pivot xs).ret.above
        (k - ((partition3 pivot xs).ret.below.length + (partition3 pivot xs).ret.equal.length))
        (by omega) (by omega)
      exact ⟨x, by simpa only [ite_eq_right hbelow, ite_eq_right hequal] using hx⟩

private theorem medianOfMedians_loop_exists_step {α : Type u} [LinearOrder α]
    (fuel : Nat)
    (hrec : ∀ (ys : List α) (rank : Nat), ys.length ≤ fuel → rank < ys.length →
      ∃ y, (medianOfMedians.loop fuel ys rank).ret = some y)
    (xs : List α) (k : Nat) (hsize : xs.length ≤ fuel + 1) (hk : k < xs.length) :
    ∃ x, (medianOfMedians.loop (fuel + 1) xs k).ret = some x := by
  by_cases hbase : xs.length ≤ 140
  · obtain ⟨x, hx⟩ := medianOfMedians_quickselect_exists xs k hk
    exact ⟨x, by simpa only [medianOfMedians.loop, ite_eq_left hbase] using hx⟩
  · have hmedians := medianOfMediansGroups_length xs
    have hpositive : 0 < (medianOfMediansGroups xs).ret.length := by omega
    have hmedsize : (medianOfMediansGroups xs).ret.length ≤ fuel := by omega
    obtain ⟨pivot, hpivot⟩ := hrec (medianOfMediansGroups xs).ret
      ((medianOfMediansGroups xs).ret.length / 2) hmedsize (by omega)
    have hpinput := medianOfMediansGroups_mem
      (medianOfMedians_loop_correct fuel _ _ _ hpivot).1
    have hpartition := medianOfMedians_partition_exists fuel hrec pivot xs k hpinput hsize hk
    simpa only [medianOfMedians.loop, ite_eq_right hbase, ret_bind, hpivot] using hpartition

private theorem medianOfMedians_loop_exists {α : Type u} [LinearOrder α] (fuel : Nat) :
    ∀ (xs : List α) (k : Nat), xs.length ≤ fuel → k < xs.length →
      ∃ x, (medianOfMedians.loop fuel xs k).ret = some x := by
  induction fuel with
  | zero =>
      intro xs k hsize hk
      omega
  | succ fuel ih =>
      intro xs k hsize hk
      exact medianOfMedians_loop_exists_step fuel ih xs k hsize hk

/-- A valid rank always returns an input value; the internal fuel cannot run out. -/
theorem medianOfMedians_exists {α : Type u} [LinearOrder α]
    (xs : List α) (k : Nat) (hk : k < xs.length) :
    ∃ x, (medianOfMedians xs k).ret = some x := by
  have h := medianOfMedians_loop_exists xs.length xs k (Nat.le_refl _) hk
  simpa only [medianOfMedians, ite_eq_left hk] using h

/-- Failure occurs exactly for an out-of-range rank, including the empty input. -/
theorem medianOfMedians_eq_none_iff {α : Type u} [LinearOrder α] (xs : List α) (k : Nat) :
    (medianOfMedians xs k).ret = none ↔ xs.length ≤ k := by
  constructor
  · intro hnone
    by_contra hlen
    have hk : k < xs.length := by omega
    obtain ⟨x, hx⟩ := medianOfMedians_exists xs k hk
    rw [hnone] at hx
    cases hx
  · intro hk
    rw [medianOfMedians_eq_pure_none_of_length_le_rank xs k hk]
    rfl

/-- The selector returns exactly the requested entry of the canonical sorted permutation. -/
theorem medianOfMedians_eq_getElem?_insertionSort {α : Type u} [LinearOrder α]
    (xs : List α) (k : Nat) :
    (medianOfMedians xs k).ret = (xs.insertionSort (· ≤ ·))[k]? := by
  cases hresult : (medianOfMedians xs k).ret with
  | none =>
      have hk := (medianOfMedians_eq_none_iff xs k).mp hresult
      symm
      exact List.getElem?_eq_none_iff.mpr (by simpa using hk)
  | some x =>
      obtain ⟨_, hlt, hle⟩ := medianOfMedians_correct hresult
      rw [← quickselect_eq_getElem?_insertionSort]
      exact (quickselect_eq_some_of_count_rank hlt hle).symm

/-- On distinct input the returned value has the source's one-based set rank. -/
theorem medianOfMedians_set_rank {α : Type u} [LinearOrder α]
    {xs : List α} {k : Nat} {x : α} (hnodup : xs.Nodup)
    (hresult : (medianOfMedians xs k).ret = some x) :
    (xs.toFinset.filter (fun y => y ≤ x)).card = k + 1 := by
  obtain ⟨hmem, hlt, hle⟩ := medianOfMedians_correct hresult
  have hequal : (partition3 x xs).ret.equal.length = 1 := by
    rw [partition3_equal_eq_filter, List.filter_eq x, List.length_replicate,
      List.count_eq_one_of_mem hnodup hmem]
  rw [partition3_count_lt] at hlt
  rw [partition3_count_le] at hle
  rw [hnodup.card_eq_countP, partition3_count_le, hequal]
  omega

/-- Translating a positive source rank `i` to index `i - 1` recovers set rank `i`. -/
theorem medianOfMedians_source_rank {α : Type u} [LinearOrder α]
    {xs : List α} (i : Nat) (hi : 0 < i) (hnodup : xs.Nodup) {x : α}
    (hresult : (medianOfMedians xs (i - 1)).ret = some x) :
    (xs.toFinset.filter (fun y => y ≤ x)).card = i := by
  have hrank := medianOfMedians_set_rank hnodup hresult
  omega

/-- Every valid one-based rank on distinct input returns a member with that set rank. -/
theorem medianOfMedians_source_exists {α : Type u} [LinearOrder α]
    (xs : List α) (i : Nat) (hi : 0 < i) (hlen : i ≤ xs.length) (hnodup : xs.Nodup) :
    ∃ x, (medianOfMedians xs (i - 1)).ret = some x ∧ x ∈ xs ∧
      (xs.toFinset.filter (fun y => y ≤ x)).card = i := by
  obtain ⟨x, hx⟩ := medianOfMedians_exists xs (i - 1) (by omega)
  exact ⟨x, hx, (medianOfMedians_correct hx).1, medianOfMedians_source_rank i hi hnodup hx⟩

/-- The lower median uses rank `(length - 1) / 2`, including even input lengths. -/
theorem medianOfMedians_lower_median {α : Type u} [LinearOrder α]
    (xs : List α) (hnonempty : 0 < xs.length) :
    ∃ x, (medianOfMedians xs ((xs.length - 1) / 2)).ret = some x ∧
      x ∈ xs ∧ xs.countP (fun y => decide (y < x)) ≤ (xs.length - 1) / 2 ∧
        (xs.length - 1) / 2 < xs.countP (fun y => decide (y ≤ x)) := by
  obtain ⟨x, hx⟩ := medianOfMedians_exists xs ((xs.length - 1) / 2) (by omega)
  exact ⟨x, hx, medianOfMedians_correct hx⟩

/-- The upper median uses rank `length / 2`, including even input lengths. -/
theorem medianOfMedians_upper_median {α : Type u} [LinearOrder α]
    (xs : List α) (hnonempty : 0 < xs.length) :
    ∃ x, (medianOfMedians xs (xs.length / 2)).ret = some x ∧
      x ∈ xs ∧ xs.countP (fun y => decide (y < x)) ≤ xs.length / 2 ∧
        xs.length / 2 < xs.countP (fun y => decide (y ≤ x)) := by
  obtain ⟨x, hx⟩ := medianOfMedians_exists xs (xs.length / 2) (by omega)
  exact ⟨x, hx, medianOfMedians_correct hx⟩

private theorem medianOfMedians_loop_pivot_weak_discard {α : Type u} [LinearOrder α]
    {xs : List α} (fuel : Nat) {pivot : α}
    (hresult : (medianOfMedians.loop fuel (medianOfMediansGroups xs).ret
      ((medianOfMediansGroups xs).ret.length / 2)).ret = some pivot) :
    3 * ((xs.length + 9) / 10 - 2) ≤ xs.countP (fun y => decide (y ≤ pivot)) ∧
      3 * ((xs.length + 9) / 10 - 2) ≤ xs.countP (fun y => decide (pivot ≤ y)) := by
  have hgroups := medianOfMediansGroups_correct xs
  have hcount := hgroups.length_eq.trans (medianOfMediansGroups_length xs)
  have h := medianOfMedians_weak_discard_bound (xs.toChunks 5) (medianOfMediansGroups xs).ret pivot
    (by simpa only [List.flatten_toChunks] using hcount)
    (fun group hg => List.length_eq_of_mem_dropLast_toChunks 5 xs group hg)
    hgroups (medianOfMedians_loop_correct fuel _ _ _ hresult).2
  simpa only [List.flatten_toChunks] using h

private theorem medianOfMedians_loop_pivot_strict_discard {α : Type u} [LinearOrder α]
    {xs : List α} (fuel : Nat) {pivot : α} (hnodup : xs.Nodup)
    (hresult : (medianOfMedians.loop fuel (medianOfMediansGroups xs).ret
      ((medianOfMediansGroups xs).ret.length / 2)).ret = some pivot) :
    3 * ((xs.length + 9) / 10 - 2) ≤ xs.countP (fun y => decide (y < pivot)) ∧
      3 * ((xs.length + 9) / 10 - 2) ≤ xs.countP (fun y => decide (pivot < y)) := by
  have hgroups := medianOfMediansGroups_correct xs
  have hcount := hgroups.length_eq.trans (medianOfMediansGroups_length xs)
  have h := medianOfMedians_strict_discard_bound (xs.toChunks 5)
    (medianOfMediansGroups xs).ret pivot
    (by simpa only [List.flatten_toChunks] using hcount)
    (fun group hg => List.length_eq_of_mem_dropLast_toChunks 5 xs group hg)
    hgroups (medianOfMedians_loop_correct fuel _ _ _ hresult).2
    (by simpa only [List.flatten_toChunks] using hnodup)
  simpa only [List.flatten_toChunks] using h

private theorem medianOfMedians_loop_base_time {α : Type u} [LinearOrder α]
    (fuel : Nat) (xs : List α) (k : Nat) (hlen : xs.length ≤ 140) :
    (medianOfMedians.loop fuel xs k).time ≤ 80 * xs.length := by
  cases fuel with
  | zero => simp [medianOfMedians.loop]
  | succ fuel =>
      have h := medianOfMedians_base_time xs k hlen
      rw [medianOfMedians_eq_quickselect_of_length_le xs k hlen] at h
      simpa only [medianOfMedians.loop, ite_eq_left hlen] using h

private theorem medianOfMedians_partition_child_sizes {α : Type u} [LinearOrder α]
    (pivot : α) (xs : List α)
    (hweak : 3 * ((xs.length + 9) / 10 - 2) ≤ xs.countP (fun y => decide (y ≤ pivot)) ∧
      3 * ((xs.length + 9) / 10 - 2) ≤ xs.countP (fun y => decide (pivot ≤ y))) :
    (partition3 pivot xs).ret.below.length ≤ 7 * xs.length / 10 + 6 ∧
      (partition3 pivot xs).ret.above.length ≤ 7 * xs.length / 10 + 6 := by
  have hlength := partition3_length pivot xs
  have hlt := partition3_count_lt pivot xs
  have hle := partition3_count_le pivot xs
  have hcomplement : xs.length = xs.countP (fun y => decide (y < pivot)) +
      xs.countP (fun y => decide (pivot ≤ y)) := by
    simpa using List.length_eq_countP_add_countP (fun y => decide (y < pivot)) (l := xs)
  omega

private theorem medianOfMedians_branch_time {α : Type u} [LinearOrder α] (fuel : Nat)
    (hrec : ∀ (ys : List α) (rank : Nat), (medianOfMedians.loop fuel ys rank).time ≤ 80 * ys.length)
    (pivot : α) (xs : List α) (k : Nat)
    (hbound : (partition3 pivot xs).ret.below.length ≤ 7 * xs.length / 10 + 6 ∧
      (partition3 pivot xs).ret.above.length ≤ 7 * xs.length / 10 + 6) :
    let parts := (partition3 pivot xs).ret
    ∃ p, p ≤ 7 * xs.length / 10 + 6 ∧
      (if k < parts.below.length then medianOfMedians.loop fuel parts.below k
        else if k < parts.below.length + parts.equal.length then pure (some pivot)
        else medianOfMedians.loop fuel parts.above (k - (parts.below.length + parts.equal.length))).time ≤ 80 * p := by
  dsimp only
  by_cases hbelow : k < (partition3 pivot xs).ret.below.length
  · refine ⟨(partition3 pivot xs).ret.below.length, hbound.1, ?_⟩
    simpa only [ite_eq_left hbelow] using hrec _ _
  · by_cases hequal : k < (partition3 pivot xs).ret.below.length + (partition3 pivot xs).ret.equal.length
    · refine ⟨0, by omega, ?_⟩
      simp only [ite_eq_right hbelow, ite_eq_left hequal, time_pure]
      omega
    · refine ⟨(partition3 pivot xs).ret.above.length, hbound.2, ?_⟩
      simpa only [ite_eq_right hbelow, ite_eq_right hequal] using hrec _ _

/-- The two BFPRT child sizes leave enough budget for linear local work. -/
theorem medianOfMedians_child_size_budget (n m p : Nat) (hn : 140 ≤ n)
    (hm : m ≤ (n + 4) / 5) (hp : p ≤ 7 * n / 10 + 6) :
    20 * m + 20 * p + n ≤ 20 * n := by
  omega

/-- The child bounds and linear local work fit the same comparison-cost budget. -/
theorem medianOfMedians_combine_time (n m p a leftCost rightCost : Nat)
    (hn : 140 ≤ n) (hm : m ≤ (n + 4) / 5) (hp : p ≤ 7 * n / 10 + 6)
    (hleft : leftCost ≤ 20 * a * m) (hright : rightCost ≤ 20 * a * p) :
    leftCost + rightCost + a * n ≤ 20 * a * n := by
  have hsize := medianOfMedians_child_size_budget n m p hn hm hp
  calc leftCost + rightCost + a * n
      ≤ 20 * a * m + 20 * a * p + a * n :=
        Nat.add_le_add (Nat.add_le_add hleft hright) (Nat.le_refl _)
    _ = a * (20 * m + 20 * p + n) := by
      rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm a 20]
    _ ≤ a * (20 * n) := Nat.mul_le_mul (Nat.le_refl a) hsize
    _ = 20 * a * n := by rw [← Nat.mul_assoc, Nat.mul_comm a 20]

private theorem medianOfMedians_loop_some_time {α : Type u} [LinearOrder α] (fuel : Nat)
    (hrec : ∀ (ys : List α) (rank : Nat), (medianOfMedians.loop fuel ys rank).time ≤ 80 * ys.length)
    (xs : List α) (k : Nat) (pivot : α) (hlen : 140 < xs.length)
    (hpivot : (medianOfMedians.loop fuel (medianOfMediansGroups xs).ret
      ((medianOfMediansGroups xs).ret.length / 2)).ret = some pivot) :
    (medianOfMedians.loop (fuel + 1) xs k).time ≤ 80 * xs.length := by
  have hmed := hrec (medianOfMediansGroups xs).ret ((medianOfMediansGroups xs).ret.length / 2)
  have hgroups := medianOfMediansGroups_time xs
  have hm := medianOfMediansGroups_length xs
  have hparts := medianOfMedians_partition_child_sizes pivot xs
    (medianOfMedians_loop_pivot_weak_discard fuel hpivot)
  obtain ⟨p, hp, hbranch⟩ := medianOfMedians_branch_time fuel hrec pivot xs k hparts
  have hbudget := medianOfMedians_combine_time xs.length (medianOfMediansGroups xs).ret.length p 4
    (medianOfMedians.loop fuel (medianOfMediansGroups xs).ret
      ((medianOfMediansGroups xs).ret.length / 2)).time _
    (Nat.le_of_lt hlen) (Nat.le_of_eq hm) hp hmed hbranch
  simp only [medianOfMedians.loop, ite_eq_right (Nat.not_le.mpr hlen), time_bind, hpivot,
    partition3_time]
  omega

private theorem medianOfMedians_loop_time_step {α : Type u} [LinearOrder α] (fuel : Nat)
    (hrec : ∀ (ys : List α) (rank : Nat), (medianOfMedians.loop fuel ys rank).time ≤ 80 * ys.length)
    (xs : List α) (k : Nat) :
    (medianOfMedians.loop (fuel + 1) xs k).time ≤ 80 * xs.length := by
  by_cases hbase : xs.length ≤ 140
  · exact medianOfMedians_loop_base_time (fuel + 1) xs k hbase
  have hlen : 140 < xs.length := by omega
  cases hpivot : (medianOfMedians.loop fuel (medianOfMediansGroups xs).ret
      ((medianOfMediansGroups xs).ret.length / 2)).ret with
  | none =>
      have hgroups := medianOfMediansGroups_time xs
      have hm := medianOfMediansGroups_length xs
      have hmed := hrec (medianOfMediansGroups xs).ret ((medianOfMediansGroups xs).ret.length / 2)
      have hbudget := medianOfMedians_combine_time xs.length (medianOfMediansGroups xs).ret.length 0 4
        (medianOfMedians.loop fuel (medianOfMediansGroups xs).ret
          ((medianOfMediansGroups xs).ret.length / 2)).time 0
        (Nat.le_of_lt hlen) (Nat.le_of_eq hm) (by omega) hmed (by omega)
      simp only [medianOfMedians.loop, ite_eq_right hbase, time_bind, hpivot, time_pure]
      omega
  | some pivot => exact medianOfMedians_loop_some_time fuel hrec xs k pivot hlen hpivot

private theorem medianOfMedians_loop_time {α : Type u} [LinearOrder α] (fuel : Nat) :
    ∀ (xs : List α) (k : Nat), (medianOfMedians.loop fuel xs k).time ≤ 80 * xs.length := by
  induction fuel with
  | zero => intro xs k; simp [medianOfMedians.loop]
  | succ fuel ih => intro xs k; exact medianOfMedians_loop_time_step fuel ih xs k

/-- Actual comparison charges are at most eighty per input occurrence, including duplicates. -/
theorem medianOfMedians_time {α : Type u} [LinearOrder α] (xs : List α) (k : Nat) :
    (medianOfMedians xs k).time ≤ 80 * xs.length := by
  by_cases hk : k < xs.length
  · simpa only [medianOfMedians, ite_eq_left hk] using medianOfMedians_loop_time xs.length xs k
  · simp [medianOfMedians, hk]

/-- Strong induction bounds a function with the BFPRT recursive child sizes. -/
theorem medianOfMedians_linear_recurrence (T : Nat → Nat) (a : Nat)
    (hbase : ∀ n, n ≤ 140 → T n ≤ 20 * a * n)
    (hstep : ∀ n, 140 < n → ∃ m p,
      m ≤ (n + 4) / 5 ∧ p ≤ 7 * n / 10 + 6 ∧ T n ≤ T m + T p + a * n) :
    ∀ n, T n ≤ 20 * a * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 141 with hle | hge
    · exact hbase n (by omega)
    · have hgt : 140 < n := by omega
      obtain ⟨m, p, hm, hp, hT⟩ := hstep n hgt
      have hmn : m < n := by omega
      have hpn : p < n := by omega
      have hleft := ih m hmn
      have hright := ih p hpn
      have hcomb := medianOfMedians_combine_time n m p a (T m) (T p)
        (Nat.le_of_lt hgt) hm hp hleft hright
      exact Nat.le_trans hT hcomb

end Cslib.Algorithms.Lean.TimeM
