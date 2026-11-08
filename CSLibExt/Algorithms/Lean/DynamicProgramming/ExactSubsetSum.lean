/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.MergeSort.MergeSort
import Mathlib.Data.List.Destutter
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Range
import Mathlib.Algebra.Order.BigOperators.Group.List
import Cslib.Foundations.Control.Monad.IsMonadHom.List
import all Init.Data.List.Control

/-!
# Exact subset sum

CLRS, fourth edition, Section 35.5, printed pages 1124-1126. The boxed procedure
is on page 1125. Each phase shifts the saved previous sorted list, merges those
two inputs, removes adjacent duplicate values, and retains values at most the target.
The source MERGE-LISTS implementation is unspecified; this realization reuses the
canonical timed merge and an adjacent equality pass.

The source inputs form a distinct positive-integer set and the target is positive.
The executable Nat domain also admits zero and repeated positions as extensions.
No negative inputs are represented. The result is a maximum value, not a subset witness.

Selected events count the initial and phase assignments, shifted additions, canonical
merge comparisons, adjacent equality decisions, target decisions, and final maximum
decisions. List allocation, cons/reverse, machine arithmetic and physical space are
outside this counter. This is not a full RAM or bit-complexity result.

Codex is the retained producer at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.ExactSubsetSum

@[no_expose] private def adjacentFrom (a : Nat) : List Nat → TimeM Nat (List Nat)
  | [] => pure [a]
  | b :: bs => do
    TimeM.tick 1
    if a ≠ b then
      let rest ← adjacentFrom b bs
      pure (a :: rest)
    else adjacentFrom a bs

@[no_expose] private def adjacent : List Nat → TimeM Nat (List Nat)
  | [] => pure []
  | a :: as => adjacentFrom a as

private theorem adjacentFrom_ret (a : Nat) (xs : List Nat) :
    (adjacentFrom a xs).ret = List.destutter' (· ≠ ·) a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    by_cases hab : a = b <;> simp [adjacentFrom, List.destutter', hab, ih]

private theorem adjacentFrom_time (a : Nat) (xs : List Nat) :
    (adjacentFrom a xs).time = xs.length := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    by_cases hab : a = b <;> simp [adjacentFrom, hab, ih] <;> omega

private theorem adjacent_ret (xs : List Nat) :
    (adjacent xs).ret = xs.destutter (· ≠ ·) := by
  cases xs with
  | nil => rfl
  | cons a xs => exact adjacentFrom_ret a xs

private theorem adjacent_time (xs : List Nat) :
    (adjacent xs).time = xs.length - 1 := by
  cases xs with
  | nil => rfl
  | cons a xs => simpa [adjacent] using adjacentFrom_time a xs

private theorem mem_destutterFrom (a z : Nat) (xs : List Nat) :
    z ∈ List.destutter' (· ≠ ·) a xs ↔ z = a ∨ z ∈ xs := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    by_cases hab : a = b
    · subst b
      simp [List.destutter', ih]
    · simp [List.destutter', hab, ih]

private theorem mem_destutter (xs : List Nat) (z : Nat) :
    z ∈ xs.destutter (· ≠ ·) ↔ z ∈ xs := by
  cases xs with
  | nil => simp
  | cons a xs => simpa [List.destutter] using mem_destutterFrom a z xs

private theorem attainable_append (xs : List Nat) (x z : Nat) :
    (∃ ys : List Nat, ys.Sublist (xs ++ [x]) ∧ ys.sum = z) ↔
      (∃ ys : List Nat, ys.Sublist xs ∧ ys.sum = z) ∨
        (∃ ys : List Nat, ys.Sublist xs ∧ ys.sum + x = z) := by
  simp [← List.mem_sublists, List.sublists_concat, or_and_right, exists_or]

private theorem attainable_powers (n z : Nat) :
    (∃ ys : List Nat, ys.Sublist ((List.range n).map (fun j => 2 ^ j)) ∧ ys.sum = z) ↔
      z < 2 ^ n := by
  induction n generalizing z with
  | zero => simp [eq_comm]
  | succ n ih =>
    rw [List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [attainable_append, pow_succ]
    constructor
    · rintro (h | ⟨ys, hys, hsum⟩)
      · have hz := (ih z).mp h
        omega
      · have hy := (ih ys.sum).mp ⟨ys, hys, rfl⟩
        omega
    · intro hz
      by_cases hl : z < 2 ^ n
      · exact Or.inl ((ih z).mpr hl)
      · obtain ⟨ys, hys, hsum⟩ := (ih (z - 2 ^ n)).mpr (by omega)
        exact Or.inr ⟨ys, hys, by omega⟩

private theorem sum_powers_two (n : Nat) :
    ((List.range n).map (fun i => 2 ^ i)).sum = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.sum_range_succ, ih, pow_succ]
    have hp : 0 < 2 ^ n := Nat.pow_pos (by omega)
    omega

private theorem filterAux_ret (p : Nat → Bool) (xs acc : List Nat) :
    (List.filterAuxM (fun z => do TimeM.tick 1; pure (p z)) xs acc :
      TimeM Nat (List Nat)).ret = (xs.filter p).reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp [List.filterAuxM]
  | cons z xs ih =>
    simp only [List.filterAuxM, TimeM.ret_bind, TimeM.ret_pure]
    rw [ih]
    cases h : p z <;> simp [h, List.reverse_cons, List.append_assoc]

private theorem filterAux_time (p : Nat → Bool) (xs acc : List Nat) :
    (List.filterAuxM (fun z => do TimeM.tick 1; pure (p z)) xs acc :
      TimeM Nat (List Nat)).time = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons z xs ih =>
    simp only [List.filterAuxM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
      TimeM.ret_bind, TimeM.ret_pure]
    rw [ih]
    simp [Nat.add_comm]

private theorem filter_ret (p : Nat → Bool) (xs : List Nat) :
    (xs.filterM (fun z => do TimeM.tick 1; pure (p z)) :
      TimeM Nat (List Nat)).ret = xs.filter p := by
  simp only [List.filterM, TimeM.ret_bind, TimeM.ret_pure, filterAux_ret,
    List.append_nil, List.reverse_reverse]

private theorem filter_time (p : Nat → Bool) (xs : List Nat) :
    (xs.filterM (fun z => do TimeM.tick 1; pure (p z)) :
      TimeM Nat (List Nat)).time = xs.length := by
  simp only [List.filterM, TimeM.time_bind, TimeM.time_pure, filterAux_time, Nat.add_zero]

private theorem shift_ret (xs : List Nat) (x : Nat) :
    (xs.mapM (fun z => do TimeM.tick 1; pure (z + x)) : TimeM Nat (List Nat)).ret =
      xs.map (fun z => z + x) := by
  simpa using congrArg Id.run
    ((TimeM.isMonadHom_pure_ret (T := Nat)).map_listMapM
      (fun z => do TimeM.tick 1; pure (z + x)) xs)

private theorem shift_time (xs : List Nat) (x : Nat) :
    (xs.mapM (fun z => do TimeM.tick 1; pure (z + x)) :
      TimeM Nat (List Nat)).time = xs.length := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
    simp only [List.mapM_cons, TimeM.time_bind, TimeM.time_pure, TimeM.time_tick,
      TimeM.ret_bind, TimeM.ret_pure]
    rw [ih]
    simp [Nat.add_comm]

/-- The sole saved-list exact-subset-sum traversal, returning all distinct feasible sums. -/
public def exactSubsetSumSums (xs : List Nat) (target : Nat) :
    TimeM Nat (List Nat) := do
  TimeM.tick 1
  xs.foldlM (fun saved x => do
    let shifted ← saved.mapM fun z => do
      TimeM.tick 1
      pure (z + x)
    let merged ← TimeM.merge saved shifted
    let unique ← adjacent merged
    let feasible ← unique.filterM fun z => do
      TimeM.tick 1
      pure (decide (z ≤ target))
    TimeM.tick 1
    pure feasible) [0]

private theorem sums_append_ret (xs : List Nat) (x target : Nat) :
    (exactSubsetSumSums (xs ++ [x]) target).ret =
      let saved := (exactSubsetSumSums xs target).ret
      ((TimeM.merge saved (saved.map (fun z => z + x))).ret.destutter (· ≠ ·)).filter
        (fun z => decide (z ≤ target)) := by
  simp only [exactSubsetSumSums, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
    TimeM.ret_bind, TimeM.ret_pure, shift_ret, adjacent_ret, filter_ret]

private theorem sums_append_time (xs : List Nat) (x target : Nat) :
    (exactSubsetSumSums (xs ++ [x]) target).time =
      (exactSubsetSumSums xs target).time + 1 +
        let saved := (exactSubsetSumSums xs target).ret
        let merged := TimeM.merge saved (saved.map (fun z => z + x))
        saved.length + merged.time + (merged.ret.length - 1) +
          (merged.ret.destutter (· ≠ ·)).length := by
  simp only [exactSubsetSumSums, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
    TimeM.time_bind, TimeM.time_pure, TimeM.time_tick, TimeM.ret_bind, TimeM.ret_pure,
    shift_ret, shift_time, adjacent_ret, adjacent_time, filter_time]
  omega

private theorem phase_events_le (saved : List Nat) (x : Nat) :
    (let merged := TimeM.merge saved (saved.map (fun z => z + x));
      saved.length + merged.time + (merged.ret.length - 1) +
        (merged.ret.destutter (· ≠ ·)).length) ≤ 7 * saved.length := by
  have hc := TimeM.merge_time saved (saved.map (fun z => z + x))
  have hl := TimeM.merge_ret_length_eq_sum saved (saved.map (fun z => z + x))
  have hu := (List.destutter_sublist (· ≠ ·)
    ((TimeM.merge saved (saved.map (fun z => z + x))).ret)).length_le
  simp only [List.length_map] at hc hl
  dsimp only
  omega

private theorem sums_take_time (xs : List Nat) (target i : Nat) (hi : i ≤ xs.length) :
    (exactSubsetSumSums (xs.take i) target).time = 1 + i +
      ((List.range i).map fun j =>
        let saved := (exactSubsetSumSums (xs.take j) target).ret
        let merged := TimeM.merge saved (saved.map (fun z => z + xs.getD j 0))
        saved.length + merged.time + (merged.ret.length - 1) +
          (merged.ret.destutter (· ≠ ·)).length).sum := by
  induction i with
  | zero => simp [exactSubsetSumSums]
  | succ i ih =>
    have hlt : i < xs.length := by omega
    have htake : xs.take (i + 1) = xs.take i ++ [xs.getD i 0] := by
      rw [List.take_succ_eq_append_getElem hlt]
      simp [List.getD, hlt]
    rw [htake, sums_append_time, ih (by omega), List.sum_range_succ]
    dsimp only
    omega

private theorem sums_append_mem (xs : List Nat) (x target z : Nat) :
    z ∈ (exactSubsetSumSums (xs ++ [x]) target).ret ↔
      z ≤ target ∧ (z ∈ (exactSubsetSumSums xs target).ret ∨
        ∃ y ∈ (exactSubsetSumSums xs target).ret, y + x = z) := by
  simp [sums_append_ret, mem_destutter, List.mem_merge, and_comm]

/-- Every returned value is exactly a feasible sum of an input sublist. -/
public theorem exactSubsetSumSums_mem (xs : List Nat) (target z : Nat) :
    z ∈ (exactSubsetSumSums xs target).ret ↔
      z ≤ target ∧ ∃ ys : List Nat, ys.Sublist xs ∧ ys.sum = z := by
  induction xs using List.reverseRecOn generalizing z with
  | nil =>
    simp [exactSubsetSumSums]
    omega
  | append_singleton xs x ih =>
    rw [sums_append_mem, attainable_append]
    simp only [ih]
    constructor
    · rintro ⟨hz, h | ⟨y, ⟨hy, ys, hys, hsum⟩, hyz⟩⟩
      · exact ⟨hz, Or.inl h.2⟩
      · exact ⟨hz, Or.inr ⟨ys, hys, by omega⟩⟩
    · rintro ⟨hz, h | ⟨ys, hys, hsum⟩⟩
      · exact ⟨hz, Or.inl ⟨hz, h⟩⟩
      · exact ⟨hz, Or.inr ⟨ys.sum, ⟨by omega, ys, hys, rfl⟩, hsum⟩⟩

/-- The empty sublist's zero sum survives every actual phase. -/
public theorem exactSubsetSumSums_zero_mem (xs : List Nat) (target : Nat) :
    0 ∈ (exactSubsetSumSums xs target).ret := by
  rw [exactSubsetSumSums_mem]
  exact ⟨Nat.zero_le _, [], List.nil_sublist _, rfl⟩

/-- The saved-list traversal returns strictly increasing values, with no duplicates. -/
public theorem exactSubsetSumSums_sorted (xs : List Nat) (target : Nat) :
    (exactSubsetSumSums xs target).ret.Pairwise (· < ·) := by
  induction xs using List.reverseRecOn with
  | nil => simp [exactSubsetSumSums]
  | append_singleton xs x ih =>
    rw [sums_append_ret]
    dsimp only
    have hs := ih.imp fun hab => le_of_lt hab
    have ht : ((exactSubsetSumSums xs target).ret.map (fun z => z + x)).Pairwise
        (· ≤ ·) := hs.map (fun z => z + x) (fun a b hab => by omega)
    have hm := TimeM.sorted_merge hs ht
    rw [hm.destutter_eq_dedup]
    have hw := hm.sublist (List.dedup_sublist _)
    have hn : (TimeM.merge (exactSubsetSumSums xs target).ret
        ((exactSubsetSumSums xs target).ret.map (fun z => z + x))).ret.dedup.Pairwise
          (· ≠ ·) := List.nodup_dedup _
    exact ((hw.and hn).imp fun hab => lt_of_le_of_ne hab.1 hab.2).filter _

/-- The distinct computed sums are bounded by the number of positional sublists. -/
public theorem exactSubsetSumSums_length_le_pow (xs : List Nat) (target : Nat) :
    (exactSubsetSumSums xs target).ret.length ≤ 2 ^ xs.length := by
  have hs : (exactSubsetSumSums xs target).ret ⊆ xs.sublists.map List.sum := by
    intro z hz
    obtain ⟨_, ys, hys, hsum⟩ := (exactSubsetSumSums_mem xs target z).mp hz
    exact List.mem_map.mpr ⟨ys, List.mem_sublists.mpr hys, hsum⟩
  simpa using (exactSubsetSumSums_sorted xs target).nodup.length_le_of_subset hs

/-- Pruning and distinctness bound the actual saved list by the target's numeric value. -/
public theorem exactSubsetSumSums_length_le_target (xs : List Nat) (target : Nat) :
    (exactSubsetSumSums xs target).ret.length ≤ target + 1 := by
  have hs : (exactSubsetSumSums xs target).ret ⊆ List.range (target + 1) := by
    intro z hz
    have hbound := ((exactSubsetSumSums_mem xs target z).mp hz).1
    exact List.mem_range.mpr (by omega)
  simpa using (exactSubsetSumSums_sorted xs target).nodup.length_le_of_subset hs

/-- Nonnegative positional inputs bound all computed sums by the total input value. -/
public theorem exactSubsetSumSums_length_le_sum (xs : List Nat) (target : Nat) :
    (exactSubsetSumSums xs target).ret.length ≤ xs.sum + 1 := by
  have hs : (exactSubsetSumSums xs target).ret ⊆ List.range (xs.sum + 1) := by
    intro z hz
    obtain ⟨_, ys, hys, hsum⟩ := (exactSubsetSumSums_mem xs target z).mp hz
    have hbound := hys.sum_le_sum (fun _ _ => Nat.zero_le _)
    exact List.mem_range.mpr (by omega)
  simpa using (exactSubsetSumSums_sorted xs target).nodup.length_le_of_subset hs

private theorem sums_time_le_exponential (xs : List Nat) (target : Nat) :
    (exactSubsetSumSums xs target).time ≤
      1 + xs.length + 7 * (2 ^ xs.length - 1) := by
  induction xs using List.reverseRecOn with
  | nil => simp [exactSubsetSumSums]
  | append_singleton xs x ih =>
    have hp : 0 < 2 ^ xs.length := Nat.pow_pos (by omega)
    have hc := phase_events_le (exactSubsetSumSums xs target).ret x
    have hl := Nat.mul_le_mul_left 7 (exactSubsetSumSums_length_le_pow xs target)
    rw [sums_append_time]
    simp only [List.length_append, List.length_singleton, pow_succ]
    dsimp only at hc ⊢
    omega

private theorem sums_time_le_numeric (xs : List Nat) (target : Nat) :
    (exactSubsetSumSums xs target).time ≤
      1 + xs.length + 7 * xs.length * min (target + 1) (xs.sum + 1) := by
  induction xs using List.reverseRecOn with
  | nil => simp [exactSubsetSumSums]
  | append_singleton xs x ih =>
    have hm : min (target + 1) (xs.sum + 1) ≤
        min (target + 1) ((xs ++ [x]).sum + 1) := by
      simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
    have hi := le_trans ih (Nat.add_le_add_left
      (Nat.mul_le_mul_left (7 * xs.length) hm) (1 + xs.length))
    have hc := phase_events_le (exactSubsetSumSums xs target).ret x
    have hl := Nat.mul_le_mul_left 7 (le_min
      (exactSubsetSumSums_length_le_target xs target)
      (exactSubsetSumSums_length_le_sum xs target))
    have hn := Nat.mul_le_mul_left 7 hm
    rw [sums_append_time]
    simp only [List.length_append, List.length_singleton, Nat.mul_add, Nat.add_mul,
      Nat.mul_one]
    dsimp only at hc ⊢
    omega

/-- Every actual source-order prefix of the powers-of-two family fills its entire sum range. -/
public theorem exactSubsetSumSums_powers_of_two (n i : Nat) (hi : i ≤ n) :
    (exactSubsetSumSums (((List.range n).map (fun j => 2 ^ j)).take i)
      (2 ^ n - 1)).ret = List.range (2 ^ i) := by
  rw [← List.map_take, List.take_range, min_eq_left hi]
  apply (exactSubsetSumSums_sorted _ _).eq_of_mem_iff List.pairwise_lt_range
  intro z
  rw [exactSubsetSumSums_mem, attainable_powers, List.mem_range]
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hi
  omega

/-- Compute the largest feasible sum by scanning the sole traversal's actual result. -/
public def exactSubsetSum (xs : List Nat) (target : Nat) : TimeM Nat Nat := do
  let sums ← exactSubsetSumSums xs target
  sums.foldlM (fun best z => do
    TimeM.tick 1
    pure (max best z)) 0

private theorem maximumFold_time (xs : List Nat) (best : Nat) :
    (xs.foldlM (fun best z => do TimeM.tick 1; pure (max best z)) best :
      TimeM Nat Nat).time = xs.length := by
  induction xs generalizing best with
  | nil => rfl
  | cons z xs ih =>
    simp only [List.foldlM_cons, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
      TimeM.ret_bind, TimeM.ret_pure]
    rw [ih]
    simp [Nat.add_comm]

/-- The returned maximum scans exactly the actual saved-list traversal's result. -/
public theorem exactSubsetSum_ret (xs : List Nat) (target : Nat) :
    (exactSubsetSum xs target).ret =
      (exactSubsetSumSums xs target).ret.foldl max 0 := by
  simpa [exactSubsetSum] using congrArg Id.run
    ((TimeM.isMonadHom_pure_ret (T := Nat)).map_listFoldlM
      (fun best z => do TimeM.tick 1; pure (max best z)) 0
      (exactSubsetSumSums xs target).ret)

/-- Exact selected-event cost, with every phase reading the actual public prefix result. -/
public theorem exactSubsetSum_time (xs : List Nat) (target : Nat) :
    (exactSubsetSum xs target).time = 1 + xs.length +
      ((List.range xs.length).map fun i =>
        let saved := (exactSubsetSumSums (xs.take i) target).ret
        let merged := TimeM.merge saved (saved.map (fun z => z + xs.getD i 0))
        saved.length + merged.time + (merged.ret.length - 1) +
          (merged.ret.destutter (· ≠ ·)).length).sum +
      (exactSubsetSumSums xs target).ret.length := by
  have hs := sums_take_time xs target xs.length (le_refl _)
  simp only [List.take_length] at hs
  simpa only [exactSubsetSum, TimeM.time_bind, maximumFold_time] using
    congrArg (fun time => time + (exactSubsetSumSums xs target).ret.length) hs

/-- The actual shifted additions alone establish exponential growth on powers-of-two inputs. -/
public theorem exactSubsetSum_time_ge_powers_of_two (n : Nat) :
    2 ^ n - 1 ≤
      (exactSubsetSum ((List.range n).map (fun j => 2 ^ j)) (2 ^ n - 1)).time := by
  have hc : ((List.range n).map (fun i => 2 ^ i)).sum ≤
      ((List.range n).map fun i =>
        let saved := (exactSubsetSumSums
          (((List.range n).map (fun j => 2 ^ j)).take i) (2 ^ n - 1)).ret
        let merged := TimeM.merge saved (saved.map (fun z => z +
          ((List.range n).map (fun j => 2 ^ j)).getD i 0))
        saved.length + merged.time + (merged.ret.length - 1) +
          (merged.ret.destutter (· ≠ ·)).length).sum := by
    apply List.sum_le_sum
    intro i hi
    have hp := exactSubsetSumSums_powers_of_two n i (le_of_lt (List.mem_range.mp hi))
    have hl : (exactSubsetSumSums
        (((List.range n).map (fun j => 2 ^ j)).take i) (2 ^ n - 1)).ret.length = 2 ^ i := by
      rw [hp, List.length_range]
    dsimp only
    omega
  rw [sum_powers_two] at hc
  dsimp only at hc
  rw [exactSubsetSum_time]
  simp only [List.length_map, List.length_range]
  omega

/-- Exponential upper bound on the actual selected-event count, including the final scan. -/
public theorem exactSubsetSum_time_le_exponential (xs : List Nat) (target : Nat) :
    (exactSubsetSum xs target).time ≤
      1 + xs.length + 7 * (2 ^ xs.length - 1) + 2 ^ xs.length := by
  have hs := sums_time_le_exponential xs target
  have hl := exactSubsetSumSums_length_le_pow xs target
  simp only [exactSubsetSum, TimeM.time_bind, maximumFold_time]
  omega

/-- Numeric upper bound on the same run, using both target and total-value cardinalities. -/
public theorem exactSubsetSum_time_le_numeric (xs : List Nat) (target : Nat) :
    (exactSubsetSum xs target).time ≤ 1 + xs.length +
      (7 * xs.length + 1) * min (target + 1) (xs.sum + 1) := by
  have hs := sums_time_le_numeric xs target
  have hl := le_min (exactSubsetSumSums_length_le_target xs target)
    (exactSubsetSumSums_length_le_sum xs target)
  simp only [exactSubsetSum, TimeM.time_bind, maximumFold_time,
    Nat.add_mul, Nat.one_mul]
  omega

/-- A numeric polynomial target gives the source's selected-event polynomial bound. -/
public theorem exactSubsetSum_time_le_of_target_le_pow (xs : List Nat) (target d : Nat)
    (ht : target ≤ xs.length ^ d) :
    (exactSubsetSum xs target).time ≤ 1 + xs.length +
      (7 * xs.length + 1) * (xs.length ^ d + 1) := by
  have hm : min (target + 1) (xs.sum + 1) ≤ xs.length ^ d + 1 := by omega
  exact le_trans (exactSubsetSum_time_le_numeric xs target)
    (Nat.add_le_add_left (Nat.mul_le_mul_left (7 * xs.length + 1) hm) (1 + xs.length))

/-- Bounded numeric input values give the source's selected-event polynomial bound. -/
public theorem exactSubsetSum_time_le_of_values_le_pow (xs : List Nat) (target d : Nat)
    (hx : ∀ x ∈ xs, x ≤ xs.length ^ d) :
    (exactSubsetSum xs target).time ≤ 1 + xs.length +
      (7 * xs.length + 1) * (xs.length * xs.length ^ d + 1) := by
  have hs : xs.sum ≤ xs.length * xs.length ^ d := by
    simpa using List.sum_le_length_nsmul xs (xs.length ^ d) hx
  have hm : min (target + 1) (xs.sum + 1) ≤ xs.length * xs.length ^ d + 1 := by omega
  exact le_trans (exactSubsetSum_time_le_numeric xs target)
    (Nat.add_le_add_left (Nat.mul_le_mul_left (7 * xs.length + 1) hm) (1 + xs.length))

/-- The returned value is optimal for positional Nat inputs, including zero and repeated values. -/
public theorem exactSubsetSum_optimal (xs : List Nat) (target : Nat) :
    (∃ ys : List Nat, ys.Sublist xs ∧ ys.sum = (exactSubsetSum xs target).ret) ∧
      (exactSubsetSum xs target).ret ≤ target ∧
      ∀ ys : List Nat, ys.Sublist xs → ys.sum ≤ target →
        ys.sum ≤ (exactSubsetSum xs target).ret := by
  have hn := List.ne_nil_of_mem (exactSubsetSumSums_zero_mem xs target)
  have heq : (exactSubsetSum xs target).ret = (exactSubsetSumSums xs target).ret.max hn := by
    rw [exactSubsetSum_ret, List.foldl_max_eq_max hn]
    simp
  have hm := List.max_mem hn
  rw [← heq] at hm
  obtain ⟨hle, ys, hys, hsum⟩ := (exactSubsetSumSums_mem xs target _).mp hm
  refine ⟨⟨ys, hys, hsum⟩, hle, ?_⟩
  intro ys hsub hbound
  have hym := (exactSubsetSumSums_mem xs target ys.sum).mpr ⟨hbound, ys, hsub, rfl⟩
  rw [heq]
  exact List.le_max_of_mem hym

/-- CLRS's optimum corollary, retaining its distinct positive-set and positive-target premises.
The positional Nat generalization is `exactSubsetSum_optimal`. -/
public theorem exactSubsetSum_optimal_of_positive (xs : List Nat) (target : Nat)
    (_hd : xs.Nodup) (_hp : ∀ x ∈ xs, 0 < x) (_ht : 0 < target) :
    (∃ ys : List Nat, ys.Sublist xs ∧ ys.sum = (exactSubsetSum xs target).ret) ∧
      (exactSubsetSum xs target).ret ≤ target ∧
      ∀ ys : List Nat, ys.Sublist xs → ys.sum ≤ target →
        ys.sum ≤ (exactSubsetSum xs target).ret :=
  exactSubsetSum_optimal xs target

end Cslib.Algorithms.Lean.ExactSubsetSum
