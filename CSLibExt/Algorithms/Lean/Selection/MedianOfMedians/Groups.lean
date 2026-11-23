/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.InsertionCost
public import MathlibExt.Data.List.ToChunks
import CSLibExt.Algorithms.Lean.Selection.Quickselect
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases

/-!
# Group medians for deterministic selection

MIT 6.046J, Spring 2015, Lecture 2, page 4 sorts columns of at most five
elements before collecting their medians. This operation uses the canonical
Batteries grouping and CSLib insertion sort with its comparison charges.
-/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

/-- **Group medians for median-of-medians selection.** Given a list $xs$ over a linear
order, split $xs$ into consecutive blocks of five elements, the last of which may be shorter.
Sort each block $g$ by insertion sort and return, in block order, the entry at position
$\lfloor (|g| - 1)/2 \rfloor$ (counting from $0$) of each sorted block, that is, its lower
median. The cost is the total number of comparisons made by these insertion sorts. -/
def medianOfMediansGroups {α : Type u} [LinearOrder α] (xs : List α) :
    TimeM Nat (List α) :=
  let rec loop : List (List α) → TimeM Nat (List α)
    | [] => pure []
    | group :: groups => do
        let sorted ← insertionSort group
        let tail ← loop groups
        match sorted[(group.length - 1) / 2]? with
        | none => pure tail
        | some x => pure (x :: tail)
  loop (xs.toChunks 5)

private theorem insertionSort_time_le_twice_length {α : Type u} [LinearOrder α]
    (xs : List α) (hsize : xs.length ≤ 5) :
    (insertionSort xs).time ≤ 2 * xs.length := by
  have hcost := insertionSort_time xs
  interval_cases h : xs.length <;> omega

private theorem medianOfMediansGroups_loop_time {α : Type u} [LinearOrder α]
    (groups : List (List α)) (hgroups : ∀ group ∈ groups, group.length ≤ 5) :
    (medianOfMediansGroups.loop groups).time ≤ 2 * (groups.map List.length).sum := by
  revert hgroups
  induction groups with
  | nil =>
      intro _
      simp [medianOfMediansGroups.loop]
  | cons group groups ih =>
      intro hgroups
      have hhead := insertionSort_time_le_twice_length group (hgroups group (by simp))
      have htail := ih (fun other hother => hgroups other (by simp [hother]))
      simp only [medianOfMediansGroups.loop, time_bind, List.map_cons, List.sum_cons]
      split <;> simp only [time_pure] <;> omega

/-- **Comparison cost of the group medians.** For every list $xs$ of length $n$ over a linear
order, computing the group medians of $xs$ takes at most $2n$ comparisons. -/
theorem medianOfMediansGroups_time {α : Type u} [LinearOrder α] (xs : List α) :
    (medianOfMediansGroups xs).time ≤ 2 * xs.length := by
  have hgroups : ∀ group ∈ xs.toChunks 5, group.length ≤ 5 :=
    fun group hgroup => List.length_le_of_mem_toChunks 5 xs (by decide) group hgroup
  change (medianOfMediansGroups.loop (xs.toChunks 5)).time ≤ 2 * xs.length
  simpa only [← List.length_flatten, List.flatten_toChunks] using
    medianOfMediansGroups_loop_time (xs.toChunks 5) hgroups

private theorem medianOfMediansGroups_loop_mem {α : Type u} [LinearOrder α]
    (groups : List (List α)) {x : α} (hx : x ∈ (medianOfMediansGroups.loop groups).ret) :
    ∃ group ∈ groups, x ∈ group := by
  revert hx
  induction groups with
  | nil =>
      intro hx
      simp [medianOfMediansGroups.loop] at hx
  | cons group groups ih =>
      intro hx
      simp only [medianOfMediansGroups.loop, ret_bind] at hx
      split at hx <;> simp only [ret_pure] at hx
      · obtain ⟨other, hother, hx⟩ := ih hx
        exact ⟨other, by simp [hother], hx⟩
      · rename_i y hy
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨group, by simp,
            (insertionSort_perm group).mem_iff.mp (List.mem_of_getElem? hy)⟩
        · obtain ⟨other, hother, hx⟩ := ih hx
          exact ⟨other, by simp [hother], hx⟩

/-- **Group medians come from the input.** For every list $xs$ over a linear order, every
entry of the list of group medians of $xs$ is an element of $xs$. -/
theorem medianOfMediansGroups_mem {α : Type u} [LinearOrder α] {xs : List α} {x : α}
    (hx : x ∈ (medianOfMediansGroups xs).ret) : x ∈ xs := by
  change x ∈ (medianOfMediansGroups.loop (xs.toChunks 5)).ret at hx
  obtain ⟨group, hgroup, hx⟩ := medianOfMediansGroups_loop_mem (xs.toChunks 5) hx
  exact List.mem_of_mem_toChunks hgroup hx

private theorem insertionSort_getElem?_rank {α : Type u} [LinearOrder α]
    (xs : List α) (k : Nat) {x : α} (h : (insertionSort xs).ret[k]? = some x) :
    x ∈ xs ∧ xs.countP (fun y => decide (y < x)) ≤ k ∧
      k < xs.countP (fun y => decide (y ≤ x)) := by
  apply quickselect_correct
  rw [quickselect_eq_getElem?_insertionSort]
  simpa only [ret_insertionSort] using h

private theorem insertionSort_getElem?_exists {α : Type u} [LinearOrder α]
    (xs : List α) (k : Nat) (hk : k < xs.length) :
    ∃ x, (insertionSort xs).ret[k]? = some x := by
  have hlength := (insertionSort_perm xs).length_eq
  cases hget : (insertionSort xs).ret[k]? with
  | none =>
      have hnone := List.getElem?_eq_none_iff.mp hget
      omega
  | some x => exact ⟨x, rfl⟩

private theorem medianOfMediansGroups_loop_correct {α : Type u} [LinearOrder α]
    (groups : List (List α)) (hgroups : ∀ group ∈ groups, group ≠ []) :
    List.Forall₂ (fun group x => x ∈ group ∧
      group.countP (fun y => decide (y < x)) ≤ (group.length - 1) / 2 ∧
      (group.length - 1) / 2 < group.countP (fun y => decide (y ≤ x)))
      groups (medianOfMediansGroups.loop groups).ret := by
  revert hgroups
  induction groups with
  | nil =>
      intro _
      exact List.Forall₂.nil
  | cons group groups ih =>
      intro hgroups
      have hhead := hgroups group (by simp)
      have hk : (group.length - 1) / 2 < group.length := by
        cases group with
        | nil => exact (hhead rfl).elim
        | cons _ _ => simp only [List.length_cons]; omega
      obtain ⟨x, hx⟩ := insertionSort_getElem?_exists group ((group.length - 1) / 2) hk
      have htail := ih (fun other hother => hgroups other (by simp [hother]))
      simp only [medianOfMediansGroups.loop, ret_bind, hx, ret_pure]
      exact List.Forall₂.cons (insertionSort_getElem?_rank group _ hx) htail

/-- **Group medians are lower medians of their blocks.** Let $xs$ be a list over a linear
order, and let $g_1, \dots, g_m$ be its consecutive blocks of five elements, the last of which
may be shorter. Then the list of group medians of $xs$ has the same length $m$, say
$x_1, \dots, x_m$, and for each $i$, writing $k_i = \lfloor (|g_i| - 1)/2 \rfloor$ and counting
elements of $g_i$ with multiplicity: $x_i$ belongs to $g_i$, at most $k_i$ elements of $g_i$
are less than $x_i$, and more than $k_i$ elements of $g_i$ are less than or equal to $x_i$. -/
theorem medianOfMediansGroups_correct {α : Type u} [LinearOrder α] (xs : List α) :
    List.Forall₂ (fun group x => x ∈ group ∧
      group.countP (fun y => decide (y < x)) ≤ (group.length - 1) / 2 ∧
      (group.length - 1) / 2 < group.countP (fun y => decide (y ≤ x)))
      (xs.toChunks 5) (medianOfMediansGroups xs).ret := by
  exact medianOfMediansGroups_loop_correct (xs.toChunks 5)
    (fun group hgroup => List.ne_nil_of_mem_toChunks 5 xs group hgroup)

/-- **Number of group medians.** For every list $xs$ of length $n$ over a linear order, the
list of group medians of $xs$ has exactly $\lfloor (n + 4)/5 \rfloor = \lceil n/5 \rceil$
entries. -/
theorem medianOfMediansGroups_length {α : Type u} [LinearOrder α] (xs : List α) :
    (medianOfMediansGroups xs).ret.length = (xs.length + 4) / 5 := by
  rw [← (medianOfMediansGroups_correct xs).length_eq]
  have hlength := List.length_toChunks 5 xs (by decide)
  have hnum : xs.length + 5 - 1 = xs.length + 4 := by omega
  simpa only [hnum] using hlength

end Cslib.Algorithms.Lean.TimeM
