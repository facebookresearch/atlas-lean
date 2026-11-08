/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue.Correctness
import all CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue.Basic
import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Selected-event bounds for indexed binary heap operations

Upward recursion reduces parent depth; downward recursion reduces the remaining
child-depth allowance. The bounds concern the exact executed event tuple, not
RAM/word/bit operations or allocation. Repeated construction uses actual INSERT calls.

Retained Lean is authored/repaired by Codex at Adam Kiezun's explicit selection.
-/

namespace Cslib.Algorithms.Lean.IndexedMinQueue

set_option autoImplicit false

universe u

open scoped BigOperators

private lemma event_le_one (i c : Fin 5) : event i c ≤ 1 := by
  unfold event
  split <;> omega

private lemma parent_depth (i : Nat) (hi : 0 < i) :
    Nat.log2 (heapParent i + 1) + 1 = Nat.log2 (i + 1) := by
  have hdiv : heapParent i + 1 = (i + 1) / 2 := by unfold heapParent; omega
  rw [hdiv, Nat.log2_def (i + 1)]
  simp only [ite_eq_left (by omega : 2 ≤ i + 1)]

private lemma log2_monotone {x y : Nat} (h : x ≤ y) : Nat.log2 x ≤ Nat.log2 y := by
  simpa only [Nat.log2_eq_log_two] using Nat.log_monotone h

private lemma child_depth (i c : Nat) (hc : 2 * i + 1 ≤ c) :
    Nat.log2 (i + 1) + 1 ≤ Nat.log2 (c + 1) := by
  have hm := log2_monotone (show (i + 1) * 2 ≤ c + 1 by omega)
  rw [Nat.log2_eq_log_two, Nat.log_mul_base (by omega : 1 < 2) (by omega)] at hm
  simpa only [Nat.log2_eq_log_two] using hm

private lemma smallerChild_level {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n)) (i c : Nat)
    (hchild : smallerChild a i = some c) :
    Nat.log2 (i + 1) + 1 ≤ Nat.log2 (c + 1) := by
  apply child_depth
  unfold smallerChild at hchild
  split at hchild
  · split at hchild
    · split at hchild
      · simp only [Option.some.injEq] at hchild
        subst c
        unfold heapRight
        omega
      · simp only [Option.some.injEq] at hchild
        subst c
        unfold heapLeft
        omega
    · simp only [Option.some.injEq] at hchild
      subst c
      unfold heapLeft
      omega
  · contradiction

private lemma child_allowance {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n)) (i c : Nat)
    (hchild : smallerChild a i = some c) :
    (Nat.log2 a.size - Nat.log2 (c + 1) + 1) + 1 ≤
      Nat.log2 a.size - Nat.log2 (i + 1) + 1 := by
  have hc := smallerChild_valid a i c hchild
  have hd := smallerChild_level a i c hchild
  have hbound := log2_monotone (show c + 1 ≤ a.size by omega)
  omega

private lemma siftUpTracked_depth_bound {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n)
    (i : Nat) (c : Fin 5) :
    (siftUpTracked a position hcap i).time c ≤ 5 * (Nat.log2 (i + 1) + 1) := by
  induction i using Nat.strong_induction_on generalizing a position with
  | h i ih =>
    rw [siftUpTracked]
    split
    · rename_i hi
      split
      · rename_i hpos
        dsimp only
        by_cases hlt : a[i] < a[heapParent i]'(heapParent_lt_size a i hi hpos)
        · simp only [ite_eq_left hlt]
          have hr := ih (heapParent i) (parent_lt i hpos)
            (a.swap i (heapParent i) hi (heapParent_lt_size a i hi hpos))
            (swapPosition a position hcap i (heapParent i) hi
              (heapParent_lt_size a i hi hpos)) (by simpa using hcap)
          rw [parent_depth i hpos] at hr
          have h0 := event_le_one 0 c
          have h1 := event_le_one 1 c
          have h3 := event_le_one 3 c
          change event 0 c + event 1 c + event 3 c + event 3 c + _ ≤ _
          omega
        · simp only [ite_eq_right hlt]
          have := event_le_one 0 c
          change event 0 c ≤ _
          omega
      · change 0 ≤ _
        omega
    · change 0 ≤ _
      omega

private lemma siftUpTracked_bound {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n)
    (i : Nat) (c : Fin 5) :
    (siftUpTracked a position hcap i).time c ≤ 5 * (Nat.log2 (a.size + 1) + 1) := by
  by_cases hi : i < a.size
  · have hr := siftUpTracked_depth_bound a position hcap i c
    have hl := log2_monotone (show i + 1 ≤ a.size + 1 by omega)
    omega
  · rw [siftUpTracked]
    simp only [dite_eq_right hi]
    change 0 ≤ _
    omega

private lemma childSelectionTime_le_one {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n)) (i : Nat) (c : Fin 5) :
    childSelectionTime a i c ≤ 1 := by
  unfold childSelectionTime
  split
  · exact event_le_one 0 c
  · exact Nat.zero_le _

private lemma siftDownTracked_depth_bound {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n)
    (i : Nat) (c : Fin 5) :
    (siftDownTracked a position hcap i).time c ≤
      5 * (Nat.log2 a.size - Nat.log2 (i + 1) + 1) := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a position i with
  | h m ih =>
    rw [siftDownTracked]
    split
    · change 0 ≤ _
      omega
    · rename_i child hchild
      dsimp only
      have hvalid := smallerChild_valid a i child hchild
      have hgt := smallerChild_gt a i child hchild
      have hi := hgt.trans hvalid
      by_cases hlt : a[child] < a[i]
      · simp only [ite_eq_left hlt]
        have hdec : a.size - child < m := by omega
        have hr := ih (a.size - child) hdec
          (a.swap i child hi hvalid)
          (swapPosition a position hcap i child hi hvalid)
          (by simpa using hcap) child (by simp only [Array.size_swap])
        simp only [Array.size_swap] at hr
        have hdepth := child_allowance a i child hchild
        have hchoose := childSelectionTime_le_one a i c
        have h0 := event_le_one 0 c
        have h1 := event_le_one 1 c
        have h3 := event_le_one 3 c
        change childSelectionTime a i c + event 0 c + event 1 c +
          event 3 c + event 3 c + _ ≤ _
        omega
      · simp only [ite_eq_right hlt]
        have hchoose := childSelectionTime_le_one a i c
        have h0 := event_le_one 0 c
        change childSelectionTime a i c + event 0 c ≤ _
        omega

private lemma siftDownTracked_bound {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n)
    (i : Nat) (c : Fin 5) :
    (siftDownTracked a position hcap i).time c ≤
      5 * (Nat.log2 (a.size + 1) + 1) := by
  have hr := siftDownTracked_depth_bound a position hcap i c
  have hl := log2_monotone (show a.size ≤ a.size + 1 by omega)
  omega

/-- Each selected INSERT event coordinate has the frozen logarithmic bound. -/
theorem insert_time {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : WithTop W) (c : Fin 5) :
    (insert q v key).time c ≤ 20 * (Nat.log2 (q.heap.data.size + 1) + 1) := by
  unfold insert
  split
  · have he := event_le_one 2 c
    change event 2 c ≤ _
    omega
  · rename_i hp
    dsimp only
    have hs : q.heap.data.size < n := absent_spare q v
      (by simpa [Option.isSome_iff_ne_none] using hp)
    have hb := siftUpTracked_depth_bound
      (q.heap.data.push (toLex (key, v)))
      (q.position.set v (some ⟨q.heap.data.size, hs⟩))
      (by simp; omega) q.heap.data.size c
    have h2 := event_le_one 2 c
    have h3 := event_le_one 3 c
    have h4 := event_le_one 4 c
    change event 2 c + event 3 c + event 4 c + _ ≤ _
    omega

/-- Each selected DECREASE-KEY coordinate has the frozen logarithmic bound. -/
theorem decreaseKey_time {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : W) (c : Fin 5) :
    (decreaseKey q v key).time c ≤ 20 * (Nat.log2 (q.heap.data.size + 1) + 1) := by
  unfold decreaseKey
  split
  · have he := event_le_one 2 c
    change event 2 c ≤ _
    omega
  · rename_i i hp
    dsimp only
    split
    · have hi := position_valid q v i hp
      have hb := siftUpTracked_bound
        (q.heap.data.set i.val (toLex ((↑key : WithTop W), v)) hi)
        q.position (by simpa using q.capacity) i.val c
      simp only [Array.size_set] at hb
      have h2 := event_le_one 2 c
      have h0 := event_le_one 0 c
      have h4 := event_le_one 4 c
      change event 2 c + event 0 c + event 4 c + _ ≤ _
      omega
    · have h2 := event_le_one 2 c
      have h0 := event_le_one 0 c
      change event 2 c + event 0 c ≤ _
      omega

/-- Each selected EXTRACT-MIN coordinate has the frozen logarithmic bound. -/
theorem extractMin_time {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (c : Fin 5) :
    (extractMin q).time c ≤ 20 * (Nat.log2 (q.heap.data.size + 1) + 1) := by
  unfold extractMin
  split
  · change 0 ≤ _
    omega
  · rename_i hempty
    dsimp only
    split
    · have h3 := event_le_one 3 c
      have h4 := event_le_one 4 c
      change event 3 c + event 4 c ≤ _
      omega
    · dsimp only
      have hne : 0 < q.heap.data.size := by omega
      have hj : q.heap.data.size - 1 < q.heap.data.size := by omega
      let a := (q.heap.data.swap 0 (q.heap.data.size - 1) hne hj).pop
      have hc : a.size ≤ n := by
        have hcap := q.capacity
        simp only [a, Array.size_pop, Array.size_swap]
        omega
      have hb := siftDownTracked_bound a
        ((swapPosition q.heap.data q.position q.capacity 0
          (q.heap.data.size - 1) hne hj).set (ofLex (q.heap.data[0]'hne)).2 none)
        hc 0 c
      have hl := log2_monotone (show a.size + 1 ≤ q.heap.data.size + 1 by
        simp only [a, Array.size_pop, Array.size_swap]
        omega)
      dsimp only [a] at hb hl
      have h1 := event_le_one 1 c
      have h3 := event_le_one 3 c
      have h4 := event_le_one 4 c
      change event 1 c + event 3 c + event 3 c + event 3 c + event 4 c + _ ≤ _
      omega

private lemma source_order_size {W : Type u} [LinearOrder W] {n : Nat}
    (qs : Fin (n + 1) → IndexedMinQueue W n) (keys : Fin n → WithTop W)
    (hstart : qs 0 = empty (W := W) n)
    (hsteps : ∀ i : Fin n,
      (insert (qs i.castSucc) i (keys i)).ret = some (qs i.succ)) :
    ∀ j : Fin (n + 1), (qs j).heap.data.size = j.val := by
  apply Fin.induction
  · rw [hstart]
    rfl
  · intro i ih
    have hh := (insert_ret (qs i.castSucc) (qs i.succ) i (keys i) (hsteps i)).1
    rw [hh]
    change (siftUp ((qs i.castSucc).heap.data.push (toLex (keys i, i)))
      (qs i.castSucc).heap.data.size).size = i.val + 1
    rw [(siftUp_perm _ _).size_eq, Array.size_push, ih]
    rfl

/-- Source-order repeated INSERT has the frozen summed event bound. -/
theorem repeated_insert_time {W : Type u} [LinearOrder W] {n : Nat}
    (qs : Fin (n + 1) → IndexedMinQueue W n) (keys : Fin n → WithTop W)
    (hstart : qs 0 = empty (W := W) n)
    (hsteps : ∀ i : Fin n,
      (insert (qs i.castSucc) i (keys i)).ret = some (qs i.succ))
    (c : Fin 5) :
    (∑ i : Fin n, (insert (qs i.castSucc) i (keys i)).time c) ≤
      20 * n * (Nat.log2 (n + 1) + 1) := by
  have hsizes := source_order_size qs keys hstart hsteps
  have hterm : ∀ i : Fin n,
      (insert (qs i.castSucc) i (keys i)).time c ≤
        20 * (Nat.log2 (n + 1) + 1) := by
    intro i
    refine (insert_time (qs i.castSucc) i (keys i) c).trans ?_
    have hsize : (qs i.castSucc).heap.data.size + 1 ≤ n + 1 := by
      rw [hsizes i.castSucc]
      exact Nat.add_le_add_right (Nat.le_of_lt i.isLt) 1
    have hlog := log2_monotone hsize
    omega
  calc
    (∑ i : Fin n, (insert (qs i.castSucc) i (keys i)).time c) ≤
        ∑ _i : Fin n, 20 * (Nat.log2 (n + 1) + 1) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = 20 * n * (Nat.log2 (n + 1) + 1) := by
      simp [mul_comm, mul_left_comm]

end Cslib.Algorithms.Lean.IndexedMinQueue
