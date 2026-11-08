/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Prod

/-! # One-pass sift-down event costs

The counters record value comparisons and actual array swaps, not elapsed time.
Erasing counters gives canonical sift-down without a heap-order precondition.
Bounds use the remaining depth `Nat.log2 a.size - Nat.log2 (i + 1)`.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

/-- The selected child lies exactly one binary-tree level below its parent. -/
theorem log2_smallerChild_add_one {α : Type u} [LinearOrder α]
    (a : Array α) (i c : Nat) (hchild : smallerChild a i = some c) :
    Nat.log2 (c + 1) = Nat.log2 (i + 1) + 1 := by
  have hgt := smallerChild_gt a i c hchild
  have hdiv : (c + 1) / 2 = i + 1 := by
    unfold smallerChild at hchild
    split at hchild
    · split at hchild
      · split at hchild <;> cases hchild <;> simp only [heapLeft, heapRight] <;> omega
      · cases hchild
        simp only [heapLeft]
        omega
    · cases hchild
  rw [Nat.log2_def (c + 1)]
  split
  · rw [hdiv]
  · omega

/-- A selected child's depth cannot exceed the maximal depth allowed by array size. -/
theorem log2_smallerChild_le_size {α : Type u} [LinearOrder α]
    (a : Array α) (i c : Nat) (hchild : smallerChild a i = some c) :
    Nat.log2 (c + 1) ≤ Nat.log2 a.size := by
  have hc := smallerChild_valid a i c hchild
  have hpow := (Nat.le_log2 (by omega : c + 1 ≠ 0)).mp
    (show Nat.log2 (c + 1) ≤ Nat.log2 (c + 1) from le_rfl)
  exact (Nat.le_log2 (by omega : a.size ≠ 0)).mpr (hpow.trans (by omega))

namespace TimeM

/-- Canonical child selection, charging one comparison when both children exist. -/
def timedSmallerChild {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    TimeM (Nat × Nat) (Option Nat) :=
  if hl : heapLeft i < a.size then
    if hr : heapRight i < a.size then do
      tick (1, 0)
      pure (if a[heapRight i] < a[heapLeft i] then
        some (heapRight i) else some (heapLeft i))
    else pure (some (heapLeft i))
  else pure none

/-- Erasing the selector's events gives canonical child selection. -/
theorem ret_timedSmallerChild {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) :
    (timedSmallerChild a i).ret = smallerChild a i := by
  unfold timedSmallerChild smallerChild
  split <;> rename_i hl
  · split <;> rfl
  · rfl

/-- Sift-down with `(value comparisons, array swaps)` as its event cost.
Index arithmetic, bounds checks, pattern matching and recursive calls are free.
The child-selection comparison is charged only when both children exist. -/
def siftDown {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    TimeM (Nat × Nat) (Array α) :=
  let selected := timedSmallerChild a i
  match hchild : selected.ret with
  | none => ⟨a, selected.time⟩
  | some c =>
    have hcanonical : smallerChild a i = some c :=
      (ret_timedSmallerChild a i).symm.trans hchild
    have hc : c < a.size := smallerChild_valid a i c hcanonical
    have hi : i < a.size := (smallerChild_gt a i c hcanonical).trans hc
    let run : TimeM (Nat × Nat) (Array α) := do
      tick (1, 0)
      if hlt : a[c] < a[i] then
        tick (0, 1)
        siftDown (a.swap i c hi hc) c
      else pure a
    ⟨run.ret, selected.time + run.time⟩
termination_by a.size - i
decreasing_by
  simp only [Array.size_swap]
  have := smallerChild_gt a i c hcanonical
  omega

/-- Erasing events recovers canonical sift-down for every array and index. -/
theorem ret_siftDown {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftDown a i).ret = Cslib.Algorithms.Lean.siftDown a i := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | h n ih =>
    rw [siftDown, Cslib.Algorithms.Lean.siftDown]
    dsimp only
    split
    · rename_i hnone
      have hn : smallerChild a i = none := (ret_timedSmallerChild a i).symm.trans hnone
      split
      · rfl
      · rename_i c hs
        simp only [hn] at hs
        cases hs
    · rename_i c hselected
      have hchild : smallerChild a i = some c :=
        (ret_timedSmallerChild a i).symm.trans hselected
      dsimp only
      simp only [ret_bind]
      split
      · have hc := smallerChild_valid a i c hchild
        have hi := (smallerChild_gt a i c hchild).trans hc
        have hdec : (a.swap i c hi hc).size - c < n := by
          simp only [Array.size_swap]
          rw [← hm]
          have := smallerChild_gt a i c hchild
          omega
        have hih := ih _ hdec (a.swap i c hi hc) c rfl
        simp only [ret_bind]
        split
        · rename_i hn
          simp only [hchild] at hn
          cases hn
        · rename_i d hd
          have hcd : some c = some d := hchild.symm.trans hd
          cases hcd
          split
          · exact hih
          · contradiction
      · split
        · rename_i hn
          simp only [hchild] at hn
          cases hn
        · rename_i d hd
          have hcd : some c = some d := hchild.symm.trans hd
          cases hcd
          split
          · contradiction
          · rfl

/-- Child selection compares values exactly when the right child exists. -/
theorem time_timedSmallerChild {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (timedSmallerChild a i).time =
      if heapRight i < a.size then (1, 0) else (0, 0) := by
  unfold timedSmallerChild
  split
  · split <;> rfl
  · have hr : ¬heapRight i < a.size := by
      unfold heapLeft heapRight at *
      omega
    simp [hr]
    rfl

/-- Selecting no child performs no value comparisons or swaps. -/
theorem time_timedSmallerChild_of_none {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) (hchild : smallerChild a i = none) :
    (timedSmallerChild a i).time = (0, 0) := by
  unfold smallerChild at hchild
  split at hchild
  · split at hchild
    · split at hchild <;> cases hchild
    · cases hchild
  · unfold timedSmallerChild
    split
    · contradiction
    · rfl

/-- Sift-down swaps at most once per remaining binary-tree level. -/
theorem siftDown_swaps_le {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftDown a i).time.2 ≤ Nat.log2 a.size - Nat.log2 (i + 1) := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | h n ih =>
    rw [siftDown]
    dsimp only
    split
    · rename_i hnone
      have hn : smallerChild a i = none := (ret_timedSmallerChild a i).symm.trans hnone
      rw [time_timedSmallerChild_of_none a i hn]
      simp
    · rename_i c hselected
      have hchild : smallerChild a i = some c :=
        (ret_timedSmallerChild a i).symm.trans hselected
      have hs : (timedSmallerChild a i).time.2 = 0 := by
        rw [time_timedSmallerChild]
        split <;> rfl
      dsimp only
      simp only [time_bind]
      split
      · have hc := smallerChild_valid a i c hchild
        have hi := (smallerChild_gt a i c hchild).trans hc
        have hdec : (a.swap i c hi hc).size - c < n := by
          simp only [Array.size_swap]
          rw [← hm]
          have := smallerChild_gt a i c hchild
          omega
        have hb := ih _ hdec (a.swap i c hi hc) c rfl
        have hd := log2_smallerChild_add_one a i c hchild
        have hn := log2_smallerChild_le_size a i c hchild
        simp [hs] at hb ⊢
        omega
      · simp [hs]

/-- Sift-down makes at most two value comparisons per remaining binary-tree level. -/
theorem siftDown_comparisons_le {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftDown a i).time.1 ≤ 2 * (Nat.log2 a.size - Nat.log2 (i + 1)) := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | h n ih =>
    rw [siftDown]
    dsimp only
    split
    · rename_i hnone
      have hn : smallerChild a i = none := (ret_timedSmallerChild a i).symm.trans hnone
      rw [time_timedSmallerChild_of_none a i hn]
      simp
    · rename_i c hselected
      have hchild : smallerChild a i = some c :=
        (ret_timedSmallerChild a i).symm.trans hselected
      have hs : (timedSmallerChild a i).time.1 ≤ 1 := by
        rw [time_timedSmallerChild]
        split <;> simp
      have hd := log2_smallerChild_add_one a i c hchild
      have hn := log2_smallerChild_le_size a i c hchild
      dsimp only
      simp only [time_bind]
      split
      · have hc := smallerChild_valid a i c hchild
        have hi := (smallerChild_gt a i c hchild).trans hc
        have hdec : (a.swap i c hi hc).size - c < n := by
          simp only [Array.size_swap]
          rw [← hm]
          have := smallerChild_gt a i c hchild
          omega
        have hb := ih _ hdec (a.swap i c hi hc) c rfl
        simp at hb ⊢
        omega
      · simp
        omega

/-- Total event count is at most three per remaining binary-tree level. -/
theorem siftDown_time_le {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftDown a i).time.1 + (siftDown a i).time.2 ≤
      3 * (Nat.log2 a.size - Nat.log2 (i + 1)) := by
  have hc := siftDown_comparisons_le a i
  have hs := siftDown_swaps_le a i
  omega

/-- A position with no child incurs no sift-down events. -/
theorem time_siftDown_of_smallerChild_none {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) (hchild : smallerChild a i = none) :
    (siftDown a i).time = (0, 0) := by
  rw [siftDown]
  dsimp only
  split
  · exact time_timedSmallerChild_of_none a i hchild
  · rename_i c hs
    have hc : smallerChild a i = some c := (ret_timedSmallerChild a i).symm.trans hs
    rw [hchild] at hc
    cases hc

/-- Leaves, including invalid indices, incur no sift-down events. -/
theorem time_siftDown_of_heapLeft_ge {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) (h : a.size ≤ heapLeft i) :
    (siftDown a i).time = (0, 0) := by
  apply time_siftDown_of_smallerChild_none
  unfold smallerChild
  split
  · omega
  · rfl

/-- An invalid index incurs no sift-down events. -/
theorem time_siftDown_of_size_le {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) (h : a.size ≤ i) :
    (siftDown a i).time = (0, 0) := by
  apply time_siftDown_of_heapLeft_ge
  unfold heapLeft
  omega

end TimeM

end Cslib.Algorithms.Lean
