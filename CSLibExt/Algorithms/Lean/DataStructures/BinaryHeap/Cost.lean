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

/-!
# Binary-heap sift-up event bounds

The cost coordinates count value comparisons and actual swaps, respectively.
Bounds checks, reads, copying, allocation, calls, and comparator implementation costs are free
in this model. These are execution-linked event bounds, not physical running-time bounds.
The canonical heap representation and operations are unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/-- Moving a nonroot index to its parent lowers its binary-tree depth by one. -/
theorem log2_heapParent_add_one (i : Nat) (hi : 0 < i) :
    Nat.log2 (heapParent i + 1) + 1 = Nat.log2 (i + 1) := by
  rw [Nat.log2_def (i + 1)]
  split
  · congr 2
    unfold heapParent
    omega
  · omega

namespace TimeM

/-- Canonical sift-up with one tick per value comparison and one tick per actual swap. -/
def siftUp {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    TimeM (Nat × Nat) (Array α) :=
  if hi : i < a.size then
    if hpos : 0 < i then do
      tick (1, 0)
      let p := heapParent i
      if a[i] < a[p]'(heapParent_lt_size a i hi hpos) then do
        tick (0, 1)
        siftUp (a.swap i p hi (heapParent_lt_size a i hi hpos)) p
      else
        pure a
    else
      pure a
  else
    pure a
termination_by i
decreasing_by
  unfold heapParent
  omega

/-- Erasing the comparison and swap events recovers the canonical returned array. -/
theorem ret_siftUp {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftUp a i).ret = Cslib.Algorithms.Lean.siftUp a i := by
  induction i using Nat.strong_induction_on generalizing a with
  | h i ih =>
    rw [siftUp, Cslib.Algorithms.Lean.siftUp]
    split
    · split
      · dsimp only
        simp only [ret_bind]
        split
        · simpa only [ret_bind, ret_tick] using
            ih (heapParent i) (by unfold heapParent; omega) _
        · rfl
      · rfl
    · rfl

/-- Every sift-up executes at most one value comparison per level above its index. -/
theorem comparisons_siftUp_le_log2 {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) : (siftUp a i).time.1 ≤ Nat.log2 (i + 1) := by
  induction i using Nat.strong_induction_on generalizing a with
  | h i ih =>
    rw [siftUp]
    split
    · split
      · dsimp only
        simp only [time_bind]
        split
        · have hparent : heapParent i < i := by unfold heapParent; omega
          have hb := ih (heapParent i) hparent
            (a.swap i (heapParent i) ‹i < a.size› (heapParent_lt_size a i ‹_› ‹_›))
          have hd := log2_heapParent_add_one i ‹0 < i›
          simp at hb ⊢
          omega
        · have hd := log2_heapParent_add_one i ‹0 < i›
          simp
          omega
      · simp
    · simp

/-- Every sift-up executes at most one swap per level above its index. -/
theorem swaps_siftUp_le_log2 {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) : (siftUp a i).time.2 ≤ Nat.log2 (i + 1) := by
  induction i using Nat.strong_induction_on generalizing a with
  | h i ih =>
    rw [siftUp]
    split
    · split
      · dsimp only
        simp only [time_bind]
        split
        · have hparent : heapParent i < i := by unfold heapParent; omega
          have hb := ih (heapParent i) hparent
            (a.swap i (heapParent i) ‹i < a.size› (heapParent_lt_size a i ‹_› ‹_›))
          have hd := log2_heapParent_add_one i ‹0 < i›
          simp at hb ⊢
          omega
        · simp
      · simp
    · simp

/-- The sum of counted comparisons and swaps is at most twice the index depth. -/
theorem events_siftUp_le_log2 {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftUp a i).time.1 + (siftUp a i).time.2 ≤ 2 * Nat.log2 (i + 1) := by
  have hc := comparisons_siftUp_le_log2 a i
  have hs := swaps_siftUp_le_log2 a i
  omega

/-- Sift-up at the root performs no comparisons or swaps. -/
theorem time_siftUp_zero {α : Type u} [LinearOrder α] (a : Array α) :
    (siftUp a 0).time = (0, 0) := by
  rw [siftUp]
  split <;> rfl

/-- An invalid index performs no comparisons or swaps. -/
theorem time_siftUp_of_size_le {α : Type u} [LinearOrder α] (a : Array α) (i : Nat)
    (hi : a.size ≤ i) : (siftUp a i).time = (0, 0) := by
  rw [siftUp]
  split
  · omega
  · rfl

end TimeM

end Cslib.Algorithms.Lean
