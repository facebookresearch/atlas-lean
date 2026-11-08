/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap

/-!
# Decrease-key for binary min-heaps

This file decreases one indexed key and repairs the affected ancestor path.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

private theorem list_set_multiset {α : Type u} [DecidableEq α]
    (xs : List α) (i : Nat) (hi : i < xs.length) (x : α) :
    (↑(xs.set i x) : Multiset α) =
      x ::ₘ (↑xs : Multiset α).erase xs[i] := by
  induction xs generalizing i x with
  | nil => simp at hi
  | cons y ys ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i < ys.length := by simpa using hi
      change y ::ₘ (↑(ys.set i x) : Multiset α) =
        x ::ₘ (y ::ₘ (↑ys : Multiset α)).erase ys[i]
      rw [ih i hi' x]
      rw [Multiset.cons_swap y x]
      by_cases hy : y = ys[i]
      · subst y
        rw [Multiset.erase_cons_head]
        exact congrArg (Multiset.cons x) (Multiset.cons_erase (List.getElem_mem hi'))
      · rw [Multiset.erase_cons_tail _ hy]

private theorem array_set_multiset {α : Type u} [DecidableEq α]
    (a : Array α) (i : Nat) (hi : i < a.size) (x : α) :
    (↑(a.set i x).toList : Multiset α) =
      x ::ₘ (↑a.toList : Multiset α).erase a[i] := by
  change (↑(a.toList.set i x) : Multiset α) =
    x ::ₘ (↑a.toList : Multiset α).erase a.toList[i]
  exact list_set_multiset a.toList i (by simpa using hi) x

/-- Decrease one indexed key and restore heap order along its ancestor path. -/
def MinHeap.decreaseKey {α : Type u} [LinearOrder α]
    (h : MinHeap α) (i : Fin h.data.size) (x : α)
    (hdecrease : x ≤ h.data[i.val]) : MinHeap α where
  data := siftUp (h.data.set i.val x) i.val
  ordered := siftUp_ordered _ _ (by
    refine {
      index_valid := by
        rw [Array.size_set]
        exact i.isLt
      ordered_except := ?_
      parent_below_children := ?_
    }
    · intro j hj hjpos hji
      have hj' : j < h.data.size := by
        rw [Array.size_set] at hj
        exact hj
      by_cases hp : heapParent j = i.val
      · have hold := h.ordered j hj' hjpos
        have hchain : x ≤ h.data[j] := by
          apply hdecrease.trans
          simpa only [hp] using hold
        rw [Array.getElem_set, ite_eq_left hp.symm, Array.getElem_set,
          ite_eq_right (Ne.symm hji)]
        exact hchain
      · have hold := h.ordered j hj' hjpos
        rw [Array.getElem_set, ite_eq_right (Ne.symm hp), Array.getElem_set,
          ite_eq_right (Ne.symm hji)]
        exact hold
    · intro j hj hjpos hp hipos
      have hj' : j < h.data.size := by
        rw [Array.size_set] at hj
        exact hj
      have hparent_ne : heapParent i.val ≠ i.val := by
        unfold heapParent
        omega
      have hji : j ≠ i.val := by
        intro hji
        subst j
        exact hparent_ne hp
      have hparent := h.ordered i.val i.isLt hipos
      have hchild := h.ordered j hj' hjpos
      have hchain :
          h.data[heapParent i.val]'(heapParent_lt_size h.data i.val i.isLt hipos) ≤
            h.data[j] := by
        apply hparent.trans
        simpa only [hp] using hchild
      rw [Array.getElem_set, ite_eq_right (Ne.symm hparent_ne), Array.getElem_set,
        ite_eq_right (Ne.symm hji)]
      exact hchain)

/-- The backing array is the selected replacement followed by canonical sift-up. -/
theorem MinHeap.decreaseKey_data {α : Type u} [LinearOrder α]
    (h : MinHeap α) (i : Fin h.data.size) (x : α)
    (hdecrease : x ≤ h.data[i.val]) :
    (h.decreaseKey i x hdecrease).data =
      siftUp (h.data.set i.val x) i.val := by
  rfl

/-- Decrease-key preserves local heap order. -/
theorem MinHeap.decreaseKey_ordered {α : Type u} [LinearOrder α]
    (h : MinHeap α) (i : Fin h.data.size) (x : α)
    (hdecrease : x ≤ h.data[i.val]) :
    HeapOrdered (h.decreaseKey i x hdecrease).data :=
  (h.decreaseKey i x hdecrease).ordered

/-- Decrease-key preserves the number of stored entries. -/
theorem MinHeap.decreaseKey_size {α : Type u} [LinearOrder α]
    (h : MinHeap α) (i : Fin h.data.size) (x : α)
    (hdecrease : x ≤ h.data[i.val]) :
    (h.decreaseKey i x hdecrease).data.size = h.data.size := by
  rw [h.decreaseKey_data i x hdecrease]
  exact (siftUp_perm (h.data.set i.val x) i.val).size_eq.trans (by simp)

/-- Decrease-key replaces exactly the selected occurrence in the represented multiset. -/
theorem MinHeap.decreaseKey_elements {α : Type u} [LinearOrder α]
    (h : MinHeap α) (i : Fin h.data.size) (x : α)
    (hdecrease : x ≤ h.data[i.val]) :
    (h.decreaseKey i x hdecrease).elements =
      x ::ₘ h.elements.erase (h.data[i.val]) := by
  change (↑(h.decreaseKey i x hdecrease).data.toList : Multiset α) =
    x ::ₘ (↑h.data.toList : Multiset α).erase h.data[i.val]
  rw [h.decreaseKey_data i x hdecrease, siftUp_multiset]
  exact array_set_multiset h.data i.val i.isLt x

end Cslib.Algorithms.Lean
