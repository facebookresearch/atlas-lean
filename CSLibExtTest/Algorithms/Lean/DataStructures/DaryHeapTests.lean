/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap
public import CSLibExt.Algorithms.Lean.DataStructures.DaryHeap
meta import CSLibExt.Algorithms.Lean.DataStructures.DaryHeap

/-!
# Tests for configurable-arity min-heaps

These client examples cover the normalization policy, arity-dependent layouts,
duplicates, boundary cases, and the public refinement theorems.
-/

public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DaryHeapTests

example : normalizedArity 0 = 2 := by rfl
example : normalizedArity 1 = 2 := by rfl
example : normalizedArity 2 = 2 := by rfl
example : normalizedArity 4 = 4 := by rfl

example (d i k : Nat) (hd : 2 ≤ d) (hk : k < d) :
    daryParent d (daryChild d i k) = i :=
  daryParent_child hd hk

example (d i : Nat) (hd : 2 ≤ d) (hi : 0 < i) :
    daryParent d i < i :=
  daryParent_lt hd hi

example {α : Type} [LinearOrder α] (heap : DaryMinHeap α) (value : α) :
    DaryHeapOrdered heap.arity (heap.push value).data :=
  heap.push_ordered value

example {α : Type} [LinearOrder α] (heap : DaryMinHeap α) (value : α) :
    (heap.push value).elements = value ::ₘ heap.elements :=
  heap.elements_push value

example {α : Type} [LinearOrder α] {heap : DaryMinHeap α} {value : α}
    {rest : DaryMinHeap α} (result : heap.extractMin = some (value, rest)) :
    value ::ₘ rest.elements = heap.elements :=
  heap.extractMin_cons_elements result

example {α : Type} [LinearOrder α] {heap : DaryMinHeap α} {value : α}
    {rest : DaryMinHeap α} (result : heap.extractMin = some (value, rest))
    {other : α} (hother : other ∈ heap.elements) : value ≤ other :=
  heap.extractMin_le result hother

/-- Project an extraction result to the returned value and backing array. -/
def extractedData (heap : DaryMinHeap Nat) : Option (Nat × Nat × Array Nat) :=
  heap.extractMin.map fun result => (result.1, result.2.arity, result.2.data)

example : (DaryMinHeap.empty 0 : DaryMinHeap Nat).arity = 2 := by rfl
example : (DaryMinHeap.empty 1 : DaryMinHeap Nat).arity = 2 := by rfl
example : (DaryMinHeap.empty 4 : DaryMinHeap Nat).arity = 4 := by rfl
example : (DaryMinHeap.empty 3 : DaryMinHeap Nat).data = #[] := by rfl
example : extractedData (DaryMinHeap.empty 3 : DaryMinHeap Nat) = none := by rfl

private def binaryDary : DaryMinHeap Nat :=
  DaryMinHeap.empty 2 |>.push 3 |>.push 1 |>.push 1 |>.push 2

private def binaryLanded : MinHeap Nat :=
  MinHeap.empty.push 3 |>.push 1 |>.push 1 |>.push 2

example : binaryDary.data = binaryLanded.data := by
  simp [binaryDary, binaryLanded, DaryMinHeap.push, DaryMinHeap.empty, normalizedArity,
    darySiftUp, daryParent, MinHeap.push, MinHeap.empty, siftUp, heapParent]

private def ternary : DaryMinHeap Nat :=
  DaryMinHeap.empty 3 |>.push 9 |>.push 4 |>.push 7 |>.push 1 |>.push 6 |>.push 2

example : ternary.arity = 3 := by rfl
example : ternary.data = #[1, 2, 7, 4, 9, 6] := by
  simp [ternary, DaryMinHeap.push, DaryMinHeap.empty, normalizedArity, darySiftUp,
    daryParent]

example : Multiset.count 2 ternary.elements = 1 := by
  simp [ternary, DaryMinHeap.elements, DaryMinHeap.push, DaryMinHeap.empty,
    normalizedArity, darySiftUp, daryParent]

private def quaternary : DaryMinHeap Nat :=
  DaryMinHeap.empty 4 |>.push 8 |>.push 7 |>.push 6 |>.push 5 |>.push 4 |>.push 3
    |>.push 2 |>.push 1

example : quaternary.arity = 4 := by rfl
example : quaternary.data = #[1, 2, 7, 6, 5, 8, 4, 3] := by
  simp [quaternary, DaryMinHeap.push, DaryMinHeap.empty, normalizedArity, darySiftUp,
    daryParent]

private def duplicates : DaryMinHeap Nat :=
  DaryMinHeap.empty 3 |>.push 4 |>.push 1 |>.push 1 |>.push 2 |>.push 1

example : Multiset.count 1 duplicates.elements = 3 := by
  simp [duplicates, DaryMinHeap.elements, DaryMinHeap.push, DaryMinHeap.empty,
    normalizedArity, darySiftUp, daryParent]

example : extractedData (DaryMinHeap.empty 4 |>.push 7) = some (7, 4, #[]) := by
  let heap : DaryMinHeap Nat := DaryMinHeap.empty 4 |>.push 7
  have hdata : heap.data = #[7] := by
    simp [heap, DaryMinHeap.push, DaryMinHeap.empty, normalizedArity, darySiftUp]
  have harity : heap.arity = 4 := by
    simp [heap, DaryMinHeap.push, DaryMinHeap.empty, normalizedArity]
  cases he : heap.extractMin with
  | none =>
      rw [DaryMinHeap.extractMin_eq_none_iff, hdata] at he
      simp at he
  | some result =>
      obtain ⟨x, rest⟩ := result
      have hx : x = 7 := by
        have hmin : heap.min? = some x := by
          unfold DaryMinHeap.extractMin at he
          split at he
          · simp only [Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, -⟩ := he
            simp [DaryMinHeap.min?, hdata]
          · contradiction
        have hmin7 : heap.min? = some 7 := by simp [DaryMinHeap.min?, hdata]
        rw [hmin7] at hmin
        exact Option.some.inj hmin.symm
      have hcons := heap.extractMin_cons_elements he
      have helems : heap.elements = {7} := by
        rw [DaryMinHeap.elements, hdata]
        rfl
      rw [hx, helems] at hcons
      have hrestElems : rest.elements = 0 :=
        (Multiset.cons_inj_right 7).mp hcons
      have hrestData : rest.data = #[] := by
        have hc := rest.card_elements
        rw [hrestElems, Multiset.card_zero] at hc
        exact Array.eq_empty_of_size_eq_zero hc.symm
      have hrestArity : rest.arity = 4 := by
        rw [heap.extractMin_arity he, harity]
      change extractedData heap = some (7, 4, #[])
      unfold extractedData
      rw [he]
      simp [hx, hrestArity, hrestData]

example : (DaryMinHeap.empty 3 |>.push 5 |>.push 1 |>.push 4 |>.push 2).min? = some 1 := by
  simp [DaryMinHeap.min?, DaryMinHeap.push, DaryMinHeap.empty, normalizedArity,
    darySiftUp, daryParent]

example : (DaryMinHeap.empty 3 |>.push 5 |>.push 1 |>.push 4 |>.push 2).extractMin.map
    (fun result => (result.1, result.2.elements)) = some (1, {2, 4, 5}) := by
  let heap : DaryMinHeap Nat :=
    DaryMinHeap.empty 3 |>.push 5 |>.push 1 |>.push 4 |>.push 2
  have hdata : heap.data = #[1, 5, 4, 2] := by
    simp [heap, DaryMinHeap.push, DaryMinHeap.empty, normalizedArity, darySiftUp,
      daryParent]
  cases he : heap.extractMin with
  | none =>
      rw [DaryMinHeap.extractMin_eq_none_iff, hdata] at he
      simp at he
  | some result =>
      obtain ⟨x, rest⟩ := result
      have hx : x = 1 := by
        have hmin : heap.min? = some x := by
          unfold DaryMinHeap.extractMin at he
          split at he
          · simp only [Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, -⟩ := he
            simp [DaryMinHeap.min?, hdata]
          · contradiction
        have hmin1 : heap.min? = some 1 := by simp [DaryMinHeap.min?, hdata]
        rw [hmin1] at hmin
        exact Option.some.inj hmin.symm
      have hcons := heap.extractMin_cons_elements he
      have helems : heap.elements = {1, 2, 4, 5} := by
        rw [DaryMinHeap.elements, hdata]
        decide
      rw [hx, helems] at hcons
      have hrestElems : rest.elements = {2, 4, 5} :=
        (Multiset.cons_inj_right 1).mp hcons
      simp [hx, hrestElems]

-- Bridge to the binary heap at arity two.
example (i : Nat) : heapParent i = daryParent 2 i :=
  heapParent_eq_daryParent_two i

example (i : Nat) : heapLeft i = daryChild 2 i 0 ∧ heapRight i = daryChild 2 i 1 :=
  ⟨heapLeft_eq_daryChild_two i, heapRight_eq_daryChild_two i⟩

example (a : Array Nat) : HeapOrdered a ↔ DaryHeapOrdered 2 a :=
  heapOrdered_iff_daryHeapOrdered_two a

example : siftUp #[1, 5, 3, 7, 0] 4 = darySiftUp #[1, 5, 3, 7, 0] 4 2 le_rfl :=
  siftUp_eq_darySiftUp_two _ _

#guard siftUp #[1, 5, 3, 7, 0] 4 == #[0, 1, 3, 7, 5]

#guard darySiftUp #[1, 5, 3, 7, 0] 4 2 le_rfl == #[0, 1, 3, 7, 5]

example : siftDown #[9, 2, 1, 4, 3] 0 = darySiftDown #[9, 2, 1, 4, 3] 0 2 le_rfl :=
  siftDown_eq_darySiftDown_two _ _

#guard siftDown #[9, 2, 1, 4, 3] 0 == #[1, 2, 9, 4, 3]
#guard darySiftDown #[9, 2, 1, 4, 3] 0 2 le_rfl == #[1, 2, 9, 4, 3]

example : smallerChild #[0, 5, 5] 0 = darySmallestChild #[0, 5, 5] 2 0 :=
  smallerChild_eq_darySmallestChild_two _ _

-- Concrete child selection, including a tie: the first minimal child wins.
example : smallerChild (#[9, 4, 4] : Array Nat) 0 = some 1 := by decide

example : darySmallestChild (#[9, 4, 2] : Array Nat) 2 0 = some 2 := by
  rw [← smallerChild_eq_darySmallestChild_two]
  decide

/-- A binary heap built by four insertions. -/
def binaryHeap : MinHeap Nat :=
  MinHeap.empty.push 4 |>.push 2 |>.push 9 |>.push 1

/-- The same insertions into an arity-two heap. -/
def daryTwoHeap : DaryMinHeap Nat :=
  (DaryMinHeap.empty 2).push 4 |>.push 2 |>.push 9 |>.push 1

example : binaryHeap.toDary = daryTwoHeap := by
  simp only [binaryHeap, daryTwoHeap, MinHeap.toDary_push, MinHeap.toDary_empty]

#guard binaryHeap.toDary.data == #[1, 2, 9, 4]
#guard daryTwoHeap.data == #[1, 2, 9, 4]
#guard (binaryHeap.extractMin.map (fun p => (p.1, p.2.toDary.data))) ==
  (daryTwoHeap.extractMin.map (fun p => (p.1, p.2.data)))

example (h : MinHeap Nat) (x : Nat) : (h.push x).toDary = h.toDary.push x :=
  MinHeap.toDary_push h x

example (h : MinHeap Nat) :
    h.extractMin.map (fun p => (p.1, p.2.toDary)) = h.toDary.extractMin :=
  MinHeap.toDary_extractMin h

example (h : MinHeap Nat) : h.toDary.toBinary h.toDary_arity = h := by
  simp

example (h : DaryMinHeap Nat) (h2 : h.arity = 2) : (h.toBinary h2).toDary = h :=
  DaryMinHeap.toBinary_toDary h h2

example (h : MinHeap Nat) : h.toDary.elements = h.elements := by
  simp

end Cslib.Algorithms.Lean.DaryHeapTests
