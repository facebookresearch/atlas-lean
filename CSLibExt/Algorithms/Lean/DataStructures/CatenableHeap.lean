/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Multiset.AddSub

/-!
# Catenable heaps

A catenable heap is a persistent unsorted heap: a container of elements of an arbitrary type `α`,
read as a multiset, with no ordering on the elements. It is built from three constructors: the
empty heap, one element added in front of a heap, and the join of two heaps. The supported
operations are `make`, `insert` and `union`; there is no find-min or delete-min.

`toList` flattens a heap from left to right with an accumulator, so it takes time linear in the
number of nodes; `toList_eq_toListNaive` identifies it with the naive recursive flattening.
`toMultiset` and `size` are read off `toList`.

## Cost model

The operations return `TimeM ℕ`, and the counter is the number of heap nodes the operation
allocates, not CPU time. `make` allocates nothing (cost 0), `insert` allocates one front node
(cost 1), and `union` allocates one join node holding both operands, never traversing either
(cost exactly 1). Flattening and the observers `toList`, `toMultiset` and `size` are not charged.

Provenance: written on 2026-10-20 from a behavioural specification, without consulting the earlier
implementation in this pull request, whose origin could not be established. The representation is
the standard join list (catenation tree).
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean

/-- A persistent unsorted heap over `α`, represented as a join list (catenation tree). -/
inductive CatenableHeap (α : Type u) : Type u where
  /-- The empty heap. -/
  | empty : CatenableHeap α
  /-- The heap with `head` added in front of `tail`. -/
  | cons (head : α) (tail : CatenableHeap α) : CatenableHeap α
  /-- The join of two heaps, with the elements of `left` before those of `right`. -/
  | join (left right : CatenableHeap α) : CatenableHeap α

namespace CatenableHeap

variable {α : Type u}

/-! ### Flattening and observers -/

/-- The naive recursive left-to-right flattening of a heap; the reference for `toList`. -/
def toListNaive : CatenableHeap α → List α
  | empty => []
  | cons head tail => head :: toListNaive tail
  | join left right => toListNaive left ++ toListNaive right

/-- Left-to-right flattening of a heap in front of the accumulator `acc`, visiting each node once.
-/
def toListAux : CatenableHeap α → List α → List α
  | empty, acc => acc
  | cons head tail, acc => head :: toListAux tail acc
  | join left right, acc => toListAux left (toListAux right acc)

/-- The left-to-right list of the elements of a heap, computed with an accumulator. -/
def toList (h : CatenableHeap α) : List α :=
  toListAux h []

/-- The multiset of the elements of a heap. -/
def toMultiset (h : CatenableHeap α) : Multiset α :=
  (toList h : Multiset α)

/-- The number of elements of a heap, counted with multiplicity. -/
def size (h : CatenableHeap α) : ℕ :=
  (toList h).length

/-- The accumulator flattening prepends the naive flattening to the accumulator. -/
theorem toListAux_eq (h : CatenableHeap α) (acc : List α) :
    toListAux h acc = toListNaive h ++ acc := by
  induction h generalizing acc with
  | empty => rfl
  | cons head tail ih => simp [toListAux, toListNaive, ih]
  | join left right ihl ihr => simp [toListAux, toListNaive, ihl, ihr]

/-- The accumulator flattening equals the naive recursive flattening. -/
theorem toList_eq_toListNaive (h : CatenableHeap α) : toList h = toListNaive h := by
  simp [toList, toListAux_eq]

/-- The empty heap flattens to the empty list. -/
@[simp] theorem toList_empty : toList (empty : CatenableHeap α) = [] := rfl

/-- A front node flattens to its element followed by the flattening of its tail. -/
@[simp] theorem toList_cons (head : α) (tail : CatenableHeap α) :
    toList (cons head tail) = head :: toList tail := by
  simp [toList_eq_toListNaive, toListNaive]

/-- A join node flattens to the flattening of its left child followed by that of its right. -/
@[simp] theorem toList_join (left right : CatenableHeap α) :
    toList (join left right) = toList left ++ toList right := by
  simp [toList_eq_toListNaive, toListNaive]

/-- The empty heap has the empty multiset. -/
@[simp] theorem toMultiset_empty : toMultiset (empty : CatenableHeap α) = 0 := rfl

/-- A front node adds its element to the multiset of its tail. -/
@[simp] theorem toMultiset_cons (head : α) (tail : CatenableHeap α) :
    toMultiset (cons head tail) = head ::ₘ toMultiset tail := by
  simp [toMultiset]

/-- The multiset of a join node is the sum of the multisets of its children. -/
@[simp] theorem toMultiset_join (left right : CatenableHeap α) :
    toMultiset (join left right) = toMultiset left + toMultiset right := by
  simp [toMultiset]

/-- The empty heap has size zero. -/
@[simp] theorem size_empty : size (empty : CatenableHeap α) = 0 := rfl

/-- A front node has one more element than its tail. -/
@[simp] theorem size_cons (head : α) (tail : CatenableHeap α) :
    size (cons head tail) = size tail + 1 := by
  simp [size]

/-- The size of a join node is the sum of the sizes of its children. -/
@[simp] theorem size_join (left right : CatenableHeap α) :
    size (join left right) = size left + size right := by
  simp [size]

/-- The size is the cardinality of the multiset of elements. -/
theorem size_eq_card_toMultiset (h : CatenableHeap α) : size h = (toMultiset h).card := by
  simp [size, toMultiset]

/-! ### Timed operations -/

/-- The empty heap; it allocates no node. -/
def make : TimeM ℕ (CatenableHeap α) :=
  pure empty

/-- Add `x` in front of `h`, allocating one front node. -/
def insert (x : α) (h : CatenableHeap α) : TimeM ℕ (CatenableHeap α) := do
  TimeM.tick 1
  pure (cons x h)

/-- Join `h₁` and `h₂`, allocating one join node that holds both operands unchanged. -/
def union (h₁ h₂ : CatenableHeap α) : TimeM ℕ (CatenableHeap α) := do
  TimeM.tick 1
  pure (join h₁ h₂)

/-- `make` returns the empty heap at cost 0. -/
theorem make_eq : (make : TimeM ℕ (CatenableHeap α)) = ⟨empty, 0⟩ := rfl

/-- `insert x h` returns the front node holding `x` and `h` at cost 1. -/
theorem insert_eq (x : α) (h : CatenableHeap α) : insert x h = ⟨cons x h, 1⟩ := rfl

/-- `union h₁ h₂` returns the join node whose children are `h₁` and `h₂`, at cost 1. -/
theorem union_eq (h₁ h₂ : CatenableHeap α) : union h₁ h₂ = ⟨join h₁ h₂, 1⟩ := rfl

/-- The result of `make` is the empty heap. -/
@[simp] theorem ret_make : (make : TimeM ℕ (CatenableHeap α)).ret = empty := rfl

/-- `make` costs 0. -/
@[simp] theorem time_make : (make : TimeM ℕ (CatenableHeap α)).time = 0 := rfl

/-- The result of `insert x h` is the front node holding `x` and `h`. -/
@[simp] theorem ret_insert (x : α) (h : CatenableHeap α) : (insert x h).ret = cons x h := rfl

/-- `insert` costs 1. -/
@[simp] theorem time_insert (x : α) (h : CatenableHeap α) : (insert x h).time = 1 := rfl

/-- The result of `union h₁ h₂` is the join node whose children are `h₁` and `h₂` unchanged. -/
@[simp] theorem ret_union (h₁ h₂ : CatenableHeap α) : (union h₁ h₂).ret = join h₁ h₂ := rfl

/-- `union` costs exactly 1, independently of its operands. -/
@[simp] theorem time_union (h₁ h₂ : CatenableHeap α) : (union h₁ h₂).time = 1 := rfl

/-- `make` flattens to the empty list. -/
theorem toList_make : toList (make : TimeM ℕ (CatenableHeap α)).ret = [] := rfl

/-- `insert x h` flattens to `x` followed by the flattening of `h`. -/
theorem toList_insert (x : α) (h : CatenableHeap α) :
    toList (insert x h).ret = x :: toList h := by
  simp

/-- `union h₁ h₂` flattens to the flattening of `h₁` followed by that of `h₂`. -/
theorem toList_union (h₁ h₂ : CatenableHeap α) :
    toList (union h₁ h₂).ret = toList h₁ ++ toList h₂ := by
  simp

/-- `make` has the empty multiset. -/
theorem toMultiset_make : toMultiset (make : TimeM ℕ (CatenableHeap α)).ret = 0 := rfl

/-- `insert x h` adds `x` to the multiset of `h`. -/
theorem toMultiset_insert (x : α) (h : CatenableHeap α) :
    toMultiset (insert x h).ret = x ::ₘ toMultiset h := by
  simp

/-- The multiset of `union h₁ h₂` is the sum of the multisets of `h₁` and `h₂`. -/
theorem toMultiset_union (h₁ h₂ : CatenableHeap α) :
    toMultiset (union h₁ h₂).ret = toMultiset h₁ + toMultiset h₂ := by
  simp

/-- `make` has size zero. -/
theorem size_make : size (make : TimeM ℕ (CatenableHeap α)).ret = 0 := rfl

/-- `insert` adds one to the size. -/
theorem size_insert (x : α) (h : CatenableHeap α) : size (insert x h).ret = size h + 1 := by
  simp

/-- The size of `union h₁ h₂` is the sum of the sizes of `h₁` and `h₂`. -/
theorem size_union (h₁ h₂ : CatenableHeap α) :
    size (union h₁ h₂).ret = size h₁ + size h₂ := by
  simp

end CatenableHeap

end Cslib.Algorithms.Lean
