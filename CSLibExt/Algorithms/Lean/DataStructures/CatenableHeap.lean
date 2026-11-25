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

/-- **Catenable heap.** A catenable heap over a type $\alpha$ is a persistent unsorted heap,
represented as a join list (catenation tree): it is either the empty heap, an element of $\alpha$
added in front of a catenable heap, or the join of two catenable heaps. -/
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

/-- **Naive flattening of a catenable heap.** The naive flattening of a catenable heap is defined
by recursion: the empty heap flattens to the empty list, the heap with an element $x$ added in
front of a heap $t$ flattens to $x$ followed by the naive flattening of $t$, and the join of
heaps $l$ and $r$ flattens to the naive flattening of $l$ followed by that of $r$.

It is the reference against which the accumulating flattening is checked. -/
def toListNaive : CatenableHeap α → List α
  | empty => []
  | cons head tail => head :: toListNaive tail
  | join left right => toListNaive left ++ toListNaive right

/-- **Accumulating flattening of a catenable heap.** Given a catenable heap $h$ and a list $s$, the
accumulating flattening of $h$ onto $s$ is defined by recursion on $h$: for the empty heap it is
$s$; for the heap with an element $x$ added in front of a heap $t$ it is $x$ followed by the
accumulating flattening of $t$ onto $s$; for the join of heaps $l$ and $r$ it is the accumulating
flattening of $l$ onto the accumulating flattening of $r$ onto $s$.

Each node of $h$ is visited once.
-/
def toListAux : CatenableHeap α → List α → List α
  | empty, acc => acc
  | cons head tail, acc => head :: toListAux tail acc
  | join left right, acc => toListAux left (toListAux right acc)

/-- **Flattening of a catenable heap.** The flattening of a catenable heap $h$ is the list of its
elements from left to right, computed as the accumulating flattening of $h$ onto the empty list.
-/
def toList (h : CatenableHeap α) : List α :=
  toListAux h []

/-- **Multiset of elements of a catenable heap.** The multiset of elements of a catenable heap $h$
is the multiset of the entries of the left-to-right list of elements of $h$. -/
def toMultiset (h : CatenableHeap α) : Multiset α :=
  (toList h : Multiset α)

/-- **Size of a catenable heap.** The size of a catenable heap is the length of its left-to-right
list of elements, that is, the number of its elements counted with multiplicity. -/
def size (h : CatenableHeap α) : ℕ :=
  (toList h).length

/-- **Accumulator flattening of a catenable heap.** For every catenable heap $h$ and list $a$,
flattening $h$ from left to right in front of the accumulator $a$ gives the naive left-to-right
flattening of $h$ followed by $a$. -/
theorem toListAux_eq (h : CatenableHeap α) (acc : List α) :
    toListAux h acc = toListNaive h ++ acc := by
  induction h generalizing acc with
  | empty => rfl
  | cons head tail ih => simp [toListAux, toListNaive, ih]
  | join left right ihl ihr => simp [toListAux, toListNaive, ihl, ihr]

/-- **Flattening of a catenable heap equals its naive flattening.** For every catenable heap $h$,
the flattening of $h$ equals the naive flattening of $h$. -/
theorem toList_eq_toListNaive (h : CatenableHeap α) : toList h = toListNaive h := by
  simp [toList, toListAux_eq]

/-- **Flattening the empty catenable heap.** The flattening of the empty catenable heap is the
empty list. -/
@[simp] theorem toList_empty : toList (empty : CatenableHeap α) = [] := rfl

/-- **Flattening a front node of a catenable heap.** For an element $x$ and a catenable heap $t$,
the flattening of the heap with $x$ added in front of $t$ is $x$ followed by the flattening of
$t$. -/
@[simp] theorem toList_cons (head : α) (tail : CatenableHeap α) :
    toList (cons head tail) = head :: toList tail := by
  simp [toList_eq_toListNaive, toListNaive]

/-- **Flattening a join of catenable heaps.** For catenable heaps $l$ and $r$, the flattening of
the join of $l$ and $r$ is the flattening of $l$ followed by the flattening of $r$. -/
@[simp] theorem toList_join (left right : CatenableHeap α) :
    toList (join left right) = toList left ++ toList right := by
  simp [toList_eq_toListNaive, toListNaive]

/-- **The empty catenable heap has no elements.** The multiset of elements of the empty catenable
heap is the empty multiset. -/
@[simp] theorem toMultiset_empty : toMultiset (empty : CatenableHeap α) = 0 := rfl

/-- **Multiset of a front node.** For every element $a$ and every catenable heap $t$, the multiset
of elements of the heap obtained by adding $a$ in front of $t$ is the multiset of elements of $t$
with one more copy of $a$. -/
@[simp] theorem toMultiset_cons (head : α) (tail : CatenableHeap α) :
    toMultiset (cons head tail) = head ::ₘ toMultiset tail := by
  simp [toMultiset]

/-- **Multiset of a join node.** For all catenable heaps $L$ and $R$, the multiset of elements of
the join node with left child $L$ and right child $R$ is the multiset sum of the multisets of
elements of $L$ and $R$ (multiplicities add). -/
@[simp] theorem toMultiset_join (left right : CatenableHeap α) :
    toMultiset (join left right) = toMultiset left + toMultiset right := by
  simp [toMultiset]

/-- **The empty catenable heap has size zero.** The empty catenable heap has size $0$. -/
@[simp] theorem size_empty : size (empty : CatenableHeap α) = 0 := rfl

/-- **Size of a heap with an element added in front.** For every element $a$ and catenable heap
$t$, the size of the heap obtained by adding $a$ in front of $t$ is the size of $t$ plus one. -/
@[simp] theorem size_cons (head : α) (tail : CatenableHeap α) :
    size (cons head tail) = size tail + 1 := by
  simp [size]

/-- **Size of a catenable heap join.** For catenable heaps $\ell$ and $r$, the size of the join
node with left child $\ell$ and right child $r$ is the size of $\ell$ plus the size of $r$. -/
@[simp] theorem size_join (left right : CatenableHeap α) :
    size (join left right) = size left + size right := by
  simp [size]

/-- **Size of a catenable heap as a multiset cardinality.** For every catenable heap $h$, the size
of $h$ equals the cardinality of the multiset of its elements. -/
theorem size_eq_card_toMultiset (h : CatenableHeap α) : size h = (toMultiset h).card := by
  simp [size, toMultiset]

/-! ### Timed operations -/

/-- **Creating an empty catenable heap.** The operation that creates a catenable heap returns the
empty heap and charges cost $0$, since it allocates no node. -/
def make : TimeM ℕ (CatenableHeap α) :=
  pure empty

/-- **Insertion into a catenable heap.** For an element $x$ and a catenable heap $h$, inserting
$x$ into $h$ returns the heap with $x$ added in front of $h$ and charges cost $1$, for the one
front node it allocates. -/
def insert (x : α) (h : CatenableHeap α) : TimeM ℕ (CatenableHeap α) := do
  TimeM.tick 1
  pure (cons x h)

/-- **Union of catenable heaps.** The union of catenable heaps $h_1$ and $h_2$ allocates one join
node, at cost $1$, and returns that join node, whose left child is $h_1$ and whose right child is
$h_2$; neither operand is traversed or changed. -/
def union (h₁ h₂ : CatenableHeap α) : TimeM ℕ (CatenableHeap α) := do
  TimeM.tick 1
  pure (join h₁ h₂)

/-- **Cost and result of creating a catenable heap.** Creating a catenable heap returns the empty
heap, at cost $0$. -/
theorem make_eq : (make : TimeM ℕ (CatenableHeap α)) = ⟨empty, 0⟩ := rfl

/-- **Cost and result of insertion into a catenable heap.** For every element $x$ and catenable
heap $h$, inserting $x$ into $h$ returns the heap with $x$ added in front of $h$, at cost
exactly $1$. -/
theorem insert_eq (x : α) (h : CatenableHeap α) : insert x h = ⟨cons x h, 1⟩ := rfl

/-- **Union allocates one join node.** For all catenable heaps $h_1$ and $h_2$, the union of $h_1$
and $h_2$ returns the join node whose left child is $h_1$ and whose right child is $h_2$, at
cost $1$. -/
theorem union_eq (h₁ h₂ : CatenableHeap α) : union h₁ h₂ = ⟨join h₁ h₂, 1⟩ := rfl

/-- **Result of creating a catenable heap.** The heap returned by the operation that creates a
catenable heap is the empty heap. -/
@[simp] theorem ret_make : (make : TimeM ℕ (CatenableHeap α)).ret = empty := rfl

/-- **Creating an empty catenable heap costs nothing.** The operation that creates an empty
catenable heap has time cost $0$. -/
@[simp] theorem time_make : (make : TimeM ℕ (CatenableHeap α)).time = 0 := rfl

/-- **Result of insertion into a catenable heap.** For every element $x$ and catenable heap $h$,
the heap returned by inserting $x$ into $h$ is the heap with $x$ added in front of $h$. -/
@[simp] theorem ret_insert (x : α) (h : CatenableHeap α) : (insert x h).ret = cons x h := rfl

/-- **Insertion into a catenable heap costs one.** For every element $x$ and catenable heap $h$,
inserting $x$ into $h$ has time cost exactly $1$. -/
@[simp] theorem time_insert (x : α) (h : CatenableHeap α) : (insert x h).time = 1 := rfl

/-- **Result of the union of catenable heaps.** For all catenable heaps $h_1$ and $h_2$, the heap
returned by their union is the join of $h_1$ and $h_2$, with $h_1$ as left child and $h_2$ as
right child, both unchanged. -/
@[simp] theorem ret_union (h₁ h₂ : CatenableHeap α) : (union h₁ h₂).ret = join h₁ h₂ := rfl

/-- **Union of catenable heaps costs one.** For all catenable heaps $h_1$ and $h_2$, the union of
$h_1$ and $h_2$ has time cost exactly $1$, independently of $h_1$ and $h_2$. -/
@[simp] theorem time_union (h₁ h₂ : CatenableHeap α) : (union h₁ h₂).time = 1 := rfl

/-- **A newly created catenable heap flattens to the empty list.** The flattening of the heap
returned by the operation that creates a catenable heap is the empty list. -/
theorem toList_make : toList (make : TimeM ℕ (CatenableHeap α)).ret = [] := rfl

/-- **Flattening after insertion into a catenable heap.** For an element $x$ and a catenable heap
$h$, the flattening of the heap returned by inserting $x$ into $h$ is $x$ followed by the
flattening of $h$. -/
theorem toList_insert (x : α) (h : CatenableHeap α) :
    toList (insert x h).ret = x :: toList h := by
  simp

/-- **Flattening a union of catenable heaps.** For catenable heaps $h_1$ and $h_2$, the flattening
of the heap returned by the union of $h_1$ and $h_2$ is the flattening of $h_1$ followed by the
flattening of $h_2$. -/
theorem toList_union (h₁ h₂ : CatenableHeap α) :
    toList (union h₁ h₂).ret = toList h₁ ++ toList h₂ := by
  simp

/-- **A newly made catenable heap has no elements.** The multiset of elements of the heap returned
by the make operation is the empty multiset. -/
theorem toMultiset_make : toMultiset (make : TimeM ℕ (CatenableHeap α)).ret = 0 := rfl

/-- **Insertion adds one copy of the element.** For every element $x$ and every catenable heap $h$,
the multiset of elements of the heap returned by inserting $x$ into $h$ is the multiset of
elements of $h$ with one more copy of $x$. -/
theorem toMultiset_insert (x : α) (h : CatenableHeap α) :
    toMultiset (insert x h).ret = x ::ₘ toMultiset h := by
  simp

/-- **Union adds the multisets of elements.** For all catenable heaps $h_1$ and $h_2$, the multiset
of elements of the heap returned by the union of $h_1$ and $h_2$ is the multiset sum of the
multisets of elements of $h_1$ and $h_2$ (multiplicities add). -/
theorem toMultiset_union (h₁ h₂ : CatenableHeap α) :
    toMultiset (union h₁ h₂).ret = toMultiset h₁ + toMultiset h₂ := by
  simp

/-- **A newly made catenable heap has size zero.** The heap returned by the operation that
creates an empty catenable heap has size $0$. -/
theorem size_make : size (make : TimeM ℕ (CatenableHeap α)).ret = 0 := rfl

/-- **Insertion into a catenable heap increases its size by one.** For every element $x$ and
catenable heap $h$, the heap returned by inserting $x$ into $h$ has size one more than the size
of $h$. -/
theorem size_insert (x : α) (h : CatenableHeap α) : size (insert x h).ret = size h + 1 := by
  simp

/-- **Size of a catenable heap union.** For catenable heaps $h_1$ and $h_2$, the heap returned by
the union of $h_1$ and $h_2$ has size equal to the size of $h_1$ plus the size of $h_2$. -/
theorem size_union (h₁ h₂ : CatenableHeap α) :
    size (union h₁ h₂).ret = size h₁ + size h₂ := by
  simp

end CatenableHeap

end Cslib.Algorithms.Lean
