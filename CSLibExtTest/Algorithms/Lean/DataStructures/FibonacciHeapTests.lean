/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.FibonacciHeap.DecreaseKey
public import Mathlib.Data.Nat.Basic

/-!
# Tests for the Fibonacci heap API

Client examples exercise empty heaps, lazy insertion and meld, duplicate
minima, consolidation through repeated deletion, and decrease-key:
invalid addresses, an increase in disguise, a root cut that becomes the
new minimum, a root cut that does not, and a nested cut inside a
consolidated tree.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FibonacciHeapTests

public def heapOfList (values : List Nat) : FibonacciHeap Nat :=
  values.foldl (fun heap value => heap.insert value) FibonacciHeap.empty

public def drainTrees : Nat → List (FibonacciTree Nat) → List Nat
  | 0, _ => []
  | fuel + 1, trees =>
      match FibonacciHeap.deleteMinTrees trees with
      | none => []
      | some (minimum, rest) => minimum :: drainTrees fuel rest

public def drain (fuel : Nat) (heap : FibonacciHeap Nat) : List Nat :=
  drainTrees fuel heap.trees

example : (FibonacciHeap.empty : FibonacciHeap Nat).findMin = none := by
  rfl

example : (FibonacciHeap.empty : FibonacciHeap Nat).deleteMin = none :=
  (FibonacciHeap.deleteMin_eq_none_iff _).mpr rfl

example : (FibonacciHeap.empty : FibonacciHeap Nat).elements = 0 :=
  FibonacciHeap.elements_empty

public def singletonHeap : FibonacciHeap Nat := FibonacciHeap.empty.insert 4

example : singletonHeap.findMin = some 4 := by
  decide

example : drain 2 singletonHeap = [4] := by
  decide

example : (FibonacciHeap.singleton 7 : FibonacciHeap Nat).elements = {7} :=
  FibonacciHeap.elements_singleton 7

public def duplicates : FibonacciHeap Nat := heapOfList [3, 1, 1, 2]

example : duplicates.findMin = some 1 := by
  decide

example : Multiset.count 1 duplicates.elements = 2 := by
  simp [duplicates, heapOfList, FibonacciHeap.elements_insert,
    FibonacciHeap.elements_empty]

example : drain 5 duplicates = [1, 1, 2, 3] := by
  decide

public def melded : FibonacciHeap Nat :=
  (heapOfList [7, 3, 5]).meld (heapOfList [4, 1, 6, 2])

example : melded.findMin = some 1 := by
  decide

example : drain 8 melded = [1, 2, 3, 4, 5, 6, 7] := by
  decide

example {heap₁ heap₂ : FibonacciHeap Nat} :
    (heap₁.meld heap₂).elements = heap₁.elements + heap₂.elements :=
  FibonacciHeap.elements_meld heap₁ heap₂

example (heap : FibonacciHeap Nat) (value : Nat) :
    (heap.insert value).elements = value ::ₘ heap.elements :=
  FibonacciHeap.elements_insert heap value

example (heap : FibonacciHeap Nat) (value : Nat) :
    (heap.insert value).elements.card = heap.elements.card + 1 :=
  FibonacciHeap.card_elements_insert heap value

example {heap : FibonacciHeap Nat} {minimum : Nat}
    {rest : FibonacciHeap Nat} (result : heap.deleteMin = some (minimum, rest)) :
    rest.elements = heap.elements.erase minimum :=
  FibonacciHeap.deleteMin_elements result

example {heap : FibonacciHeap Nat} {minimum value : Nat}
    (result : heap.findMin = some minimum) (member : value ∈ heap.elements) :
    minimum ≤ value :=
  FibonacciHeap.findMin_le result member

example (heap : FibonacciHeap Nat) :
    heap.deleteMin.map (fun result => (result.1, result.2.trees)) =
      FibonacciHeap.deleteMinTrees heap.trees :=
  FibonacciHeap.deleteMin_trees heap

/-- Equal roots retain the left tree as parent when linking. -/
example :
    (FibonacciTree.link (FibonacciTree.singleton 1)
      (FibonacciTree.singleton 1)).root = 1 := by
  decide

example :
    (FibonacciTree.link (FibonacciTree.singleton 2)
      (FibonacciTree.singleton 1)).root = 1 := by
  decide

example (left right : FibonacciTree Nat) :
    (FibonacciTree.link left right).elements = left.elements + right.elements :=
  FibonacciTree.elements_link left right

/-- Heap with root list `[8, 3, 5]` (each a singleton tree), so root
index `0` addresses the tree holding `8`. -/
public def sample : FibonacciHeap Nat := heapOfList [5, 3, 8]

example : sample.findMin = some 3 := by
  decide

example : sample.trees[0]? = some (FibonacciTree.singleton 8) := by
  rfl

/-- A root cut that becomes the new minimum: decreasing `8` to `1`
updates the cached minimum to `min 1 3 = 1`. -/
example : (sample.decreaseKey 0 [] 1).findMin = some 1 := by
  obtain ⟨rest, hcut⟩ := FibonacciForest.cutTreeAt_of_subtreeAt
    (trees := sample.trees) (i := 0) (p := [])
    (t := FibonacciTree.singleton 8) (sub := FibonacciTree.singleton 8)
    (by rfl) (FibonacciTree.subtreeAt_nil _)
  exact FibonacciHeap.decreaseKey_findMin (newKey := 1) (m := 3) hcut (by decide) (by decide)

example : (sample.decreaseKey 0 [] 1).elements = {1, 3, 5} := by
  have h := FibonacciHeap.decreaseKey_elements_of_subtreeAt
    (heap := sample) (i := 0) (p := []) (newKey := 1)
    (t := FibonacciTree.singleton 8) (sub := FibonacciTree.singleton 8)
    (by rfl) (FibonacciTree.subtreeAt_nil _) (by decide)
  rw [h]
  simp [sample, heapOfList, FibonacciHeap.elements_insert,
    FibonacciHeap.elements_empty, FibonacciTree.root_singleton]

/-- A root cut that does not beat the old minimum keeps it: decreasing
`8` to `4` leaves the cached minimum at `3`. -/
example : (sample.decreaseKey 0 [] 4).findMin = some 3 := by
  obtain ⟨rest, hcut⟩ := FibonacciForest.cutTreeAt_of_subtreeAt
    (trees := sample.trees) (i := 0) (p := [])
    (t := FibonacciTree.singleton 8) (sub := FibonacciTree.singleton 8)
    (by rfl) (FibonacciTree.subtreeAt_nil _)
  exact FibonacciHeap.decreaseKey_findMin (newKey := 4) (m := 3) hcut (by decide) (by decide)

example : (sample.decreaseKey 0 [] 1).elements.card = sample.elements.card := by
  obtain ⟨rest, hcut⟩ := FibonacciForest.cutTreeAt_of_subtreeAt
    (trees := sample.trees) (i := 0) (p := [])
    (t := FibonacciTree.singleton 8) (sub := FibonacciTree.singleton 8)
    (by rfl) (FibonacciTree.subtreeAt_nil _)
  exact FibonacciHeap.decreaseKey_card_elements hcut (by decide)

example : FibonacciForest.Valid (sample.decreaseKey 0 [] 1).trees :=
  FibonacciHeap.decreaseKey_valid sample 0 [] 1

/-- An increase in disguise is a no-op. -/
example : sample.decreaseKey 0 [] 99 = sample := by
  obtain ⟨rest, hcut⟩ := FibonacciForest.cutTreeAt_of_subtreeAt
    (trees := sample.trees) (i := 0) (p := [])
    (t := FibonacciTree.singleton 8) (sub := FibonacciTree.singleton 8)
    (by rfl) (FibonacciTree.subtreeAt_nil _)
  exact FibonacciHeap.decreaseKey_eq_self_of_not_le hcut (by
    simp [FibonacciTree.root_singleton])

/-- A root index past the end of the root list is a no-op. -/
example : sample.decreaseKey 10 [] 0 = sample :=
  FibonacciHeap.decreaseKey_eq_self_of_cut_none (by
    have htrees : sample.trees = [FibonacciTree.singleton 8,
      FibonacciTree.singleton 3, FibonacciTree.singleton 5] := rfl
    rw [htrees]
    rfl)

/-- A path that steps into a childless tree is a no-op. -/
example : sample.decreaseKey 0 [0] 0 = sample :=
  FibonacciHeap.decreaseKey_eq_self_of_cut_none (by
    have htrees : sample.trees = [FibonacciTree.singleton 8,
      FibonacciTree.singleton 3, FibonacciTree.singleton 5] := rfl
    rw [htrees]
    rfl)

example {heap : FibonacciHeap Nat} {i : Nat} {p : List Nat} {newKey m : Nat}
    {sub : FibonacciTree Nat} {rest : List (FibonacciTree Nat)}
    (hcut : FibonacciForest.cutTreeAt heap.trees i p = some (sub, rest))
    (hle : newKey ≤ sub.root) (hmin : heap.findMin = some m) :
    (heap.decreaseKey i p newKey).findMin = some (min newKey m) :=
  FibonacciHeap.decreaseKey_findMin hcut hle hmin

/-- A linked tree holding `2` at the root and `3` as its only child. -/
public def linkedTree : FibonacciTree Nat :=
  FibonacciTree.link (FibonacciTree.singleton 2) (FibonacciTree.singleton 3)

public def linkedHeap : FibonacciHeap Nat :=
  ⟨[linkedTree], some 2, by
    intro tree member
    simp only [List.mem_singleton] at member
    subst member
    exact FibonacciTree.Valid.link (FibonacciTree.valid_singleton 2)
      (FibonacciTree.valid_singleton 3), by
    decide⟩

example : FibonacciTree.subtreeAt [0] linkedTree =
    some (FibonacciTree.singleton 3) := by
  rfl

example : linkedHeap.findMin = some 2 := by
  rfl

/-- Decreasing the child `3` through the nested address `0, [0]` cuts
it out of its parent and makes it the minimum. -/
example : (linkedHeap.decreaseKey 0 [0] 0).findMin = some 0 := by
  obtain ⟨rest, hcut⟩ := FibonacciForest.cutTreeAt_of_subtreeAt
    (trees := linkedHeap.trees) (i := 0) (p := [0])
    (t := linkedTree) (sub := FibonacciTree.singleton 3)
    (by rfl) (by rfl)
  exact FibonacciHeap.decreaseKey_findMin hcut (by decide) (by rfl)

example :
    (linkedHeap.decreaseKey 0 [0] 0).elements.card =
      linkedHeap.elements.card := by
  obtain ⟨rest, hcut⟩ := FibonacciForest.cutTreeAt_of_subtreeAt
    (trees := linkedHeap.trees) (i := 0) (p := [0])
    (t := linkedTree) (sub := FibonacciTree.singleton 3)
    (by rfl) (by rfl)
  exact FibonacciHeap.decreaseKey_card_elements hcut (by decide)

#check FibonacciHeap.empty
#check FibonacciHeap.singleton
#check FibonacciHeap.meld
#check FibonacciHeap.insert
#check FibonacciHeap.findMin
#check FibonacciHeap.deleteMin
#check FibonacciHeap.decreaseKey
#check FibonacciHeap.elements_insert
#check FibonacciHeap.findMin_le
#check FibonacciHeap.deleteMin_elements
#check FibonacciHeap.decreaseKey_elements
#check FibonacciHeap.decreaseKey_findMin
#check FibonacciHeap.decreaseKey_valid

#print axioms FibonacciHeap.elements_insert
#print axioms FibonacciHeap.elements_meld
#print axioms FibonacciHeap.findMin_mem
#print axioms FibonacciHeap.findMin_le
#print axioms FibonacciHeap.deleteMin_elements
#print axioms FibonacciHeap.deleteMin_sortedDegrees
#print axioms FibonacciHeap.decreaseKey_elements
#print axioms FibonacciHeap.decreaseKey_card_elements
#print axioms FibonacciHeap.decreaseKey_findMin
#print axioms FibonacciHeap.decreaseKey_valid

end Cslib.Algorithms.Lean.FibonacciHeapTests
