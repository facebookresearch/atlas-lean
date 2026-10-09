/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinomialHeap

/-!
# Tests for the binomial min-heap API

These client examples exercise empty heaps, deterministic links, duplicate minima, meld, and
repeated deletion through the public executable and correctness API.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BinomialHeapTests

public def heapOfList (values : List Nat) : BinomialHeap Nat :=
  values.foldl (fun heap value => heap.insert value) BinomialHeap.empty

public def drainTrees : Nat → List (BinomialTree Nat) → List Nat
  | 0, _ => []
  | fuel + 1, trees =>
      match BinomialHeap.deleteMinTrees trees with
      | none => []
      | some (minimum, rest) => minimum :: drainTrees fuel rest

public def drain (fuel : Nat) (heap : BinomialHeap Nat) : List Nat :=
  drainTrees fuel heap.trees

example : (BinomialHeap.empty : BinomialHeap Nat).findMin = none := by
  rfl

example : (BinomialHeap.empty : BinomialHeap Nat).deleteMin = none := by
  apply (BinomialHeap.deleteMin_eq_none_iff _).mpr
  rfl

public def singleton : BinomialHeap Nat := BinomialHeap.empty.insert 4

example : singleton.findMin = some 4 := by
  simp [singleton, BinomialHeap.findMin, BinomialHeap.insert, BinomialHeap.singleton,
    BinomialHeap.meld, BinomialHeap.empty, BinomialForest.removeMinTree,
    BinomialForest.meldTrees, BinomialTree.singleton, BinomialTree.root]

example : drain 2 singleton = [4] := by
  simp [drain, drainTrees, singleton, BinomialHeap.deleteMinTrees, BinomialHeap.insert,
    BinomialHeap.singleton, BinomialHeap.meld, BinomialHeap.empty,
    BinomialForest.removeMinTree, BinomialForest.meldTrees, BinomialTree.singleton,
    BinomialTree.root, BinomialTree.children]

public def leftTree : BinomialTree Nat :=
  BinomialTree.link (BinomialTree.singleton 0) (BinomialTree.singleton 1)

public def rightTree : BinomialTree Nat :=
  BinomialTree.link (BinomialTree.singleton 0) (BinomialTree.singleton 2)

/-- Equal roots retain the left tree as parent, so the right tree becomes its first child. -/
example : (BinomialTree.link leftTree rightTree).children.head? = some rightTree := by
  rfl

public def duplicates : BinomialHeap Nat := heapOfList [3, 1, 1, 2]

example : Multiset.count 1 duplicates.elements = 2 := by
  simp [duplicates, heapOfList, BinomialHeap.elements, BinomialHeap.insert,
    BinomialHeap.singleton, BinomialHeap.meld, BinomialHeap.empty,
    BinomialForest.elements, BinomialForest.meldTrees, BinomialForest.carry,
    BinomialTree.singleton, BinomialTree.link, BinomialTree.elements,
    BinomialTree.root, BinomialTree.rank, BinomialTree.children]

example : drain 5 duplicates = [1, 1, 2, 3] := by
  simp [drain, drainTrees, duplicates, heapOfList, BinomialHeap.deleteMinTrees,
    BinomialHeap.insert,
    BinomialHeap.singleton, BinomialHeap.meld, BinomialHeap.empty,
    BinomialForest.removeMinTree, BinomialForest.meldTrees, BinomialForest.carry,
    BinomialTree.singleton, BinomialTree.link, BinomialTree.root,
    BinomialTree.rank, BinomialTree.children]

public def melded : BinomialHeap Nat :=
  (heapOfList [7, 3, 5]).meld (heapOfList [4, 1, 6, 2])

example : melded.findMin = some 1 := by
  simp [melded, heapOfList, BinomialHeap.findMin, BinomialHeap.insert,
    BinomialHeap.singleton, BinomialHeap.meld, BinomialHeap.empty,
    BinomialForest.removeMinTree, BinomialForest.meldTrees, BinomialForest.carry,
    BinomialTree.singleton, BinomialTree.link, BinomialTree.root,
    BinomialTree.rank, BinomialTree.children]

example : drain 8 melded = [1, 2, 3, 4, 5, 6, 7] := by
  simp [drain, drainTrees, melded, heapOfList, BinomialHeap.deleteMinTrees,
    BinomialHeap.insert,
    BinomialHeap.singleton, BinomialHeap.meld, BinomialHeap.empty,
    BinomialForest.removeMinTree, BinomialForest.meldTrees, BinomialForest.carry,
    BinomialTree.singleton, BinomialTree.link, BinomialTree.root,
    BinomialTree.rank, BinomialTree.children]

example {heap₁ heap₂ : BinomialHeap Nat} :
    (heap₁.meld heap₂).elements = heap₁.elements + heap₂.elements :=
  heap₁.elements_meld heap₂

example {heap : BinomialHeap Nat} {minimum : Nat} {rest : BinomialHeap Nat}
    (result : heap.deleteMin = some (minimum, rest)) :
    rest.elements = heap.elements.erase minimum :=
  heap.deleteMin_elements result

example (heap : BinomialHeap Nat) :
    heap.deleteMin.map (fun result => (result.1, result.2.trees)) =
      BinomialHeap.deleteMinTrees heap.trees :=
  heap.deleteMin_trees

example {heap : BinomialHeap Nat} {minimum value : Nat}
    (result : heap.findMin = some minimum) (member : value ∈ heap.elements) :
    minimum ≤ value :=
  heap.findMin_le result member

end Cslib.Algorithms.Lean.BinomialHeapTests
