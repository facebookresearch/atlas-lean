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

universe u

example {α : Type u} [LE α] {tree : BinomialTree α} (valid : tree.Valid) :
    tree.rank ≤ Nat.log2 tree.elements.card :=
  valid.rank_le_log2_card

example {α : Type u} [LE α] {trees : List (BinomialTree α)} {tree : BinomialTree α}
    (valid : BinomialForest.Valid trees) (member : tree ∈ trees) :
    tree.rank ≤ Nat.log2 (BinomialForest.elements trees).card :=
  valid.member_rank_le_log2_card member

example {α : Type u} [LE α] {trees : List (BinomialTree α)}
    (valid : BinomialForest.Valid trees) :
    trees.length ≤ Nat.log2 (BinomialForest.elements trees).card + 1 :=
  valid.length_le_log2_card_succ

example {α : Type u} [LE α] {trees : List (BinomialTree α)}
    (valid : BinomialForest.Valid trees) (empty : (BinomialForest.elements trees).card = 0) :
    trees.length = 0 :=
  valid.length_eq_zero_of_card_eq_zero empty

example {α : Type u} [LinearOrder α] (heap : BinomialHeap α) {tree : BinomialTree α}
    (member : tree ∈ heap.trees) : tree.rank ≤ Nat.log2 heap.elements.card :=
  heap.rank_le_log2_card member

example {α : Type u} [LinearOrder α] (heap : BinomialHeap α) :
    heap.trees.length ≤ Nat.log2 heap.elements.card + 1 :=
  heap.length_le_log2_card_succ

example : (BinomialHeap.empty : BinomialHeap Nat).elements.card = 0 := by
  rfl

example : ([] : List (BinomialTree Nat)).length = 0 :=
  BinomialForest.valid_nil.length_eq_zero_of_card_eq_zero rfl

example : (BinomialTree.singleton (0 : Nat)).elements.card = 1 := by
  simp

example : (BinomialTree.link (BinomialTree.singleton (0 : Nat))
    (BinomialTree.singleton 0)).rank = 1 := by
  rfl

example : (BinomialTree.link (BinomialTree.singleton (0 : Nat))
    (BinomialTree.singleton 0)).elements.card = 2 := by
  simp [BinomialTree.elements_link]

example {α : Type u} [LE α] {trees : List (BinomialTree α)} {tree : BinomialTree α}
    (valid : BinomialForest.Valid trees) (member : tree ∈ trees) :
    tree.rank ≤ Nat.log2 (BinomialForest.elements trees).card :=
  @BinomialForest.Valid.member_rank_le_log2_card α _ trees tree valid member

example : (heapOfList [0, 0, 0]).trees.length = 2 := by
  simp [heapOfList, BinomialHeap.insert, BinomialHeap.singleton, BinomialHeap.meld,
    BinomialHeap.empty, BinomialForest.meldTrees, BinomialForest.carry,
    BinomialTree.singleton, BinomialTree.link, BinomialTree.root,
    BinomialTree.rank, BinomialTree.children]

example : (heapOfList [0, 0, 0]).trees.map BinomialTree.rank = [0, 1] := by
  simp [heapOfList, BinomialHeap.insert, BinomialHeap.singleton, BinomialHeap.meld,
    BinomialHeap.empty, BinomialForest.meldTrees, BinomialForest.carry,
    BinomialTree.singleton, BinomialTree.link, BinomialTree.root,
    BinomialTree.rank, BinomialTree.children]

example : (heapOfList [0, 0, 0, 0]).trees.map BinomialTree.rank = [2] := by
  simp [heapOfList, BinomialHeap.insert, BinomialHeap.singleton, BinomialHeap.meld,
    BinomialHeap.empty, BinomialForest.meldTrees, BinomialForest.carry,
    BinomialTree.singleton, BinomialTree.link, BinomialTree.root,
    BinomialTree.rank, BinomialTree.children]

example : (heapOfList [0, 0, 0]).elements.card = 3 := by
  simp only [heapOfList, List.foldl_cons, List.foldl_nil, BinomialHeap.elements_insert,
    Multiset.card_cons]
  rfl

example : (heapOfList [0, 0, 0, 0]).elements.card = 4 := by
  simp only [heapOfList, List.foldl_cons, List.foldl_nil, BinomialHeap.elements_insert,
    Multiset.card_cons]
  rfl

example : ¬ BinomialTree.Valid (BinomialTree.node 1 (0 : Nat) []) := by
  intro valid
  have ranks := valid.children_ranks
  simp [BinomialTree.children, BinomialTree.rank] at ranks

example : ¬ BinomialForest.Valid
    [BinomialTree.singleton (0 : Nat), BinomialTree.singleton 0, BinomialTree.singleton 0] := by
  intro valid
  have ranks := valid.2
  simp at ranks

end Cslib.Algorithms.Lean.BinomialHeapTests
