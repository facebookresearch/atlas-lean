/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap

/-!
# Pairing-heap executable regression tests

Concrete merges, operations, and small time witnesses for the three
pairing-heap variants. All reductions and correctness checks use the
public API and kernel-checked proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.PairingHeapTests

open PairingHeap

/-- The singleton `List2` heap holding `a`. -/
def singleton2 (a : ℕ) : List2.Heap ℕ := some (List2.Hp.mk a [])

example : List2.merge (singleton2 0) (singleton2 1) =
    some (List2.Hp.mk 0 [List2.Hp.mk 1 []]) := by
  simp [singleton2, List2.merge, List2.link]

example : List2.merge (singleton2 1) (singleton2 0) =
    some (List2.Hp.mk 0 [List2.Hp.mk 1 []]) := by
  simp [singleton2, List2.merge, List2.link]

example : List2.msetHeap (List2.merge (singleton2 0) (singleton2 1)) =
    {0} + {1} := by
  rw [List2.mset_merge]
  simp [singleton2, List2.msetHp_eq, List2.msetHpList_nil]

example : List2.invar (List2.merge (singleton2 0) (singleton2 1)) := by
  apply List2.invar_merge
  · simp [singleton2, List2.php_eq, List2.phpList_nil]
  · simp [singleton2, List2.php_eq, List2.phpList_nil]

example : List2.getMin (List2.merge (singleton2 0) (singleton2 1)) = some 0 := by
  simp [singleton2, List2.merge, List2.link, List2.getMin]

example : List2.delMin (List2.merge (singleton2 0) (singleton2 1)) =
    singleton2 1 := by
  simp [singleton2, List2.merge, List2.link, List2.delMin, List2.pass1, List2.pass2]

example : List2.pass1 [List2.Hp.mk 0 [], List2.Hp.mk 1 [], List2.Hp.mk 2 []] =
    [List2.Hp.mk 0 [List2.Hp.mk 1 []], List2.Hp.mk 2 []] := by
  simp [List2.pass1, List2.link]

/-- Exercise 23.1, part 1, at a concrete list. -/
example : List2.mergePairs [List2.Hp.mk 0 [], List2.Hp.mk 1 [], List2.Hp.mk 2 []] =
    List2.pass2 (List2.pass1 [List2.Hp.mk 0 [], List2.Hp.mk 1 [], List2.Hp.mk 2 []]) :=
  List2.mergePairs_eq _

/-- The `Tpass2 (pass1 hs) + Tpass1 hs = |hs| + 2` identity, at a
concrete list. -/
example : List2.Tpass2 (List2.pass1 [List2.Hp.mk 0 [], List2.Hp.mk 1 []]) +
    List2.Tpass1 [List2.Hp.mk 0 [], List2.Hp.mk 1 []] = 4 :=
  List2.Tpass2_pass1_add_Tpass1 _

/-- The singleton `Tree` heap holding `a`. -/
def singletonT (a : ℕ) : Tree.BTree ℕ :=
  Tree.BTree.node Tree.BTree.leaf a Tree.BTree.leaf

example : Tree.merge (singletonT 0) (singletonT 1) =
    Tree.BTree.node (singletonT 1) 0 Tree.BTree.leaf := by
  simp [singletonT, Tree.merge, Tree.link]

example : Tree.merge (singletonT 1) (singletonT 0) =
    Tree.BTree.node (singletonT 1) 0 Tree.BTree.leaf := by
  simp [singletonT, Tree.merge, Tree.link]

example : Tree.msetTree (Tree.merge (singletonT 0) (singletonT 1)) =
    {0} + {1} := by
  have h1 : Tree.isRoot (singletonT 0) := by simp [singletonT, Tree.isRoot_node]
  have h2 : Tree.isRoot (singletonT 1) := by simp [singletonT, Tree.isRoot_node]
  rw [Tree.mset_merge h1 h2]
  simp [singletonT, Tree.msetTree]

example : Tree.isRoot (Tree.merge (singletonT 0) (singletonT 1)) := by
  have h1 : Tree.isRoot (singletonT 0) := by simp [singletonT, Tree.isRoot_node]
  have h2 : Tree.isRoot (singletonT 1) := by simp [singletonT, Tree.isRoot_node]
  exact Tree.isRoot_merge h1 h2

example : Tree.getMin (Tree.merge (singletonT 0) (singletonT 1)) = some 0 := by
  simp [singletonT, Tree.merge, Tree.link, Tree.getMin]

example : Tree.delMin (Tree.merge (singletonT 0) (singletonT 1)) =
    singletonT 1 := by
  simp [singletonT, Tree.merge, Tree.link, Tree.delMin, Tree.pass1, Tree.pass2]

example : Tree.pheap (Tree.merge (singletonT 0) (singletonT 1)) := by
  have h1 : Tree.isRoot (singletonT 0) := by simp [singletonT, Tree.isRoot_node]
  have h2 : Tree.isRoot (singletonT 1) := by simp [singletonT, Tree.isRoot_node]
  have p1 : Tree.pheap (singletonT 0) := Tree.pheap_singleton 0
  have p2 : Tree.pheap (singletonT 1) := Tree.pheap_singleton 1
  exact Tree.pheap_merge h1 h2 p1 p2

/-- The singleton `List1` heap holding `a`. -/
def singleton1 (a : ℕ) : List1.Heap ℕ := List1.Heap.hp a []

example : List1.merge (singleton1 0) (singleton1 1) =
    List1.Heap.hp 0 [List1.Heap.hp 1 []] := by
  simp [singleton1, List1.merge]

example : List1.merge (singleton1 1) (singleton1 0) =
    List1.Heap.hp 0 [List1.Heap.hp 1 []] := by
  simp [singleton1, List1.merge]

example : List1.msetHeap (List1.merge (singleton1 0) (singleton1 1)) =
    {0} + {1} := by
  rw [List1.mset_merge]
  simp [singleton1, List1.msetHeap]

example : List1.pheap (List1.merge (singleton1 0) (singleton1 1)) := by
  apply List1.pheap_merge
  · simp [singleton1, List1.pheap]
  · simp [singleton1, List1.pheap]

example : List1.getMin (List1.merge (singleton1 0) (singleton1 1)) = some 0 := by
  simp [singleton1, List1.merge, List1.getMin]

example : List1.delMin (List1.merge (singleton1 0) (singleton1 1)) =
    singleton1 1 := by
  simp [singleton1, List1.merge, List1.delMin, List1.pass1, List1.pass2]

/-- `pass2 (pass1 hs) = mergePairs hs` for the List1 variant, at a
concrete list. -/
example : List1.pass2 (List1.pass1 [List1.Heap.hp 0 [], List1.Heap.hp 1 [],
      List1.Heap.hp 2 []]) =
    List1.mergePairs [List1.Heap.hp 0 [], List1.Heap.hp 1 [],
      List1.Heap.hp 2 []] :=
  List1.pass12_mergePairs _

end PairingHeapTests

end Cslib.Algorithms.Lean
