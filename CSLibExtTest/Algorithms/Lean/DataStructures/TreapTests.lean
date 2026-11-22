/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Treap

set_option autoImplicit false

universe u v

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace TreapTests

open Treap Treap.Tree

private abbrev populated : Tree Nat String :=
  .node (.node .empty 1 "one" 20 .empty) 2 "two" 10
    (.node .empty 3 "three" 30 .empty)

private theorem populated_valid : Valid populated := by
  simp [Valid, Ordered, HeapOrdered, AllNodes]

private abbrev inserted : Tree Nat String := insert 4 "four" 5 populated

private abbrev erased : Tree Nat String := erase 2 populated

example : contents populated = [(1, "one"), (2, "two"), (3, "three")] := by decide
example : keys populated = [1, 2, 3] := by decide
example : lookup 1 populated = some "one" := by decide
example : lookup 9 populated = none := by decide
example : lookupWithCost 3 populated = (some "three", 2) := by decide
example : lookupWithCost 9 populated = (none, 2) := by decide
example : Valid inserted := valid_insert populated_valid
example : contents inserted =
    [(1, "one"), (2, "two"), (3, "three"), (4, "four")] := by
  show contents (insert 4 "four" 5 populated) = _
  rw [contents_insert]
  decide
example : rootPriority inserted = some 5 := by
  simp [Tree.insert, split, merge, rootPriority]
example : lookup 4 inserted = some "four" := lookup_insert_eq populated_valid
example : Valid erased := valid_erase populated_valid
example : contents erased = [(1, "one"), (3, "three")] := by
  show contents (erase 2 populated) = _
  rw [contents_erase]
  decide
example : lookup 2 erased = none := lookup_erase_eq_none populated_valid
example : (keys populated).Nodup := keys_nodup populated_valid.1
example : lookup 3 populated = some "three" ↔
    (3, "three") ∈ contents populated := lookup_contents populated_valid.1
example : (lookupWithCost 3 populated).2 ≤ size populated := lookupWithCost_le_size

private abbrev leftSingleton : Tree Nat String :=
  .node .empty 1 "one" 20 .empty

private abbrev rightSingleton : Tree Nat String :=
  .node .empty 2 "two" 10 .empty

example : HeapOrdered (merge leftSingleton rightSingleton) :=
  heapOrdered_merge _ _ (by simp [HeapOrdered, AllNodes])
    (by simp [HeapOrdered, AllNodes])
example : rootPriority (merge leftSingleton rightSingleton) = some 10 := by
  simp [leftSingleton, rightSingleton, merge, rootPriority]

/- This controlled mutation chooses the larger-priority root for these two
singletons. The negative check is the mutation-test oracle. -/
private abbrev mutatedMerge : Tree Nat String :=
  .node .empty 1 "one" 20 rightSingleton

example : ¬HeapOrdered mutatedMerge := by
  simp [HeapOrdered, AllNodes]
example : ¬Valid mutatedMerge := by
  simp [mutatedMerge, rightSingleton, Valid, HeapOrdered, AllNodes]

/-! Projections to `BinarySearchTree` and `CartesianTree`. -/

example : keyTree populated = .node 2 (.node 1 .nil .nil) (.node 3 .nil .nil) := rfl
example : priorityTree populated = .node 10 (.node 20 .nil .nil) (.node 30 .nil .nil) := rfl
example : keyTree leftSingleton = .node 1 .nil .nil := by simp [leftSingleton]
example : priorityTree leftSingleton = .node 20 .nil .nil := by simp [leftSingleton]
example : BinarySearchTree.Ordered (keyTree populated) :=
  ordered_keyTree.mp populated_valid.1
example : CartesianTree.HeapOrdered (priorityTree populated) :=
  heapOrdered_priorityTree.mp populated_valid.2
example : ¬CartesianTree.HeapOrdered (priorityTree mutatedMerge) := fun hHeap =>
  (show ¬HeapOrdered mutatedMerge by simp [HeapOrdered, AllNodes])
    (heapOrdered_priorityTree.mpr hHeap)
example : (2 : Nat) ∈ keyTree populated := mem_keyTree.mp (Or.inr (Or.inl rfl))
example : BinarySearchTree.All (· < 4) (keyTree populated) :=
  allNodes_keyTree.mp (by simp [AllNodes])
example : BinarySearchTree.All (10 ≤ ·) (priorityTree populated) :=
  allNodes_priorityTree.mp (by simp [AllNodes])

/- Both bridges hold in arbitrary universes. -/
example {κ : Type u} {ν : Type v} [LT κ] (tree : Tree κ ν) :
    Ordered tree ↔ BinarySearchTree.Ordered (keyTree tree) :=
  ordered_keyTree
example {κ : Type u} {ν : Type v} (tree : Tree κ ν) :
    HeapOrdered tree ↔ CartesianTree.HeapOrdered (priorityTree tree) :=
  heapOrdered_priorityTree

/-! Lookup frame lemmas. -/

example : lookup 1 inserted = lookup 1 populated :=
  lookup_insert_ne populated_valid.1 (by decide)
example : lookup 3 erased = some "three" :=
  (lookup_erase_ne populated_valid.1 (by decide)).trans (by decide)
example {κ : Type u} {ν : Type v} [LinearOrder κ] {query key : κ} {value : ν}
    {priority : Nat} {tree : Tree κ ν} (hOrdered : Ordered tree) (hNe : query ≠ key) :
    lookup query (insert key value priority tree) = lookup query tree ∧
      lookup query (erase key tree) = lookup query tree :=
  ⟨lookup_insert_ne hOrdered hNe, lookup_erase_ne hOrdered hNe⟩

/- Edge cases: replacing an existing key, querying an absent key, erasing a missing
key, and the empty tree in arbitrary universes. -/
example : lookup 1 (insert 2 "replacement" 0 populated) = lookup 1 populated :=
  lookup_insert_ne populated_valid.1 (by decide)
example : lookup 9 (insert 2 "replacement" 50 populated) = lookup 9 populated :=
  lookup_insert_ne populated_valid.1 (by decide)
example : lookup 9 (erase 4 populated) = lookup 9 populated :=
  lookup_erase_ne populated_valid.1 (by decide)
example {κ : Type u} {ν : Type v} [LinearOrder κ] (query key : κ) (value : ν)
    (priority : Nat) (hNe : query ≠ key) :
    lookup query (insert key value priority (.empty : Tree κ ν)) = none :=
  lookup_insert_ne (by trivial) hNe
example {κ : Type u} {ν : Type v} [LinearOrder κ] (query key : κ) (hNe : query ≠ key) :
    lookup query (erase key (.empty : Tree κ ν)) = none :=
  lookup_erase_ne (by trivial) hNe

/- The frame lemmas need key order but not heap order: this tree is ordered
and violates the heap invariant. -/
private abbrev orderedNotHeap : Tree Nat String :=
  .node .empty 1 "one" 20 (.node .empty 2 "two" 10 .empty)

example : ¬HeapOrdered orderedNotHeap := by simp [HeapOrdered, AllNodes]
example : lookup 2 (insert 3 "three" 5 orderedNotHeap) = some "two" :=
  (lookup_insert_ne (by simp [Ordered, AllNodes]) (by decide)).trans (by decide)
example : Ordered (insert 3 "three" 5 orderedNotHeap) :=
  ordered_insert (by simp [Ordered, AllNodes])
example : Ordered (erase 1 orderedNotHeap) :=
  ordered_erase (by simp [Ordered, AllNodes])

/- Key order cannot be dropped: in this unordered tree, lookup misses key 5,
and removing or replacing key 3 exposes it. -/
private abbrev unordered : Tree Nat String :=
  .node (.node .empty 5 "five" 1 .empty) 3 "three" 0 .empty

example : ¬Ordered unordered := by simp [Ordered, AllNodes]
example : lookup 5 unordered = none := by decide
example : lookup 5 (erase 3 unordered) = some "five" := by
  simp [erase, split, merge, lookup]
example : lookup 5 (Tree.insert 3 "new" 2 unordered) = some "five" := by
  simp [Tree.insert, split, merge, lookup]

#check Tree
#check SplitResult
#check lookup
#check lookupWithCost
#check merge
#check split
#check Treap.Tree.insert
#check erase
#check Valid
#check contents
#check valid_insert
#check valid_erase
#check lookup_contents
#check lookupWithCost_le_size
#check keyTree
#check priorityTree
#check ordered_keyTree
#check heapOrdered_priorityTree
#check lookup_insert_ne
#check lookup_erase_ne

#print axioms allNodes_iff_forall_mem
#print axioms memKey_of_memNode
#print axioms mem_contents
#print axioms key_mem_contents
#print axioms allNodes_key_iff
#print axioms mem_keys
#print axioms ordered_keys
#print axioms keys_nodup
#print axioms lookup_eq_some_iff
#print axioms lookup_contents
#print axioms lookupWithCost_result
#print axioms lookupWithCost_le_size
#print axioms heap_root_min
#print axioms memKey_merge
#print axioms contents_merge
#print axioms ordered_merge
#print axioms heapOrdered_merge
#print axioms ordered_split
#print axioms heapOrdered_split
#print axioms split_bounds
#print axioms valid_split
#print axioms valid_merge
#print axioms valid_insert
#print axioms valid_erase
#print axioms contents_split
#print axioms contents_insert
#print axioms contents_erase
#print axioms lookup_insert_eq
#print axioms lookup_erase_eq_none
#print axioms ordered_insert
#print axioms ordered_erase
#print axioms lookup_insert_ne
#print axioms lookup_erase_ne
#print axioms keyTree_node
#print axioms priorityTree_node
#print axioms allNodes_keyTree
#print axioms allNodes_priorityTree
#print axioms mem_keyTree
#print axioms ordered_keyTree
#print axioms heapOrdered_priorityTree

end TreapTests
end Cslib.Algorithms.Lean
