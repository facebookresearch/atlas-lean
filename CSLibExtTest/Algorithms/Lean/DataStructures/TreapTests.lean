/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Treap

set_option autoImplicit false

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

end TreapTests
end Cslib.Algorithms.Lean
