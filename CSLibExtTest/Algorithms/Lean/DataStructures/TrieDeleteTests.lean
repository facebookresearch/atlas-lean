/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Trie.Delete

@[expose] public section

/-!
# Tests for trie deletion

These examples exercise empty-key deletion, prefix deletion, shared-prefix retention,
absent keys, pruning, sibling ordering after deletion, and the public `setChild`
specification.
-/

namespace Cslib.Algorithms.Lean.TrieDeleteTests

open Trie

private def orderTrie : Trie Nat String :=
  ((Trie.empty.insert [1] "one").insert [2] "two").insert [2, 3] "two-three"

private theorem orderTrie_valid : orderTrie.Valid :=
  ((Trie.Valid.empty.insert [1] "one").insert [2] "two").insert [2, 3] "two-three"

example : orderTrie.entries =
    [([1], "one"), ([2], "two"), ([2, 3], "two-three")] := by
  decide

-- Deleting below a non-first child preserves the order of surviving entries.
example : (orderTrie.delete [2, 3]).entries =
    [([1], "one"), ([2], "two")] := by
  decide

example : (orderTrie.delete [1]).entries =
    [([2], "two"), ([2, 3], "two-three")] := by
  decide

example : (orderTrie.delete [2, 3]).lookup [2] = some "two" := by
  decide

example : (orderTrie.delete [2, 3]).lookup [2, 3] = none := by
  decide

example : (orderTrie.delete [2, 3]).lookup [1] = some "one" := by
  decide

-- Absent keys: every lookup and the entry list are unchanged.
example : (orderTrie.delete [9]).entries = orderTrie.entries := by
  decide

example : (orderTrie.delete [2, 9]).entries = orderTrie.entries := by
  decide

example : (orderTrie.delete []).entries = orderTrie.entries := by
  decide

example : (orderTrie.delete [1, 2]).lookup [1] = some "one" := by
  decide

-- Empty-key deletion removes only the root value.
private def rootedTrie : Trie Nat String :=
  ((Trie.empty.insert [] "root").insert [1] "one").insert [1, 2] "nested"

example : (rootedTrie.delete []).lookup [] = none := by
  decide

example : (rootedTrie.delete []).entries =
    [([1], "one"), ([1, 2], "nested")] := by
  decide

-- Prefix deletion keeps extensions; deleting an extension keeps its prefix.
example : (rootedTrie.delete [1]).lookup [1, 2] = some "nested" := by
  decide

example : (rootedTrie.delete [1]).lookup [] = some "root" := by
  decide

example : (rootedTrie.delete [1, 2]).lookup [1] = some "one" := by
  decide

example : (rootedTrie.delete [1, 2]).entries =
    [([], "root"), ([1], "one")] := by
  decide

-- Shared-prefix retention.
private def sharedTrie : Trie Nat String :=
  (Trie.empty.insert [1, 2] "left").insert [1, 3] "right"

example : (sharedTrie.delete [1, 2]).lookup [1, 3] = some "right" := by
  decide

example : (sharedTrie.delete [1, 2]).entries = [([1, 3], "right")] := by
  decide

-- Pruning: deleting the only key leaves an empty trie.
example : ((Trie.empty.insert [1, 2] "only" : Trie Nat String).delete [1, 2]).entries =
    [] := by
  decide

example : ((Trie.empty.insert [1, 2] "only" : Trie Nat String).delete [1, 2]) =
    Trie.empty :=
  rfl

example : (sharedTrie.delete [1, 3] |>.delete [1, 2]).entries = [] := by
  decide

-- Deleting from the empty trie and deleting the empty key there.
example : ((Trie.empty : Trie Nat String).delete []).entries = [] := by
  decide

example : ((Trie.empty : Trie Nat String).delete [1]).lookup [1] = none := by
  decide

-- The public `setChild` spec, exercised directly: in-place replacement
-- preserves sibling positions and drops later duplicates at the key.
private def childA : Trie Nat String := Trie.empty.insert [] "a"
private def childB : Trie Nat String := Trie.empty.insert [] "b"
private def childC : Trie Nat String := Trie.empty.insert [] "c"

example : Trie.setChild 2 childC [(1, childA), (2, childB), (3, childA)] =
    [(1, childA), (2, childC), (3, childA)] :=
  rfl

example : Trie.setChild 2 childC [(1, childA), (2, childB), (2, childA), (3, childA)] =
    [(1, childA), (2, childC), (3, childA)] :=
  rfl

example : Trie.setChild 2 Trie.empty [(1, childA), (2, childB), (3, childA)] =
    [(1, childA), (3, childA)] :=
  rfl

example : (Trie.setChild 2 childC [(1, childA), (2, childB)]).lookup 2 = some childC :=
  Trie.lookup_setChild_self 2 childC [(1, childA), (2, childB)] |>.trans rfl

example : (Trie.setChild 2 childC [(1, childA), (2, childB)]).lookup 1 = some childA :=
  Trie.lookup_setChild_of_ne (by decide) childC [(1, childA), (2, childB)] |>.trans rfl

-- Validity and lookup specifications through the public theorem API.
example : (orderTrie.delete [2, 3]).Valid := orderTrie_valid.delete [2, 3]

example : (orderTrie.delete [9]).Valid := orderTrie_valid.delete [9]

example (keys : List Nat) : (orderTrie.delete keys).lookup keys = none :=
  Trie.lookup_delete_self orderTrie keys

example {deletedKeys keys : List Nat} (h : keys ≠ deletedKeys) :
    (orderTrie.delete deletedKeys).lookup keys = orderTrie.lookup keys :=
  Trie.lookup_delete_of_ne orderTrie h

example {value : Option String} {children : List (Nat × Trie Nat String)}
    (h : Trie.Valid (.node value children)) {child : Trie Nat String}
    (hchild : child.Valid) :
    Trie.Valid (.node value (Trie.setChild 2 child children)) :=
  h.setChild hchild

#check Trie.setChild
#check Trie.lookup_setChild_self
#check Trie.lookup_setChild_of_ne
#check Trie.setChild_valid
#check Trie.Valid.setChild
#check Trie.delete
#check Trie.lookup_delete_self
#check Trie.lookup_delete_of_ne
#check Trie.Valid.delete
#check Trie.isEmptyNode_eq_true_iff

#print axioms Trie.lookup_setChild_self
#print axioms Trie.lookup_setChild_of_ne
#print axioms Trie.setChild_valid
#print axioms Trie.Valid.setChild
#print axioms Trie.lookup_delete_self
#print axioms Trie.lookup_delete_of_ne
#print axioms Trie.Valid.delete

end Cslib.Algorithms.Lean.TrieDeleteTests
