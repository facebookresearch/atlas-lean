/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.AvlTree.DictionarySpec

/-!
# Tests for the AVL-tree ordered-set adapter

The adapter is exercised through the generic `OrderedSetSpec` interface.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.AvlDictionarySpecTest

open Cslib.Algorithms.Lean.DictionarySpec

example (x : Nat) (s : AvlTree.Tree Nat) (hs : (avlSpec Nat).inv s) :
    (avlSpec Nat).mem x ((avlSpec Nat).insert x s) :=
  (avlSpec Nat).mem_insert_self x hs

example (x : Nat) (s : AvlTree.Tree Nat) (hs : (avlSpec Nat).inv s) :
    ¬ (avlSpec Nat).mem x ((avlSpec Nat).delete x s) :=
  (avlSpec Nat).not_mem_delete_self x hs

example : (avlSpec Nat).toFinset (avlSpec Nat).empty = ∅ :=
  (avlSpec Nat).toFinset_empty

example : (avlSpec Nat).toFinset ((avlSpec Nat).insert 1 (avlSpec Nat).empty) = {1} := by
  rw [(avlSpec Nat).toFinset_insert 1 (avlSpec Nat).inv_empty,
    (avlSpec Nat).toFinset_empty]
  decide

example (s : AvlTree.Tree Nat) (hs : (avlSpec Nat).inv s) :
    (avlSpec Nat).mem 1 s ↔ 1 ∈ (avlSpec Nat).toFinset s :=
  (avlSpec Nat).mem_iff_toFinset 1 hs

end Cslib.Algorithms.Lean.AvlDictionarySpecTest
end
