/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.DictionarySpec

/-!
# Tests for the red-black-tree ordered-set adapter

The adapter is exercised through the generic `OrderedSetSpec` interface.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.RedBlackDictionarySpecTest

open Cslib.Algorithms.Lean.DictionarySpec

example (x : Nat) (s : RedBlackTree.Tree Nat) (hs : (redBlackSpec Nat).inv s) :
    (redBlackSpec Nat).mem x ((redBlackSpec Nat).insert x s) :=
  (redBlackSpec Nat).mem_insert_self x hs

example (x : Nat) (s : RedBlackTree.Tree Nat) (hs : (redBlackSpec Nat).inv s) :
    ¬ (redBlackSpec Nat).mem x ((redBlackSpec Nat).delete x s) :=
  (redBlackSpec Nat).not_mem_delete_self x hs

example : (redBlackSpec Nat).toFinset (redBlackSpec Nat).empty = ∅ :=
  (redBlackSpec Nat).toFinset_empty

example : (redBlackSpec Nat).toFinset ((redBlackSpec Nat).insert 1 (redBlackSpec Nat).empty) = {1} := by
  rw [(redBlackSpec Nat).toFinset_insert 1 (redBlackSpec Nat).inv_empty,
    (redBlackSpec Nat).toFinset_empty]
  decide

example (s : RedBlackTree.Tree Nat) (hs : (redBlackSpec Nat).inv s) :
    (redBlackSpec Nat).mem 1 s ↔ 1 ∈ (redBlackSpec Nat).toFinset s :=
  (redBlackSpec Nat).mem_iff_toFinset 1 hs

end Cslib.Algorithms.Lean.RedBlackDictionarySpecTest
end
