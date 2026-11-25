/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.Delete
public import CSLibExt.Algorithms.Lean.DataStructures.DictionarySpec

/-!
# Red-black-tree adapter for the ordered-set specification

`redBlackSpec` refines `OrderedSetSpec` with red-black trees, using the inorder
traversal as the finite-set abstraction and `RedBlackTree.Valid` as the
representation invariant.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace DictionarySpec

/-- Red-black trees refine the finite ordered-set record, with the inorder
traversal as the finite-set abstraction and `RedBlackTree.Valid` (ordered,
red property, black-balanced, black root) as the invariant. Deletion is the
provider's delete-by-rebuilding. -/
public def redBlackSpec (α : Type u) [LinearOrder α] :
    OrderedSetSpec α (RedBlackTree.Tree α) where
  empty := .empty
  insert := RedBlackTree.insert
  delete := RedBlackTree.delete
  mem := fun x tree => x ∈ tree
  inv := RedBlackTree.Valid
  toFinset := fun tree => (RedBlackTree.inorder tree).toFinset
  inv_empty := by exact RedBlackTree.valid_empty
  inv_insert := by intro x s hs; exact RedBlackTree.valid_insert hs
  inv_delete := by intro x s _hs; exact RedBlackTree.valid_delete
  toFinset_empty := by simp [RedBlackTree.inorder_empty]
  toFinset_insert := by
    intro x s _hs
    apply Finset.ext
    intro y
    simp only [List.mem_toFinset, RedBlackTree.mem_inorder,
      RedBlackTree.mem_insert, Finset.mem_insert]
  toFinset_delete := by
    intro x s hs
    apply Finset.ext
    intro y
    simp only [List.mem_toFinset, RedBlackTree.mem_inorder,
      RedBlackTree.mem_delete hs.1, Finset.mem_erase]
    exact and_comm
  mem_iff_toFinset := by
    intro x s _hs
    simp only [List.mem_toFinset, RedBlackTree.mem_inorder]

end DictionarySpec
end Cslib.Algorithms.Lean
end
