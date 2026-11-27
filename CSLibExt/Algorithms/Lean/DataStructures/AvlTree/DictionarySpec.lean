/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.AvlTree.Delete
public import CSLibExt.Algorithms.Lean.DataStructures.DictionarySpec

/-!
# AVL-tree adapter for the ordered-set specification

`avlSpec` refines `OrderedSetSpec` with AVL trees, using the inorder
traversal as the finite-set abstraction and `AvlTree.Valid` as the
representation invariant.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace DictionarySpec

/-- AVL trees refine the finite ordered-set record, with the inorder
traversal as the finite-set abstraction and `AvlTree.Valid` (ordered,
correct height caches, balanced) as the invariant. -/
public def avlSpec (α : Type u) [LinearOrder α] :
    OrderedSetSpec α (AvlTree.Tree α) where
  empty := .empty
  insert := AvlTree.insert
  delete := AvlTree.delete
  mem := fun x tree => x ∈ tree
  inv := AvlTree.Valid
  toFinset := fun tree => (AvlTree.inorder tree).toFinset
  inv_empty := by exact AvlTree.valid_empty
  inv_insert := by intro x s hs; exact AvlTree.valid_insert hs
  inv_delete := by intro x s hs; exact AvlTree.valid_delete hs
  toFinset_empty := by simp [AvlTree.inorder_empty]
  toFinset_insert := by
    intro x s _hs
    apply Finset.ext
    intro y
    simp only [List.mem_toFinset, AvlTree.mem_inorder,
      AvlTree.mem_insert, Finset.mem_insert]
  toFinset_delete := by
    intro x s hs
    apply Finset.ext
    intro y
    simp only [List.mem_toFinset, AvlTree.mem_inorder, AvlTree.delete,
      AvlTree.mem_erase hs.1, Finset.mem_erase]
    exact and_comm
  mem_iff_toFinset := by
    intro x s _hs
    simp only [List.mem_toFinset, AvlTree.mem_inorder]

end DictionarySpec
end Cslib.Algorithms.Lean
end
