/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree.Delete
public import CSLibExt.Algorithms.Lean.DataStructures.OrderStatisticTree

/-!
# Order-statistic tree deletion

Key deletion for the size-augmented tree of `OrderStatisticTree.lean`. The name
`erase` already denotes cache-stripping there, so deletion is called `delete`.

Deletion follows the search path, rebuilding ancestors with the cache-repairing
constructor `node`; at the deleted node the two subtrees are combined with
`merge`. Apart from the caches, this is binary search tree deletion: for all
trees, ordered or not and with correct caches or not, erasing the caches turns
`merge` into `BinarySearchTree.join` (`erase_merge`) and `delete` into
`BinarySearchTree.delete` (`erase_delete`). The order, membership, and traversal
theorems below are derived from the `BinarySearchTree` results through these two
equations. Rank and select after deletion use the cache refinements of the parent
module.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace OrderStatisticTree

universe u

/--
Merge two trees in which every key of the first is smaller than every key of
the second, repairing every rebuilt cache. For any two trees, erasing the caches
of the result gives `BinarySearchTree.join` of the erased trees (`erase_merge`);
`ordered_merge` shows that the result is ordered when both trees are ordered and
separated in this way.
-/
public def merge {α : Type u} : Tree α → Tree α → Tree α
  | .nil, right => right
  | .node entry left right, other => node entry.key left (merge right other)

/-- Delete a key, leaving the tree unchanged in membership when it is absent. -/
public def delete {α : Type u} [LinearOrder α] (key : α) : Tree α → Tree α
  | .nil => .nil
  | .node entry left right =>
      if key < entry.key then node entry.key (delete key left) right
      else if entry.key < key then node entry.key left (delete key right)
      else merge left right

/-- Merging preserves correct caches. -/
public theorem cacheCorrect_merge {α : Type u} {left right : Tree α}
    (hLeft : CacheCorrect left) (hRight : CacheCorrect right) :
    CacheCorrect (merge left right) := by
  induction left generalizing right with
  | nil => exact hRight
  | node entry subLeft subRight _ihLeft ihRight =>
    rcases hLeft with ⟨hSubLeft, hSubRight, -⟩
    simp [merge, cacheCorrect_node hSubLeft (ihRight hSubRight hRight)]

/-- Deletion preserves correct caches. -/
public theorem cacheCorrect_delete {α : Type u} [LinearOrder α] {key : α}
    {tree : Tree α} (hTree : CacheCorrect tree) : CacheCorrect (delete key tree) := by
  induction tree with
  | nil => trivial
  | node entry left right ihLeft ihRight =>
    rcases hTree with ⟨hLeft, hRight, -⟩
    by_cases hKeyLeft : key < entry.key
    · simp [delete, hKeyLeft, cacheCorrect_node (ihLeft hLeft) hRight]
    · by_cases hKeyRight : entry.key < key
      · simp [delete, hKeyLeft, hKeyRight, cacheCorrect_node hLeft (ihRight hRight)]
      · have hDelete : delete key (.node entry left right) = merge left right := by
          simp [delete, hKeyLeft, hKeyRight]
        rw [hDelete]
        exact cacheCorrect_merge hLeft hRight

private theorem erase_node' {α : Type u} (key : α) (left right : Tree α) :
    erase (node key left right) = .node key (erase left) (erase right) :=
  rfl

/--
Erasing the caches of a merge gives `BinarySearchTree.join` of the erased trees,
for any two trees, with no ordering, separation, or cache hypothesis.
-/
public theorem erase_merge {α : Type u} (left right : Tree α) :
    erase (merge left right) = BinarySearchTree.join (erase left) (erase right) := by
  induction left generalizing right with
  | nil => rfl
  | node entry subLeft subRight _ihLeft ihRight =>
    simp [merge, BinarySearchTree.join, erase, erase_node', ihRight]

/--
Erasing after deletion agrees with deletion in the underlying binary search tree,
for every tree, ordered or not and with correct caches or not.
-/
public theorem erase_delete {α : Type u} [LinearOrder α] (key : α) (tree : Tree α) :
    erase (delete key tree) = BinarySearchTree.delete key (erase tree) := by
  induction tree with
  | nil => rfl
  | node entry left right ihLeft ihRight =>
    simp only [delete, BinarySearchTree.delete, erase]
    by_cases hLeft : key < entry.key
    · simp [hLeft, erase_node', ihLeft]
    · by_cases hRight : entry.key < key
      · simp [hLeft, hRight, erase_node', ihRight]
      · simp [hLeft, hRight, erase_merge]

/-- Merging separated trees preserves the prerequisite BST ordering invariant. -/
public theorem ordered_merge {α : Type u} [LinearOrder α] {left right : Tree α}
    (hLeft : Ordered left) (hRight : Ordered right)
    (hSeparated : ∀ x ∈ left, ∀ y ∈ right, x < y) : Ordered (merge left right) := by
  change BinarySearchTree.Ordered (erase (merge left right))
  rw [erase_merge]
  exact BinarySearchTree.ordered_join hLeft hRight hSeparated

/-- Deletion preserves the prerequisite BST ordering invariant. -/
public theorem ordered_delete {α : Type u} [LinearOrder α] {key : α}
    {tree : Tree α} (hTree : Ordered tree) : Ordered (delete key tree) := by
  change BinarySearchTree.Ordered (erase (delete key tree))
  rw [erase_delete]
  exact BinarySearchTree.ordered_delete hTree

/-- The inorder traversal of a merge is the concatenation of the traversals. -/
public theorem inorder_merge {α : Type u} {left right : Tree α} :
    inorder (merge left right) = inorder left ++ inorder right := by
  change BinarySearchTree.inorder (erase (merge left right)) = _
  rw [erase_merge]
  exact BinarySearchTree.inorder_join

/-- Membership in a merge is membership in one of the two trees. -/
public theorem mem_merge {α : Type u} {x : α} {left right : Tree α} :
    x ∈ merge left right ↔ x ∈ left ∨ x ∈ right := by
  change x ∈ erase (merge left right) ↔ x ∈ erase left ∨ x ∈ erase right
  rw [erase_merge]
  exact BinarySearchTree.mem_join

/--
Deletion from an ordered tree filters the deleted key out of the inorder list.
That list has no duplicates, so this agrees with the `List.erase` form of
`BinarySearchTree.inorder_delete`.
-/
public theorem inorder_delete {α : Type u} [LinearOrder α] {key : α} {tree : Tree α}
    (hTree : Ordered tree) :
    inorder (delete key tree) = (inorder tree).filter (· ≠ key) := by
  change BinarySearchTree.inorder (erase (delete key tree)) =
    (BinarySearchTree.inorder (erase tree)).filter (· ≠ key)
  rw [erase_delete, BinarySearchTree.inorder_delete hTree,
    (BinarySearchTree.inorder_nodup hTree).erase_eq_filter]
  simp only [bne, Bool.beq_eq_decide_eq, decide_not]

/-- Deletion from an ordered tree removes exactly the deleted key from structural membership. -/
public theorem mem_delete_iff {α : Type u} [LinearOrder α] {key y : α} {tree : Tree α}
    (hTree : Ordered tree) : y ∈ delete key tree ↔ y ∈ tree ∧ y ≠ key := by
  change y ∈ erase (delete key tree) ↔ y ∈ erase tree ∧ y ≠ key
  rw [erase_delete]
  exact BinarySearchTree.mem_delete hTree

/-- The deleted key is absent after deletion from an ordered tree. -/
public theorem not_mem_delete {α : Type u} [LinearOrder α] {key : α} {tree : Tree α}
    (hTree : Ordered tree) : key ∉ delete key tree :=
  fun hKey => ((mem_delete_iff hTree).mp hKey).2 rfl

/-- Comparison search does not find the deleted key after deletion from an ordered tree. -/
public theorem contains_delete_self {α : Type u} [LinearOrder α] {key : α}
    {tree : Tree α} (hTree : Ordered tree) :
    contains key (delete key tree) = false := by
  by_contra hFound
  have hTrue : contains key (delete key tree) = true := by
    cases hContains : contains key (delete key tree) with
    | false => exact absurd hContains hFound
    | true => rfl
  exact not_mem_delete hTree
    ((contains_eq_true_iff (ordered_delete hTree)).mp hTrue)

/-- Cached rank after deletion refines the traversal rank of the erased result. -/
public theorem rank_delete_eq_bstRank {α : Type u} [LinearOrder α] {key query : α}
    {tree : Tree α} (hCache : CacheCorrect tree) (hTree : Ordered tree) :
    rank query (delete key tree) =
      BinarySearchTree.rank query (erase (delete key tree)) :=
  rank_eq_bstRank (cacheCorrect_delete hCache) (ordered_delete hTree)

/-- Cached select after deletion refines the traversal select of the erased result. -/
public theorem select_delete_eq_bstSelect {α : Type u} [LinearOrder α] {key : α}
    {tree : Tree α} (hCache : CacheCorrect tree) (index : Nat) :
    select (delete key tree) index =
      BinarySearchTree.select (erase (delete key tree)) index :=
  select_eq_bstSelect (cacheCorrect_delete hCache) index

/-- Selecting the rank of a key that survives deletion returns that key. -/
public theorem select_rank_delete {α : Type u} [LinearOrder α] {key y : α}
    {tree : Tree α} (hCache : CacheCorrect tree) (hTree : Ordered tree)
    (hy : y ∈ delete key tree) :
    select (delete key tree) (rank y (delete key tree)) = some y :=
  select_rank (cacheCorrect_delete hCache) (ordered_delete hTree) hy

end OrderStatisticTree
end Cslib.Algorithms.Lean
