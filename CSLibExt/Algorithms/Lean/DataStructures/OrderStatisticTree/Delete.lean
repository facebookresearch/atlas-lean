/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.OrderStatisticTree

/-!
# Order-statistic tree deletion

Key deletion for the size-augmented tree of `OrderStatisticTree.lean`. The name
`erase` already denotes cache-stripping there, so deletion is called `delete`.

Deletion follows the search path, rebuilding ancestors with the cache-repairing
constructor `node`; at the deleted node the two subtrees are combined with
`merge`. Order, membership, traversal, rank, and select specifications are
inherited from `BinarySearchTree` through `erase`, following the parent module.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace OrderStatisticTree

universe u

/--
Merge two trees in which every key of the first is smaller than every key of
the second, repairing every rebuilt cache. The result is unspecified when that
separation does not hold.
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

/-- The cache-stripped image of merging, used only to inherit BST specifications. -/
private def bstMerge {α : Type u} : BinaryTree α → BinaryTree α → BinaryTree α
  | .nil, right => right
  | .node key left right, other => .node key left (bstMerge right other)

/-- The cache-stripped image of deletion, used only to inherit BST specifications. -/
private def bstDelete {α : Type u} [LinearOrder α] (key : α) :
    BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node root left right =>
      if key < root then .node root (bstDelete key left) right
      else if root < key then .node root left (bstDelete key right)
      else bstMerge left right

private theorem erase_node' {α : Type u} (key : α) (left right : Tree α) :
    erase (node key left right) = .node key (erase left) (erase right) :=
  rfl

private theorem erase_merge {α : Type u} (left right : Tree α) :
    erase (merge left right) = bstMerge (erase left) (erase right) := by
  induction left generalizing right with
  | nil => rfl
  | node entry subLeft subRight _ihLeft ihRight =>
    simp [merge, bstMerge, erase, erase_node', ihRight]

private theorem erase_delete {α : Type u} [LinearOrder α] (key : α) (tree : Tree α) :
    erase (delete key tree) = bstDelete key (erase tree) := by
  induction tree with
  | nil => rfl
  | node entry left right ihLeft ihRight =>
    simp only [delete, bstDelete, erase]
    by_cases hLeft : key < entry.key
    · simp [hLeft, erase_node', ihLeft]
    · by_cases hRight : entry.key < key
      · simp [hLeft, hRight, erase_node', ihRight]
      · simp [hLeft, hRight, erase_merge]

private theorem inorder_bstMerge {α : Type u} (left right : BinaryTree α) :
    BinarySearchTree.inorder (bstMerge left right) =
      BinarySearchTree.inorder left ++ BinarySearchTree.inorder right := by
  induction left generalizing right with
  | nil => rfl
  | node key subLeft subRight _ihLeft ihRight =>
    simp [bstMerge, BinarySearchTree.inorder_node, ihRight, List.append_assoc]

private theorem mem_bstMerge {α : Type u} {x : α} {left right : BinaryTree α} :
    x ∈ bstMerge left right ↔ x ∈ left ∨ x ∈ right := by
  rw [← BinarySearchTree.mem_inorder, inorder_bstMerge, List.mem_append,
    BinarySearchTree.mem_inorder, BinarySearchTree.mem_inorder]

private theorem all_bstMerge_of {α : Type u} {p : α → Prop}
    {left right : BinaryTree α}
    (hLeft : BinarySearchTree.All p left) (hRight : BinarySearchTree.All p right) :
    BinarySearchTree.All p (bstMerge left right) := by
  rw [BinarySearchTree.all_iff_forall_mem] at hLeft hRight ⊢
  intro x hx
  rcases mem_bstMerge.mp hx with hx | hx
  · exact hLeft x hx
  · exact hRight x hx

private theorem ordered_bstMerge {α : Type u} [LinearOrder α]
    {left right : BinaryTree α}
    (hLeft : BinarySearchTree.Ordered left) (hRight : BinarySearchTree.Ordered right)
    (hSeparated : ∀ x ∈ left, ∀ y ∈ right, x < y) :
    BinarySearchTree.Ordered (bstMerge left right) := by
  induction left with
  | nil => exact hRight
  | node key subLeft subRight _ihLeft ihRight =>
    rcases hLeft with ⟨hSubLeft, hSubRight, hAllLeft, hAllRight⟩
    have hSeparatedRight : ∀ x ∈ subRight, ∀ y ∈ right, x < y :=
      fun x hx y hy => hSeparated x (Or.inr (Or.inr hx)) y hy
    have hKeyRight : BinarySearchTree.All (key < ·) right := by
      rw [BinarySearchTree.all_iff_forall_mem]
      exact fun y hy => hSeparated key (Or.inr (Or.inl rfl)) y hy
    simp only [bstMerge]
    exact ⟨hSubLeft, ihRight hSubRight hSeparatedRight, hAllLeft,
      all_bstMerge_of hAllRight hKeyRight⟩

private theorem filter_ne_eq_self {α : Type u} [DecidableEq α] {bound : α}
    {xs : List α} (h : ∀ x ∈ xs, x ≠ bound) : xs.filter (· ≠ bound) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ bound := h x (by simp)
    have hxs : ∀ y ∈ xs, y ≠ bound := fun y hy => h y (by simp [hy])
    rw [List.filter_cons_of_pos (by simp [hx]), ih hxs]

private theorem inorder_bstDelete {α : Type u} [LinearOrder α] {key : α}
    {tree : BinaryTree α} (hTree : BinarySearchTree.Ordered tree) :
    BinarySearchTree.inorder (bstDelete key tree) =
      (BinarySearchTree.inorder tree).filter (· ≠ key) := by
  induction tree with
  | nil => rfl
  | node root left right ihLeft ihRight =>
    rcases hTree with ⟨hOrderedLeft, hOrderedRight, hAllLeft, hAllRight⟩
    by_cases hKeyLeft : key < root
    · have hConsAll :
          (root :: BinarySearchTree.inorder right).filter (· ≠ key) =
            root :: BinarySearchTree.inorder right := by
        apply filter_ne_eq_self
        intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ne_of_gt hKeyLeft
        · have hRootX : root < x :=
            (BinarySearchTree.all_iff_forall_mem.mp hAllRight) x
              (BinarySearchTree.mem_inorder.mp hx)
          exact ne_of_gt (lt_trans hKeyLeft hRootX)
      have hDelete : bstDelete key (.node root left right) =
          .node root (bstDelete key left) right := by
        simp [bstDelete, hKeyLeft]
      simp only [hDelete, BinarySearchTree.inorder_node, List.filter_append,
        ihLeft hOrderedLeft, hConsAll]
    · by_cases hKeyRight : root < key
      · have hLeftAll :
            (BinarySearchTree.inorder left).filter (· ≠ key) =
              BinarySearchTree.inorder left := by
          apply filter_ne_eq_self
          intro x hx
          have hXRoot : x < root :=
            (BinarySearchTree.all_iff_forall_mem.mp hAllLeft) x
              (BinarySearchTree.mem_inorder.mp hx)
          exact ne_of_lt (lt_trans hXRoot hKeyRight)
        have hRootNe : root ≠ key := ne_of_lt hKeyRight
        have hCons :
            (root :: BinarySearchTree.inorder right).filter (· ≠ key) =
              root :: (BinarySearchTree.inorder right).filter (· ≠ key) := by
          simp [hRootNe]
        have hDelete : bstDelete key (.node root left right) =
            .node root left (bstDelete key right) := by
          simp [bstDelete, hKeyLeft, hKeyRight]
        simp only [hDelete, BinarySearchTree.inorder_node, List.filter_append,
          hLeftAll, hCons, ihRight hOrderedRight]
      · have hEqual : root = key :=
          le_antisymm (le_of_not_gt hKeyLeft) (le_of_not_gt hKeyRight)
        subst root
        have hLeftAll :
            (BinarySearchTree.inorder left).filter (· ≠ key) =
              BinarySearchTree.inorder left := by
          apply filter_ne_eq_self
          intro x hx
          exact ne_of_lt <|
            (BinarySearchTree.all_iff_forall_mem.mp hAllLeft) x
              (BinarySearchTree.mem_inorder.mp hx)
        have hRightAll :
            (BinarySearchTree.inorder right).filter (· ≠ key) =
              BinarySearchTree.inorder right := by
          apply filter_ne_eq_self
          intro x hx
          exact ne_of_gt <|
            (BinarySearchTree.all_iff_forall_mem.mp hAllRight) x
              (BinarySearchTree.mem_inorder.mp hx)
        have hDelete : bstDelete key (.node key left right) =
            bstMerge left right := by
          simp [bstDelete, hKeyLeft]
        have hCons : (key :: BinarySearchTree.inorder right).filter (· ≠ key) =
            (BinarySearchTree.inorder right).filter (· ≠ key) := by
          simp
        simp only [hDelete, BinarySearchTree.inorder_node, inorder_bstMerge,
          List.filter_append, hLeftAll, hCons, hRightAll]

private theorem mem_bstDelete_iff {α : Type u} [LinearOrder α] {key y : α}
    {tree : BinaryTree α} (hTree : BinarySearchTree.Ordered tree) :
    y ∈ bstDelete key tree ↔ y ∈ tree ∧ y ≠ key := by
  rw [← BinarySearchTree.mem_inorder, ← BinarySearchTree.mem_inorder,
    inorder_bstDelete hTree]
  simp [List.mem_filter]

private theorem ordered_bstDelete {α : Type u} [LinearOrder α] {key : α}
    {tree : BinaryTree α} (hTree : BinarySearchTree.Ordered tree) :
    BinarySearchTree.Ordered (bstDelete key tree) := by
  induction tree with
  | nil => trivial
  | node root left right ihLeft ihRight =>
    rcases hTree with ⟨hOrderedLeft, hOrderedRight, hAllLeft, hAllRight⟩
    by_cases hKeyLeft : key < root
    · have hAllDeleted : BinarySearchTree.All (· < root) (bstDelete key left) := by
        rw [BinarySearchTree.all_iff_forall_mem] at hAllLeft ⊢
        exact fun x hx => hAllLeft x ((mem_bstDelete_iff hOrderedLeft).mp hx).1
      have hDelete : bstDelete key (.node root left right) =
          .node root (bstDelete key left) right := by
        simp [bstDelete, hKeyLeft]
      rw [hDelete]
      exact ⟨ihLeft hOrderedLeft, hOrderedRight, hAllDeleted, hAllRight⟩
    · by_cases hKeyRight : root < key
      · have hAllDeleted : BinarySearchTree.All (root < ·) (bstDelete key right) := by
          rw [BinarySearchTree.all_iff_forall_mem] at hAllRight ⊢
          exact fun x hx => hAllRight x ((mem_bstDelete_iff hOrderedRight).mp hx).1
        have hDelete : bstDelete key (.node root left right) =
            .node root left (bstDelete key right) := by
          simp [bstDelete, hKeyLeft, hKeyRight]
        rw [hDelete]
        exact ⟨hOrderedLeft, ihRight hOrderedRight, hAllLeft, hAllDeleted⟩
      · have hDelete : bstDelete key (.node root left right) = bstMerge left right := by
          simp [bstDelete, hKeyLeft, hKeyRight]
        rw [hDelete]
        apply ordered_bstMerge hOrderedLeft hOrderedRight
        intro x hx y hy
        exact lt_trans
          ((BinarySearchTree.all_iff_forall_mem.mp hAllLeft) x hx)
          ((BinarySearchTree.all_iff_forall_mem.mp hAllRight) y hy)

/-- Merging separated trees preserves the prerequisite BST ordering invariant. -/
public theorem ordered_merge {α : Type u} [LinearOrder α] {left right : Tree α}
    (hLeft : Ordered left) (hRight : Ordered right)
    (hSeparated : ∀ x ∈ left, ∀ y ∈ right, x < y) : Ordered (merge left right) := by
  show BinarySearchTree.Ordered (erase (merge left right))
  rw [erase_merge]
  exact ordered_bstMerge hLeft hRight hSeparated

/-- Deletion preserves the prerequisite BST ordering invariant. -/
public theorem ordered_delete {α : Type u} [LinearOrder α] {key : α}
    {tree : Tree α} (hTree : Ordered tree) : Ordered (delete key tree) := by
  show BinarySearchTree.Ordered (erase (delete key tree))
  rw [erase_delete]
  exact ordered_bstDelete hTree

/-- The inorder traversal of a merge is the concatenation of the traversals. -/
public theorem inorder_merge {α : Type u} {left right : Tree α} :
    inorder (merge left right) = inorder left ++ inorder right := by
  show BinarySearchTree.inorder (erase (merge left right)) = _
  rw [erase_merge]
  exact inorder_bstMerge _ _

/-- Membership in a merge is membership in one of the two trees. -/
public theorem mem_merge {α : Type u} {x : α} {left right : Tree α} :
    x ∈ merge left right ↔ x ∈ left ∨ x ∈ right := by
  change x ∈ erase (merge left right) ↔ x ∈ erase left ∨ x ∈ erase right
  rw [erase_merge]
  exact mem_bstMerge

/-- Traversal deletion removes exactly the deleted key from the inorder list. -/
public theorem inorder_delete {α : Type u} [LinearOrder α] {key : α} {tree : Tree α}
    (hTree : Ordered tree) :
    inorder (delete key tree) = (inorder tree).filter (· ≠ key) := by
  show BinarySearchTree.inorder (erase (delete key tree)) =
    (BinarySearchTree.inorder (erase tree)).filter (· ≠ key)
  rw [erase_delete]
  exact inorder_bstDelete hTree

/-- Deletion removes exactly the deleted key from structural membership. -/
public theorem mem_delete_iff {α : Type u} [LinearOrder α] {key y : α} {tree : Tree α}
    (hTree : Ordered tree) : y ∈ delete key tree ↔ y ∈ tree ∧ y ≠ key := by
  change y ∈ erase (delete key tree) ↔ y ∈ erase tree ∧ y ≠ key
  rw [erase_delete]
  exact mem_bstDelete_iff hTree

/-- The deleted key is absent from the result. -/
public theorem not_mem_delete {α : Type u} [LinearOrder α] {key : α} {tree : Tree α}
    (hTree : Ordered tree) : key ∉ delete key tree :=
  fun hKey => ((mem_delete_iff hTree).mp hKey).2 rfl

/-- Comparison search does not find the deleted key in the result. -/
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
