/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree

/-!
# Order-statistic binary search trees

This module augments Mathlib's `BinaryTree` carrier with a cached subtree size at
each node. Its ordering, traversal, membership, rank, and select specifications
are inherited from `BinarySearchTree` through `erase`.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace OrderStatisticTree

universe u

/-- The key and cached number of nodes in the subtree rooted at a node. -/
public structure Entry (α : Type u) where
  key : α
  subtreeSize : Nat
deriving DecidableEq, Repr

/-- An order-statistic tree uses Mathlib's canonical binary-tree carrier. -/
public abbrev Tree (α : Type u) := BinaryTree (Entry α)

/-- The cached size at the root, or zero for an empty tree. -/
public def cachedSize {α : Type u} : Tree α → Nat
  | .nil => 0
  | .node entry _ _ => entry.subtreeSize

/-- Remove cached sizes, yielding the underlying binary search tree. -/
public def erase {α : Type u} : Tree α → BinaryTree α
  | .nil => .nil
  | .node entry left right => .node entry.key (erase left) (erase right)

/-- Cached sizes are correct at every node. -/
public def CacheCorrect {α : Type u} : Tree α → Prop
  | .nil => True
  | .node entry left right =>
      CacheCorrect left ∧ CacheCorrect right ∧
        entry.subtreeSize = left.numNodes + right.numNodes + 1

/-- The ordering invariant is the prerequisite BST invariant after erasing caches. -/
public def Ordered {α : Type u} [LT α] (tree : Tree α) : Prop :=
  BinarySearchTree.Ordered (erase tree)

/-- Inorder traversal is inherited from the prerequisite BST. -/
public def inorder {α : Type u} (tree : Tree α) : List α :=
  BinarySearchTree.inorder (erase tree)

instance {α : Type u} : Membership α (Tree α) where
  mem tree key := key ∈ erase tree

/-- Construct a node whose cache is computed from its children. -/
public def node {α : Type u} (key : α) (left right : Tree α) : Tree α :=
  .node { key, subtreeSize := cachedSize left + cachedSize right + 1 } left right

/-- Comparison search navigates one branch. -/
public def contains {α : Type u} [LinearOrder α] (query : α) : Tree α → Bool
  | .nil => false
  | .node entry left right =>
      if query < entry.key then contains query left
      else if entry.key < query then contains query right
      else true

/-- Insert a key, ignoring a duplicate and repairing every cache on the search path. -/
public def insert {α : Type u} [LinearOrder α] (key : α) : Tree α → Tree α
  | .nil => node key .nil .nil
  | tree@(.node entry left right) =>
      if key < entry.key then node entry.key (insert key left) right
      else if entry.key < key then node entry.key left (insert key right)
      else tree

/-- Build a tree by inserting keys from right to left. -/
public def fromList {α : Type u} [LinearOrder α] : List α → Tree α
  | [] => .nil
  | key :: keys => insert key (fromList keys)

/-- The number of keys strictly smaller than a query, using cached left sizes. -/
public def rank {α : Type u} [LinearOrder α] (query : α) : Tree α → Nat
  | .nil => 0
  | .node entry left right =>
      if query < entry.key then rank query left
      else if entry.key < query then cachedSize left + 1 + rank query right
      else cachedSize left

/-- The zero-based selected key, using cached left sizes to navigate one branch. -/
public def select {α : Type u} : Tree α → Nat → Option α
  | .nil, _ => none
  | .node entry left right, index =>
      if index < cachedSize left then select left index
      else if index = cachedSize left then some entry.key
      else select right (index - cachedSize left - 1)

/-- A correct root cache equals the canonical number of nodes. -/
public theorem cachedSize_eq_numNodes {α : Type u} {tree : Tree α}
    (hTree : CacheCorrect tree) : cachedSize tree = tree.numNodes := by
  cases tree with
  | nil => rfl
  | node entry left right =>
    exact hTree.2.2

private theorem erase_numNodes {α : Type u} (tree : Tree α) :
    (erase tree).numNodes = tree.numNodes := by
  induction tree with
  | nil => rfl
  | node entry left right ihLeft ihRight =>
    simp [erase, ihLeft, ihRight]

/-- The public node constructor preserves correct subtree-size caches. -/
public theorem cacheCorrect_node {α : Type u} {key : α} {left right : Tree α}
    (hLeft : CacheCorrect left) (hRight : CacheCorrect right) :
    CacheCorrect (node key left right) := by
  refine ⟨hLeft, hRight, ?_⟩
  simp [cachedSize_eq_numNodes hLeft, cachedSize_eq_numNodes hRight]

private theorem erase_node {α : Type u} (key : α) (left right : Tree α) :
    erase (node key left right) = .node key (erase left) (erase right) :=
  rfl

/-- Erasing after insertion agrees with insertion in the underlying binary search tree. -/
public theorem erase_insert {α : Type u} [LinearOrder α] (key : α) (tree : Tree α) :
    erase (insert key tree) = BinarySearchTree.insert key (erase tree) := by
  induction tree with
  | nil => rfl
  | node entry left right ihLeft ihRight =>
    simp only [insert, BinarySearchTree.insert, erase]
    by_cases hLeft : key < entry.key
    · simp [hLeft, erase_node, ihLeft]
    · by_cases hRight : entry.key < key
      · simp [hLeft, hRight, erase_node, ihRight]
      · simp [hLeft, hRight, erase]

/-- Insertion preserves correct caches. -/
public theorem cacheCorrect_insert {α : Type u} [LinearOrder α] {key : α}
    {tree : Tree α} (hTree : CacheCorrect tree) : CacheCorrect (insert key tree) := by
  induction tree with
  | nil => exact cacheCorrect_node trivial trivial
  | node entry left right ihLeft ihRight =>
    rcases hTree with ⟨hLeft, hRight, hSize⟩
    by_cases hKeyLeft : key < entry.key
    · simp [insert, hKeyLeft, cacheCorrect_node (ihLeft hLeft) hRight]
    · by_cases hKeyRight : entry.key < key
      · simp [insert, hKeyLeft, hKeyRight, cacheCorrect_node hLeft (ihRight hRight)]
      · simpa [insert, hKeyLeft, hKeyRight, CacheCorrect] using
          And.intro hLeft (And.intro hRight hSize)

/-- Insertion preserves the prerequisite BST ordering invariant. -/
public theorem ordered_insert {α : Type u} [LinearOrder α] {key : α}
    {tree : Tree α} (hTree : Ordered tree) : Ordered (insert key tree) := by
  rw [Ordered, erase_insert]
  exact BinarySearchTree.ordered_insert hTree

/-- Trees built by insertion have correct caches. -/
public theorem cacheCorrect_fromList {α : Type u} [LinearOrder α] {keys : List α} :
    CacheCorrect (fromList keys) := by
  induction keys with
  | nil => trivial
  | cons key keys ih => exact cacheCorrect_insert ih

/-- Trees built by insertion satisfy the prerequisite BST ordering invariant. -/
public theorem ordered_fromList {α : Type u} [LinearOrder α] {keys : List α} :
    Ordered (fromList keys) := by
  induction keys with
  | nil => trivial
  | cons key keys ih => exact ordered_insert ih

private theorem erase_fromList {α : Type u} [LinearOrder α] (keys : List α) :
    erase (fromList keys) = BinarySearchTree.fromList keys := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp [fromList, erase_insert, ih, BinarySearchTree.fromList]

/-- Membership in a tree built from a list is list membership. -/
public theorem mem_fromList {α : Type u} [LinearOrder α] {key : α} {keys : List α} :
    key ∈ fromList keys ↔ key ∈ keys := by
  change key ∈ erase (fromList keys) ↔ key ∈ keys
  rw [erase_fromList]
  exact BinarySearchTree.mem_fromList

private theorem contains_eq_bstContains {α : Type u} [LinearOrder α]
    (query : α) (tree : Tree α) :
    contains query tree = BinarySearchTree.contains query (erase tree) := by
  induction tree with
  | nil => rfl
  | node entry left right ihLeft ihRight =>
    simp only [contains, erase, BinarySearchTree.contains]
    by_cases hLeft : query < entry.key
    · simp [hLeft, ihLeft]
    · by_cases hRight : entry.key < query
      · simp [hLeft, hRight, ihRight]
      · simp [hLeft, hRight]

/-- Comparison search returns true exactly for structural membership in an ordered tree. -/
public theorem contains_eq_true_iff {α : Type u} [LinearOrder α] {query : α}
    {tree : Tree α} (hTree : Ordered tree) : contains query tree = true ↔ query ∈ tree := by
  rw [contains_eq_bstContains]
  exact BinarySearchTree.contains_eq_true_iff hTree

private theorem filter_lt_eq_nil_of_forall_ge {α : Type u} [LinearOrder α]
    {bound : α} {xs : List α} (h : ∀ x ∈ xs, bound ≤ x) :
    xs.filter (· < bound) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : bound ≤ x := h x (by simp)
    have hxs : ∀ y ∈ xs, bound ≤ y := by
      intro y hy
      exact h y (by simp [hy])
    simp [not_lt_of_ge hx, ih hxs]

private theorem filter_lt_eq_self_of_forall_lt {α : Type u} [LinearOrder α]
    {bound : α} {xs : List α} (h : ∀ x ∈ xs, x < bound) :
    xs.filter (· < bound) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x < bound := h x (by simp)
    have hxs : ∀ y ∈ xs, y < bound := by
      intro y hy
      exact h y (by simp [hy])
    simp [hx, ih hxs]

/-- Cached navigation rank refines the prerequisite traversal-based rank. -/
public theorem rank_eq_bstRank {α : Type u} [LinearOrder α] {query : α}
    {tree : Tree α} (hCache : CacheCorrect tree) (hTree : Ordered tree) :
    rank query tree = BinarySearchTree.rank query (erase tree) := by
  induction tree with
  | nil => rfl
  | node entry left right ihLeft ihRight =>
    rcases hCache with ⟨hCacheLeft, hCacheRight, hSize⟩
    rcases hTree with ⟨hOrderedLeft, hOrderedRight, hAllLeft, hAllRight⟩
    have hLeftLength : cachedSize left = (BinarySearchTree.inorder (erase left)).length := by
      rw [cachedSize_eq_numNodes hCacheLeft, ← erase_numNodes]
      exact BinarySearchTree.numNodes_eq_length_inorder
    by_cases hQueryLeft : query < entry.key
    · have hRightNone :
          (BinarySearchTree.inorder (erase right)).filter (· < query) = [] := by
        apply filter_lt_eq_nil_of_forall_ge
        intro x hx
        have hKeyX : entry.key < x :=
          (BinarySearchTree.all_iff_forall_mem.mp hAllRight) x
            (BinarySearchTree.mem_inorder.mp hx)
        exact le_of_lt (lt_trans hQueryLeft hKeyX)
      have hKeyNotQuery : ¬entry.key < query := not_lt_of_ge (le_of_lt hQueryLeft)
      rw [show rank query (.node entry left right) = rank query left by
        simp [rank, hQueryLeft]]
      rw [ihLeft hCacheLeft hOrderedLeft]
      simp only [BinarySearchTree.rank, erase, BinarySearchTree.inorder_node,
        List.filter_append, List.filter_cons]
      simp [hKeyNotQuery, hRightNone]
    · by_cases hKeyQuery : entry.key < query
      · have hLeftAll :
            (BinarySearchTree.inorder (erase left)).filter (· < query) =
              BinarySearchTree.inorder (erase left) := by
          apply filter_lt_eq_self_of_forall_lt
          intro x hx
          have hXKey : x < entry.key :=
            (BinarySearchTree.all_iff_forall_mem.mp hAllLeft) x
              (BinarySearchTree.mem_inorder.mp hx)
          exact lt_trans hXKey hKeyQuery
        simp [rank, hQueryLeft, hKeyQuery, BinarySearchTree.rank, erase,
          BinarySearchTree.inorder_node, hLeftAll, hLeftLength,
          ihRight hCacheRight hOrderedRight, Nat.add_assoc, Nat.add_comm]
        omega
      · have hQueryEq : query = entry.key :=
          le_antisymm (le_of_not_gt hKeyQuery) (le_of_not_gt hQueryLeft)
        subst query
        have hLeftAll :
            (BinarySearchTree.inorder (erase left)).filter (· < entry.key) =
              BinarySearchTree.inorder (erase left) := by
          apply filter_lt_eq_self_of_forall_lt
          intro x hx
          exact (BinarySearchTree.all_iff_forall_mem.mp hAllLeft) x
            (BinarySearchTree.mem_inorder.mp hx)
        have hRightNone :
            (BinarySearchTree.inorder (erase right)).filter (· < entry.key) = [] := by
          apply filter_lt_eq_nil_of_forall_ge
          intro x hx
          exact le_of_lt <|
            (BinarySearchTree.all_iff_forall_mem.mp hAllRight) x
              (BinarySearchTree.mem_inorder.mp hx)
        simp [rank, hQueryLeft, BinarySearchTree.rank,
          BinarySearchTree.inorder_node, erase, hLeftAll, hRightNone, hLeftLength]

/-- Cached navigation select refines the prerequisite traversal-based select. -/
public theorem select_eq_bstSelect {α : Type u} {tree : Tree α}
    (hCache : CacheCorrect tree) (index : Nat) :
    select tree index = BinarySearchTree.select (erase tree) index := by
  induction tree generalizing index with
  | nil => rfl
  | node entry left right ihLeft ihRight =>
    rcases hCache with ⟨hCacheLeft, hCacheRight, hSize⟩
    have hLeftLength : cachedSize left = (BinarySearchTree.inorder (erase left)).length := by
      rw [cachedSize_eq_numNodes hCacheLeft, ← erase_numNodes]
      exact BinarySearchTree.numNodes_eq_length_inorder
    by_cases hIndexLeft : index < cachedSize left
    · simp [select, hIndexLeft, BinarySearchTree.select, BinarySearchTree.inorder_node, erase,
        List.getElem?_append, ← hLeftLength, ihLeft hCacheLeft]
    · by_cases hIndexRoot : index = cachedSize left
      · subst index
        simp [select, BinarySearchTree.select, BinarySearchTree.inorder_node, erase,
          hLeftLength]
      · have hLeftIndex : cachedSize left < index := by omega
        have hDrop : index - cachedSize left = (index - cachedSize left - 1) + 1 := by
          omega
        rw [show select (.node entry left right) index =
            select right (index - cachedSize left - 1) by
          simp [select, hIndexLeft, hIndexRoot]]
        rw [ihRight hCacheRight]
        unfold BinarySearchTree.select
        simp only [erase, BinarySearchTree.inorder_node, List.getElem?_append]
        rw [ite_eq_right (by omega : ¬index < (BinarySearchTree.inorder (erase left)).length)]
        rw [← hLeftLength, hDrop]
        rfl

/-- Selecting the rank of a present key returns that key. -/
public theorem select_rank {α : Type u} [LinearOrder α] {key : α} {tree : Tree α}
    (hCache : CacheCorrect tree) (hTree : Ordered tree) (hKey : key ∈ tree) :
    select tree (rank key tree) = some key := by
  rw [select_eq_bstSelect hCache, rank_eq_bstRank hCache hTree]
  exact BinarySearchTree.select_rank hTree hKey

/-- A successfully selected key has rank equal to its selected index. -/
public theorem rank_select {α : Type u} [LinearOrder α] {tree : Tree α}
    (hCache : CacheCorrect tree) (hTree : Ordered tree) {index : Nat} {key : α}
    (hSelect : select tree index = some key) : rank key tree = index := by
  rw [rank_eq_bstRank hCache hTree]
  apply BinarySearchTree.rank_select hTree
  rw [← select_eq_bstSelect hCache]
  exact hSelect

end OrderStatisticTree
end Cslib.Algorithms.Lean
