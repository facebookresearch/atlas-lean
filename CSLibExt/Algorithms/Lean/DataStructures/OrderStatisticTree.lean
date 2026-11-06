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

/-- **Order-statistic tree node entry.** A node entry of an order-statistic tree over a type
$\alpha$ consists of a key in $\alpha$ and a natural number, the cached number of nodes in the
subtree rooted at that node. -/
public structure Entry (α : Type u) where
  key : α
  subtreeSize : Nat
deriving DecidableEq, Repr

/-- **Order-statistic tree.** An order-statistic tree with keys in a type $\alpha$ is a binary
tree, possibly empty, each of whose nodes carries a key in $\alpha$ together with a natural
number, meant as the cached number of nodes in the subtree rooted at that node. That these
caches are correct is a separate condition. -/
public abbrev Tree (α : Type u) := BinaryTree (Entry α)

/-- **Cached root size.** The cached root size of an order-statistic tree is the subtree size
stored in the entry of its root node, and is $0$ for the empty tree. -/
public def cachedSize {α : Type u} : Tree α → Nat
  | .nil => 0
  | .node entry _ _ => entry.subtreeSize

/-- **Erasing the size caches of an order-statistic tree.** The erasure of an order-statistic
tree is the binary tree of the same shape whose node keys are the keys of the original nodes:
the empty tree is sent to the empty tree, and a node is sent to the node with the same key
whose left and right subtrees are the erasures of the original left and right subtrees, so
every cached subtree size is dropped. -/
public def erase {α : Type u} : Tree α → BinaryTree α
  | .nil => .nil
  | .node entry left right => .node entry.key (erase left) (erase right)

/-- **Correct size caches.** An order-statistic tree has correct size caches when, at every
node, the cached subtree size equals the number of nodes of the left subtree plus the number of
nodes of the right subtree plus one, that is, the number of nodes of the subtree rooted at that
node. The empty tree has correct size caches. -/
public def CacheCorrect {α : Type u} : Tree α → Prop
  | .nil => True
  | .node entry left right =>
      CacheCorrect left ∧ CacheCorrect right ∧
        entry.subtreeSize = left.numNodes + right.numNodes + 1

/-- **Ordered order-statistic tree.** An order-statistic tree over a type equipped with a
relation $<$ is ordered when the binary tree obtained by erasing its cached sizes is an ordered
binary search tree: at every node, each key of the left subtree is $<$ the node's key, the
node's key is $<$ each key of the right subtree, and both subtrees are ordered. -/
public def Ordered {α : Type u} [LT α] (tree : Tree α) : Prop :=
  BinarySearchTree.Ordered (erase tree)

/-- **Inorder traversal of an order-statistic tree.** The inorder traversal of an
order-statistic tree is the inorder traversal of the binary tree obtained by erasing its cached
subtree sizes: the traversal of the left subtree, then the root key, then the traversal of the
right subtree, and the empty list for the empty tree. -/
public def inorder {α : Type u} (tree : Tree α) : List α :=
  BinarySearchTree.inorder (erase tree)

instance {α : Type u} : Membership α (Tree α) where
  mem tree key := key ∈ erase tree

/-- **Order-statistic tree node with computed cache.** Given a key $k$ and order-statistic
trees $L$ and $R$, the node built from them has key $k$, left subtree $L$, right subtree $R$,
and cached subtree size equal to the cached root size of $L$ plus the cached root size of $R$
plus one, where the empty tree has cached root size zero. -/
public def node {α : Type u} (key : α) (left right : Tree α) : Tree α :=
  .node { key, subtreeSize := cachedSize left + cachedSize right + 1 } left right

/-- **Search in an order-statistic tree.** Let $\alpha$ be a linearly ordered type and
$q \in \alpha$. Searching for $q$ in the empty tree returns false. At a node with key $k$, the
search continues in the left subtree if $q < k$, continues in the right subtree if $k < q$, and
returns true otherwise. -/
public def contains {α : Type u} [LinearOrder α] (query : α) : Tree α → Bool
  | .nil => false
  | .node entry left right =>
      if query < entry.key then contains query left
      else if entry.key < query then contains query right
      else true

/-- **Insertion into an order-statistic tree.** Inserting a key $k$ of a linearly ordered type
into the empty tree gives a single node with key $k$ and cached size $1$. For a nonempty tree
with root key $r$: if $k < r$, the key is inserted into the left subtree; if $r < k$, it is
inserted into the right subtree; in both cases the root is rebuilt with key $r$ and cached size
equal to the cached root sizes of its two subtrees plus one (an empty subtree counts as zero).
Otherwise $k = r$ and the tree is returned unchanged. -/
public def insert {α : Type u} [LinearOrder α] (key : α) : Tree α → Tree α
  | .nil => node key .nil .nil
  | tree@(.node entry left right) =>
      if key < entry.key then node entry.key (insert key left) right
      else if entry.key < key then node entry.key left (insert key right)
      else tree

/-- **Order-statistic tree built from a list.** For a linearly ordered key type, the
order-statistic tree built from a list of keys is obtained by inserting the keys into the empty
tree from right to left: the empty list gives the empty tree, and a list with head $k$ and
tail $l$ gives the insertion of $k$ into the tree built from $l$. -/
public def fromList {α : Type u} [LinearOrder α] : List α → Tree α
  | [] => .nil
  | key :: keys => insert key (fromList keys)

/-- **Rank in an order-statistic tree.** For a key $q$ of a linearly ordered type, the rank of
$q$ in an order-statistic tree is computed by descending from the root. It is $0$ for the empty
tree. At a node with key $k$, left subtree $L$ and right subtree $R$, it is the rank of $q$ in
$L$ if $q < k$; it is $s(L) + 1$ plus the rank of $q$ in $R$ if $k < q$; and it is $s(L)$ if
$q = k$. Here $s(L)$ is the subtree size cached at the root of $L$, and $0$ if $L$ is empty.

When the cached sizes are correct and the tree is ordered, this is the number of keys in the
tree strictly smaller than $q$. -/
public def rank {α : Type u} [LinearOrder α] (query : α) : Tree α → Nat
  | .nil => 0
  | .node entry left right =>
      if query < entry.key then rank query left
      else if entry.key < query then cachedSize left + 1 + rank query right
      else cachedSize left

/-- **Select in an order-statistic tree.** For an order-statistic tree $T$ and a natural number
$i$, select at index $i$ in $T$ is computed by descending from the root. It returns nothing for
the empty tree. At a node with key $k$, left subtree $L$ and right subtree $R$, it is select at
index $i$ in $L$ if $i < s(L)$; it returns $k$ if $i = s(L)$; and it is select at index
$i - s(L) - 1$ in $R$ if $i > s(L)$. Here $s(L)$ is the subtree size cached at the root of $L$,
and $0$ if $L$ is empty.

When the cached sizes are correct, this returns the key at zero-based position $i$ of the
inorder traversal, and nothing if $T$ has at most $i$ nodes. -/
public def select {α : Type u} : Tree α → Nat → Option α
  | .nil, _ => none
  | .node entry left right, index =>
      if index < cachedSize left then select left index
      else if index = cachedSize left then some entry.key
      else select right (index - cachedSize left - 1)

/-- **Correct caches give the tree size.** If an order-statistic tree $T$ has correct cached
subtree sizes at every node, then the cached root size of $T$ (zero for the empty tree) equals
the number of nodes of $T$. -/
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

/-- **The cache-computing node constructor preserves correct size caches.** Let $k$ be a key and
let $L$ and $R$ be order-statistic trees whose cached subtree sizes are correct at every node.
Then the node with key $k$, left subtree $L$ and right subtree $R$, whose root cache is the
cached root size of $L$ plus the cached root size of $R$ plus one, also has correct cached
subtree sizes at every node. -/
public theorem cacheCorrect_node {α : Type u} {key : α} {left right : Tree α}
    (hLeft : CacheCorrect left) (hRight : CacheCorrect right) :
    CacheCorrect (node key left right) := by
  refine ⟨hLeft, hRight, ?_⟩
  simp [cachedSize_eq_numNodes hLeft, cachedSize_eq_numNodes hRight]

private theorem erase_node {α : Type u} (key : α) (left right : Tree α) :
    erase (node key left right) = .node key (erase left) (erase right) :=
  rfl

/-- **Insertion commutes with forgetting the size caches.** Let $\alpha$ be a linearly ordered
type, $k \in \alpha$ and $T$ an order-statistic tree over $\alpha$. Forgetting the cached sizes
of the tree obtained by inserting $k$ into $T$ gives the same binary tree as inserting $k$, by
ordinary binary-search-tree insertion, into $T$ with its cached sizes forgotten. -/
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

/-- **Insertion preserves correct size caches.** Let $\alpha$ be a linearly ordered type, let
$k \in \alpha$, and let $T$ be an order-statistic tree over $\alpha$ whose cached subtree sizes
are correct at every node. Then the tree obtained by inserting $k$ into $T$ also has correct
cached subtree sizes at every node. -/
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

/-- **Insertion preserves ordering of order-statistic trees.** Let $T$ be an order-statistic
tree over a linearly ordered key type that is ordered, meaning that after its cached sizes are
erased, at every node each key of the left subtree is strictly smaller than the node's key and
each key of the right subtree is strictly larger. Then for every key $k$, the tree obtained by
inserting $k$ into $T$ is again ordered. -/
public theorem ordered_insert {α : Type u} [LinearOrder α] {key : α}
    {tree : Tree α} (hTree : Ordered tree) : Ordered (insert key tree) := by
  rw [Ordered, erase_insert]
  exact BinarySearchTree.ordered_insert hTree

/-- **Order-statistic trees built from a list have correct size caches.** Let $\alpha$ be a
linearly ordered type. For every list $\ell$ of elements of $\alpha$, the order-statistic tree
obtained by inserting the elements of $\ell$ into the empty tree, from right to left, has correct
cached subtree sizes at every node. -/
public theorem cacheCorrect_fromList {α : Type u} [LinearOrder α] {keys : List α} :
    CacheCorrect (fromList keys) := by
  induction keys with
  | nil => trivial
  | cons key keys ih => exact cacheCorrect_insert ih

/-- **Order-statistic trees built from lists are ordered.** For every list $l$ of keys from a
linearly ordered type, the order-statistic tree built from $l$ by successive insertion is
ordered: after its cached sizes are erased, at every node each key of the left subtree is
strictly smaller than the node's key and each key of the right subtree is strictly larger. -/
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

/-- **Keys of an order-statistic tree built from a list.** For a linearly ordered key type, a
key $k$ and a list $l$ of keys, $k$ is a key of some node of the order-statistic tree built
from $l$ by successive insertion if and only if $k$ occurs in $l$. -/
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

/-- **Search in an ordered order-statistic tree is correct.** Let $\alpha$ be a linearly ordered
type and $T$ an order-statistic tree over $\alpha$ that is ordered: after forgetting the cached
sizes, at every node all keys in the left subtree are smaller than the node's key and all keys in
the right subtree are larger. Then for every $q \in \alpha$, comparison search for $q$ in $T$
returns true if and only if $q$ is the key of some node of $T$. -/
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

/-- **Cached rank agrees with traversal rank.** Let $T$ be an order-statistic tree over a
linearly ordered key type whose cached subtree sizes are correct at every node and which is
ordered. Then for every query $q$, the rank of $q$ computed by descending $T$ with cached
left-subtree sizes equals the number of entries strictly smaller than $q$ in the inorder
traversal of the binary tree obtained by erasing the caches of $T$. -/
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

/-- **Cached select agrees with inorder select.** For every order-statistic tree $T$ whose
cached subtree sizes are correct and every natural number $i$, select at index $i$ in $T$
(descending with the cached sizes) returns the same result as taking the element at zero-based
position $i$ of the inorder traversal of the binary tree obtained from $T$ by erasing the cached
sizes; in particular both return nothing when that position does not exist. -/
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

/-- **Select inverts rank in an order-statistic tree.** Let $T$ be an order-statistic tree over
a linearly ordered type whose cached subtree sizes are correct and which satisfies the
binary-search-tree ordering. For every key $k$ in $T$, select in $T$ at the index equal to the
rank of $k$ in $T$ returns $k$. -/
public theorem select_rank {α : Type u} [LinearOrder α] {key : α} {tree : Tree α}
    (hCache : CacheCorrect tree) (hTree : Ordered tree) (hKey : key ∈ tree) :
    select tree (rank key tree) = some key := by
  rw [select_eq_bstSelect hCache, rank_eq_bstRank hCache hTree]
  exact BinarySearchTree.select_rank hTree hKey

/-- **Rank inverts select in an order-statistic tree.** Let $T$ be an order-statistic tree
over a linearly ordered type whose cached subtree sizes are correct and which satisfies the
binary-search-tree ordering. If select at zero-based index $i$ in $T$ returns a key $k$, then
the rank of $k$ in $T$ equals $i$. -/
public theorem rank_select {α : Type u} [LinearOrder α] {tree : Tree α}
    (hCache : CacheCorrect tree) (hTree : Ordered tree) {index : Nat} {key : α}
    (hSelect : select tree index = some key) : rank key tree = index := by
  rw [rank_eq_bstRank hCache hTree]
  apply BinarySearchTree.rank_select hTree
  rw [← select_eq_bstSelect hCache]
  exact hSelect

end OrderStatisticTree
end Cslib.Algorithms.Lean
