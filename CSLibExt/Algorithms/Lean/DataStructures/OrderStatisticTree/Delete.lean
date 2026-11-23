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
**Merging order-statistic trees.** The merge of order-statistic trees $A$ and $B$ is defined by
recursion on $A$. If $A$ is empty, it is $B$. If $A$ has root key $x$, left subtree $L$ and right
subtree $R$, it is the node with key $x$, left subtree $L$ and right subtree the merge of $R$ and
$B$, whose cached size is the sum of the cached root sizes of its children plus one, an empty
child counting as zero. Thus $B$ is attached below the rightmost path of $A$, and every node on
that path gets a recomputed cache.

The merge is intended for trees in which every key of $A$ is smaller than every key of $B$, but it
is defined for all pairs of trees. For any two trees, erasing the caches of the result gives
`BinarySearchTree.join` of the erased trees (`erase_merge`); `ordered_merge` shows that the
result is ordered when both trees are ordered and separated in this way.
-/
public def merge {α : Type u} : Tree α → Tree α → Tree α
  | .nil, right => right
  | .node entry left right, other => node entry.key left (merge right other)

/--
**Deletion from an order-statistic tree.** Deleting a key $k$ from an order-statistic tree over a
linearly ordered type follows the comparison path from the root. The empty tree stays empty. At a
node with key $x$, left subtree $L$ and right subtree $R$: if $k < x$, the result is the node with
key $x$, left subtree the deletion of $k$ from $L$ and right subtree $R$; if $x < k$, it is the
node with key $x$, left subtree $L$ and right subtree the deletion of $k$ from $R$; otherwise
($k = x$) it is the merge of $L$ and $R$. Each rebuilt node gets as cached size the sum of the
cached root sizes of its children plus one, an empty child counting as zero.

If $k$ does not occur in the tree, the result has the same keys.
-/
public def delete {α : Type u} [LinearOrder α] (key : α) : Tree α → Tree α
  | .nil => .nil
  | .node entry left right =>
      if key < entry.key then node entry.key (delete key left) right
      else if entry.key < key then node entry.key left (delete key right)
      else merge left right

/-- **Order-statistic merge preserves cache correctness.** Let $A$ and $B$ be order-statistic trees
whose cached subtree size at every node equals the number of nodes in that node's subtree. Then
the merge of $A$ and $B$ has the same property. No ordering between the keys of $A$ and $B$ is
assumed. -/
public theorem cacheCorrect_merge {α : Type u} {left right : Tree α}
    (hLeft : CacheCorrect left) (hRight : CacheCorrect right) :
    CacheCorrect (merge left right) := by
  induction left generalizing right with
  | nil => exact hRight
  | node entry subLeft subRight _ihLeft ihRight =>
    rcases hLeft with ⟨hSubLeft, hSubRight, -⟩
    simp [merge, cacheCorrect_node hSubLeft (ihRight hSubRight hRight)]

/-- **Order-statistic deletion preserves cache correctness.** Let $\alpha$ be a linearly ordered
type, $k \in \alpha$ a key and $T$ an order-statistic tree over $\alpha$. If the cached subtree size
at every node of $T$ equals the number of nodes in that node's subtree, then the same holds for the
tree obtained by deleting $k$ from $T$. -/
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

/--
Erasing the caches of a merge gives `BinarySearchTree.join` of the erased trees,
for any two trees, with no ordering, separation, or cache hypothesis.
-/
public theorem erase_merge {α : Type u} (left right : Tree α) :
    erase (merge left right) = BinarySearchTree.join (erase left) (erase right) := by
  induction left generalizing right with
  | nil => rfl
  | node entry subLeft subRight _ihLeft ihRight =>
    simp [merge, BinarySearchTree.join, erase, erase_node, ihRight]

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
    · simp [hLeft, erase_node, ihLeft]
    · by_cases hRight : entry.key < key
      · simp [hLeft, hRight, erase_node, ihRight]
      · simp [hLeft, hRight, erase_merge]

/-- **Merging separated ordered order-statistic trees preserves order.** Let $\alpha$ be a
linearly ordered type and let $L$ and $R$ be ordered order-statistic trees over $\alpha$ such
that $x < y$ for every key $x$ of $L$ and every key $y$ of $R$. Then the merge of $L$ and $R$
is ordered. -/
public theorem ordered_merge {α : Type u} [LinearOrder α] {left right : Tree α}
    (hLeft : Ordered left) (hRight : Ordered right)
    (hSeparated : ∀ x ∈ left, ∀ y ∈ right, x < y) : Ordered (merge left right) := by
  change BinarySearchTree.Ordered (erase (merge left right))
  rw [erase_merge]
  exact BinarySearchTree.ordered_join hLeft hRight hSeparated

/-- **Deletion preserves order in an order-statistic tree.** Let $\alpha$ be a linearly ordered
type and let $T$ be an order-statistic tree over $\alpha$ that is ordered, that is, after its
cached sizes are removed, every key in a left subtree is strictly smaller than the key of its node
and every key in a right subtree is strictly larger. Then for every key $k$, the tree obtained
from $T$ by deleting $k$ is again ordered. -/
public theorem ordered_delete {α : Type u} [LinearOrder α] {key : α}
    {tree : Tree α} (hTree : Ordered tree) : Ordered (delete key tree) := by
  change BinarySearchTree.Ordered (erase (delete key tree))
  rw [erase_delete]
  exact BinarySearchTree.ordered_delete hTree

/-- **Inorder traversal of an order-statistic merge.** For order-statistic trees $A$ and $B$, the
inorder traversal of the merge of $A$ and $B$ is the inorder traversal of $A$ followed by the
inorder traversal of $B$. No ordering between the keys of $A$ and $B$ is assumed. -/
public theorem inorder_merge {α : Type u} {left right : Tree α} :
    inorder (merge left right) = inorder left ++ inorder right := by
  change BinarySearchTree.inorder (erase (merge left right)) = _
  rw [erase_merge]
  exact BinarySearchTree.inorder_join

/-- **Keys of an order-statistic merge.** For order-statistic trees $A$ and $B$ over a type $\alpha$
and any $x \in \alpha$, $x$ is a key of the merge of $A$ and $B$ if and only if $x$ is a key of $A$
or a key of $B$. No ordering between the keys of $A$ and $B$ is assumed. -/
public theorem mem_merge {α : Type u} {x : α} {left right : Tree α} :
    x ∈ merge left right ↔ x ∈ left ∨ x ∈ right := by
  change x ∈ erase (merge left right) ↔ x ∈ erase left ∨ x ∈ erase right
  rw [erase_merge]
  exact BinarySearchTree.mem_join

/-- **Inorder traversal after order-statistic deletion.** Let $\alpha$ be a linearly ordered type,
$k \in \alpha$ and $T$ an ordered order-statistic tree over $\alpha$ (at every node, all keys of
the left subtree are smaller and all keys of the right subtree are larger than the node's key).
The inorder traversal of the tree obtained by deleting $k$ from $T$ is the inorder traversal of
$T$ with every occurrence of $k$ removed.

The inorder list of an ordered tree has no duplicates, so this agrees with the `List.erase` form
of `BinarySearchTree.inorder_delete`. -/
public theorem inorder_delete {α : Type u} [LinearOrder α] {key : α} {tree : Tree α}
    (hTree : Ordered tree) :
    inorder (delete key tree) = (inorder tree).filter (· ≠ key) := by
  change BinarySearchTree.inorder (erase (delete key tree)) =
    (BinarySearchTree.inorder (erase tree)).filter (· ≠ key)
  rw [erase_delete, BinarySearchTree.inorder_delete hTree,
    (BinarySearchTree.inorder_nodup hTree).erase_eq_filter]
  simp only [bne, Bool.beq_eq_decide_eq, decide_not]

/-- **Keys of an order-statistic tree after deletion.** Let $\alpha$ be a linearly ordered type,
$k \in \alpha$ and $T$ an ordered order-statistic tree over $\alpha$ (at every node, all keys of
the left subtree are smaller and all keys of the right subtree are larger than the node's key).
For every $y \in \alpha$, $y$ is a key of the tree obtained by deleting $k$ from $T$ if and only
if $y$ is a key of $T$ and $y \ne k$. -/
public theorem mem_delete_iff {α : Type u} [LinearOrder α] {key y : α} {tree : Tree α}
    (hTree : Ordered tree) : y ∈ delete key tree ↔ y ∈ tree ∧ y ≠ key := by
  change y ∈ erase (delete key tree) ↔ y ∈ erase tree ∧ y ≠ key
  rw [erase_delete]
  exact BinarySearchTree.mem_delete hTree

/-- **Deleted key is absent after deletion from an ordered order-statistic tree.** Let $\alpha$ be a
linearly ordered type, $k \in \alpha$ and $T$ an ordered order-statistic tree over $\alpha$ (at
every node, all keys of the left subtree are smaller and all keys of the right subtree are larger
than the node's key). Then $k$ is not a key of the tree obtained by deleting $k$ from $T$. -/
public theorem not_mem_delete {α : Type u} [LinearOrder α] {key : α} {tree : Tree α}
    (hTree : Ordered tree) : key ∉ delete key tree :=
  fun hKey => ((mem_delete_iff hTree).mp hKey).2 rfl

/-- **Search misses a key deleted from an ordered order-statistic tree.** Let $\alpha$ be a linearly
ordered type, $k \in \alpha$ and $T$ an ordered order-statistic tree over $\alpha$ (at every node,
all keys of the left subtree are smaller and all keys of the right subtree are larger than the
node's key). Comparison search for $k$ in the tree obtained by deleting $k$ from $T$ returns
false. -/
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

/-- **Rank after deletion in an order-statistic tree.** Let $\alpha$ be a linearly ordered type
and let $T$ be an order-statistic tree over $\alpha$ that is ordered and whose cached subtree
sizes are correct. Let $k$ and $q$ be keys and let $T'$ be the tree obtained from $T$ by
deleting $k$. Then the rank of $q$ in $T'$, computed by navigation with cached sizes, equals the
number of entries strictly smaller than $q$ in the inorder traversal of $T'$ with its cached
sizes removed. -/
public theorem rank_delete_eq_bstRank {α : Type u} [LinearOrder α] {key query : α}
    {tree : Tree α} (hCache : CacheCorrect tree) (hTree : Ordered tree) :
    rank query (delete key tree) =
      BinarySearchTree.rank query (erase (delete key tree)) :=
  rank_eq_bstRank (cacheCorrect_delete hCache) (ordered_delete hTree)

/-- **Selection after deletion in an order-statistic tree.** Let $\alpha$ be a linearly ordered
type and let $T$ be an order-statistic tree over $\alpha$ whose cached subtree sizes are correct.
Let $k$ be a key and let $T'$ be the tree obtained from $T$ by deleting $k$. Then for every
natural number $i$, selecting position $i$ in $T'$ by navigation with cached sizes returns the
entry at zero-based position $i$ of the inorder traversal of $T'$ with its cached sizes removed,
and returns nothing when that traversal has at most $i$ entries. -/
public theorem select_delete_eq_bstSelect {α : Type u} [LinearOrder α] {key : α}
    {tree : Tree α} (hCache : CacheCorrect tree) (index : Nat) :
    select (delete key tree) index =
      BinarySearchTree.select (erase (delete key tree)) index :=
  select_eq_bstSelect (cacheCorrect_delete hCache) index

/-- **Selecting the rank of a surviving key after deletion.** Let $\alpha$ be a linearly ordered
type, let $T$ be an order-statistic tree over $\alpha$ that is ordered and whose cached subtree
sizes are correct, let $k$ be a key, and let $T'$ be the tree obtained from $T$ by deleting $k$.
If $y$ is a key of $T'$, then selecting, with cached sizes, the position in $T'$ given by the
cached rank of $y$ in $T'$ returns $y$. -/
public theorem select_rank_delete {α : Type u} [LinearOrder α] {key y : α}
    {tree : Tree α} (hCache : CacheCorrect tree) (hTree : Ordered tree)
    (hy : y ∈ delete key tree) :
    select (delete key tree) (rank y (delete key tree)) = some y :=
  select_rank (cacheCorrect_delete hCache) (ordered_delete hTree) hy

end OrderStatisticTree
end Cslib.Algorithms.Lean
