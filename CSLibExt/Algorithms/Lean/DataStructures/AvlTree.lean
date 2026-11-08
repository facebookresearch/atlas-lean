/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree
public import Mathlib.Order.Defs.LinearOrder

/-!
# AVL trees

This module develops height-balanced binary search trees with a cached height at
each node. The smart constructor `mkNode` recomputes the cache from the cached
heights of the children in constant time. Insertion repairs the balance invariant
with single and double rotations, all performed by the local rebalancing function
`balance`. Insertion ignores an already-present key.

Membership, `All`, ordering, and inorder traversal are not redeveloped here: they
are inherited from `BinarySearchTree` through the cache-erasing projection
`toBinaryTree`, as in `OrderStatisticTree`. Only the height caches, the balance
invariant, rotations, and the rebalancing insertion are AVL-specific; their
specifications are the erasure equations `inorder_balance`, `mem_balance`, and
`ordered_balance` together with the height bounds for `balance`.

Deletion is out of scope for this module.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace AvlTree

/-- A binary tree with a cached height stored at each node. -/
public inductive Tree (α : Type u) where
  | empty : Tree α
  | node (height : Nat) (left : Tree α) (key : α) (right : Tree α) : Tree α
deriving DecidableEq, Repr

variable {α : Type u}

/-- The cached height of a tree, read off the root in constant time. -/
public def height : Tree α → Nat
  | .empty => 0
  | .node cached _ _ _ => cached

/-- Construct a node whose cached height is computed from its children. -/
public def mkNode (left : Tree α) (key : α) (right : Tree α) : Tree α :=
  .node (max (height left) (height right) + 1) left key right

@[simp] public theorem height_empty : height (.empty : Tree α) = 0 :=
  rfl

@[simp] public theorem height_node {cached : Nat} {left right : Tree α} {key : α} :
    height (.node cached left key right) = cached :=
  rfl

@[simp] public theorem height_mkNode {left right : Tree α} {key : α} :
    height (mkNode left key right) = max (height left) (height right) + 1 :=
  rfl

/-- Cached heights agree with the defining recursion at every node. -/
public def CacheCorrect : Tree α → Prop
  | .empty => True
  | .node cached left _ right =>
      CacheCorrect left ∧ CacheCorrect right ∧
        cached = max (height left) (height right) + 1

/-- The AVL balance invariant: at every node, the heights of the two subtrees
differ by at most one, so the balance factor lies in `{-1, 0, 1}`. -/
public def Balanced : Tree α → Prop
  | .empty => True
  | .node _ left _ right =>
      Balanced left ∧ Balanced right ∧ height left ≤ height right + 1 ∧
        height right ≤ height left + 1

/-- Remove cached heights, yielding the underlying binary search tree. -/
public def toBinaryTree : Tree α → BinaryTree α
  | .empty => .nil
  | .node _ left key right => .node key (toBinaryTree left) (toBinaryTree right)

@[simp] public theorem toBinaryTree_empty :
    toBinaryTree (.empty : Tree α) = .nil :=
  rfl

@[simp] public theorem toBinaryTree_node {cached : Nat} {left right : Tree α}
    {key : α} :
    toBinaryTree (.node cached left key right) =
      .node key (toBinaryTree left) (toBinaryTree right) :=
  rfl

@[simp] public theorem toBinaryTree_mkNode {left right : Tree α} {key : α} :
    toBinaryTree (mkNode left key right) =
      .node key (toBinaryTree left) (toBinaryTree right) :=
  rfl

/-- Structural membership, inherited from `BinarySearchTree` through
`toBinaryTree`. -/
public def Mem (x : α) (tree : Tree α) : Prop :=
  BinarySearchTree.Mem x (toBinaryTree tree)

public instance : Membership α (Tree α) :=
  ⟨fun tree x => Mem x tree⟩

@[simp] private theorem mem_empty {x : α} :
    x ∈ (Tree.empty : Tree α) ↔ False :=
  Iff.rfl

@[simp] private theorem mem_node {x key : α} {cached : Nat} {left right : Tree α} :
    x ∈ Tree.node cached left key right ↔ x ∈ left ∨ x = key ∨ x ∈ right :=
  Iff.rfl

@[simp] private theorem mem_mkNode {x key : α} {left right : Tree α} :
    x ∈ mkNode left key right ↔ x ∈ left ∨ x = key ∨ x ∈ right :=
  Iff.rfl

/-- `All p tree` states that every key in `tree` satisfies `p`; it is
`BinarySearchTree.All` of the cache-erased tree. -/
public def All (p : α → Prop) (tree : Tree α) : Prop :=
  BinarySearchTree.All p (toBinaryTree tree)

/-- Every left key is smaller and every right key is larger, recursively; it is
`BinarySearchTree.Ordered` of the cache-erased tree. -/
public def Ordered [LT α] (tree : Tree α) : Prop :=
  BinarySearchTree.Ordered (toBinaryTree tree)

/-- Append the inorder traversal of a tree to an existing suffix in linear
time; inherited from `BinarySearchTree` through `toBinaryTree`. -/
public def inorderAux (tree : Tree α) (suffix : List α) : List α :=
  BinarySearchTree.inorderAux (toBinaryTree tree) suffix

/-- The linear-time inorder traversal of a tree, inherited from
`BinarySearchTree` through `toBinaryTree`. -/
public def inorder (tree : Tree α) : List α :=
  BinarySearchTree.inorder (toBinaryTree tree)

@[simp] public theorem inorder_empty : inorder (.empty : Tree α) = [] :=
  rfl

@[simp] public theorem inorder_node {cached : Nat} (key : α) (left right : Tree α) :
    inorder (.node cached left key right) = inorder left ++ key :: inorder right :=
  BinarySearchTree.inorder_node key (toBinaryTree left) (toBinaryTree right)

@[simp] public theorem inorder_mkNode (key : α) (left right : Tree α) :
    inorder (mkNode left key right) = inorder left ++ key :: inorder right :=
  inorder_node key left right

/-- Membership in an AVL tree is `BinarySearchTree` membership in its
cache-erased tree, by definition. -/
public theorem mem_toBinaryTree {x : α} {tree : Tree α} :
    x ∈ tree ↔ x ∈ toBinaryTree tree :=
  Iff.rfl

/-- `All` on an AVL tree is `BinarySearchTree.All` of its cache-erased tree,
by definition. -/
public theorem all_toBinaryTree {p : α → Prop} {tree : Tree α} :
    All p tree ↔ BinarySearchTree.All p (toBinaryTree tree) :=
  Iff.rfl

/-- Ordering of an AVL tree is `BinarySearchTree.Ordered` of its cache-erased
tree, by definition. -/
public theorem ordered_toBinaryTree [LT α] {tree : Tree α} :
    Ordered tree ↔ BinarySearchTree.Ordered (toBinaryTree tree) :=
  Iff.rfl

/-- The inorder traversal of an AVL tree is the `BinarySearchTree` inorder
traversal of its cache-erased tree, by definition. -/
public theorem inorder_toBinaryTree (tree : Tree α) :
    inorder tree = BinarySearchTree.inorder (toBinaryTree tree) :=
  rfl

/-- Search a tree by following comparisons from its root. -/
public def contains [LinearOrder α] (x : α) : Tree α → Bool
  | .empty => false
  | .node _ left key right =>
      if x < key then contains x left
      else if key < x then contains x right
      else true

/--
Rebuild a node from children whose heights differ by at most two, restoring the
balance invariant. When the left child is too tall, a single right rotation is
performed if the left-left grandchild is at least as tall as the left-right one,
and a double left-right rotation otherwise; the right-heavy case is symmetric.
Children that already differ by at most one are rebuilt with `mkNode`.
-/
public def balance (left : Tree α) (key : α) (right : Tree α) : Tree α :=
  if height right + 1 < height left then
    match left with
    | .node _ leftLeft leftKey leftRight =>
        if height leftRight ≤ height leftLeft then
          mkNode leftLeft leftKey (mkNode leftRight key right)
        else
          match leftRight with
          | .node _ leftRightLeft leftRightKey leftRightRight =>
              mkNode (mkNode leftLeft leftKey leftRightLeft) leftRightKey
                (mkNode leftRightRight key right)
          | .empty => mkNode left key right
    | .empty => mkNode left key right
  else if height left + 1 < height right then
    match right with
    | .node _ rightLeft rightKey rightRight =>
        if height rightLeft ≤ height rightRight then
          mkNode (mkNode left key rightLeft) rightKey rightRight
        else
          match rightLeft with
          | .node _ rightLeftLeft rightLeftKey rightLeftRight =>
              mkNode (mkNode left key rightLeftLeft) rightLeftKey
                (mkNode rightLeftRight rightKey rightRight)
          | .empty => mkNode left key right
    | .empty => mkNode left key right
  else mkNode left key right

/-- Insert a key, leaving an existing equal key unchanged and rebalancing
every node on the search path. -/
public def insert [LinearOrder α] (x : α) : Tree α → Tree α
  | .empty => mkNode .empty x .empty
  | tree@(.node _ left key right) =>
      if x < key then balance (insert x left) key right
      else if key < x then balance left key (insert x right)
      else tree

/-- Build a tree by inserting the list from right to left. -/
public def fromList [LinearOrder α] : List α → Tree α
  | [] => .empty
  | x :: xs => insert x (fromList xs)

/-- `All` is equivalent to universal quantification over structural
membership; inherited from `BinarySearchTree`. -/
public theorem all_iff_forall_mem {p : α → Prop} {tree : Tree α} :
    All p tree ↔ ∀ x, x ∈ tree → p x :=
  BinarySearchTree.all_iff_forall_mem

/-- Inorder traversal contains exactly the structurally present keys;
inherited from `BinarySearchTree`. -/
public theorem mem_inorder {x : α} {tree : Tree α} :
    x ∈ inorder tree ↔ x ∈ tree :=
  BinarySearchTree.mem_inorder

/-- The inorder traversal of an ordered tree is strictly increasing;
inherited from `BinarySearchTree`. -/
public theorem ordered_inorder [LinearOrder α] {tree : Tree α}
    (hTree : Ordered tree) : List.Pairwise (· < ·) (inorder tree) :=
  BinarySearchTree.ordered_inorder hTree

/-- The inorder traversal of an ordered tree has no duplicate keys;
inherited from `BinarySearchTree`. -/
public theorem inorder_nodup [LinearOrder α] {tree : Tree α}
    (hTree : Ordered tree) : (inorder tree).Nodup :=
  BinarySearchTree.inorder_nodup hTree

private theorem All_mono {p q : α → Prop} (h : ∀ a, p a → q a) (tree : Tree α) :
    All p tree → All q tree :=
  fun hTree =>
    all_iff_forall_mem.mpr fun x hx => h x (all_iff_forall_mem.mp hTree x hx)

@[simp] private theorem all_mkNode {p : α → Prop} {key : α} {left right : Tree α} :
    All p (mkNode left key right) ↔ All p left ∧ p key ∧ All p right :=
  Iff.rfl

/-- The smart constructor produces a node with a correct cached height. -/
public theorem cacheCorrect_mkNode {key : α} {left right : Tree α}
    (hLeft : CacheCorrect left) (hRight : CacheCorrect right) :
    CacheCorrect (mkNode left key right) :=
  ⟨hLeft, hRight, rfl⟩

/-- The smart constructor preserves the balance invariant when the children
heights already differ by at most one. -/
public theorem balanced_mkNode {key : α} {left right : Tree α}
    (hLeft : Balanced left) (hRight : Balanced right)
    (hLeftRight : height left ≤ height right + 1)
    (hRightLeft : height right ≤ height left + 1) :
    Balanced (mkNode left key right) :=
  ⟨hLeft, hRight, hLeftRight, hRightLeft⟩

private theorem ordered_mkNode [LT α] {key : α} {left right : Tree α}
    (hLeft : Ordered left) (hRight : Ordered right)
    (hAllLeft : All (· < key) left) (hAllRight : All (key < ·) right) :
    Ordered (mkNode left key right) :=
  ⟨hLeft, hRight, hAllLeft, hAllRight⟩

/-- If the two sides are already height-balanced against each other,
`balance` is just `mkNode` (no rotation). -/
public theorem balance_eq_mkNode_of_le {key : α} {left right : Tree α}
    (hLeft : height left ≤ height right + 1) (hRight : height right ≤ height left + 1) :
    balance left key right = mkNode left key right := by
  unfold balance
  simp only [show ¬(height right + 1 < height left) by omega,
    show ¬(height left + 1 < height right) by omega, ite_false]

/-- Left-heavy with a left-heavy (or even) left child: `balance` performs
the single right rotation. -/
public theorem balance_left_single {key leftKey : α} {cached : Nat}
    {leftLeft leftRight right : Tree α}
    (hTall : height right + 1 < cached) (hSingle : height leftRight ≤ height leftLeft) :
    balance (.node cached leftLeft leftKey leftRight) key right =
      mkNode leftLeft leftKey (mkNode leftRight key right) := by
  unfold balance
  simp only [height_node, hTall, hSingle, ite_true]

/-- Left-heavy with a right-heavy left child: `balance` performs the
left-right double rotation. -/
public theorem balance_left_double {key leftKey leftRightKey : α}
    {cached cachedRight : Nat}
    {leftLeft leftRightLeft leftRightRight right : Tree α}
    (hTall : height right + 1 < cached) (hDouble : height leftLeft < cachedRight) :
    balance (.node cached leftLeft leftKey
        (.node cachedRight leftRightLeft leftRightKey leftRightRight)) key right =
      mkNode (mkNode leftLeft leftKey leftRightLeft) leftRightKey
        (mkNode leftRightRight key right) := by
  unfold balance
  simp only [height_node, hTall, ite_true,
    show ¬(cachedRight ≤ height leftLeft) by omega, ite_false]

/-- Right-heavy with a right-heavy (or even) right child: `balance`
performs the single left rotation. -/
public theorem balance_right_single {key rightKey : α} {cached : Nat}
    {left rightLeft rightRight : Tree α}
    (hTall : height left + 1 < cached)
    (hSingle : height rightLeft ≤ height rightRight) :
    balance left key (.node cached rightLeft rightKey rightRight) =
      mkNode (mkNode left key rightLeft) rightKey rightRight := by
  unfold balance
  simp only [height_node, show ¬(cached + 1 < height left) by omega, ite_false,
    hTall, ite_true, hSingle]

/-- Right-heavy with a left-heavy right child: `balance` performs the
right-left double rotation. -/
public theorem balance_right_double {key rightKey rightLeftKey : α}
    {cached cachedLeft : Nat}
    {left rightLeftLeft rightLeftRight rightRight : Tree α}
    (hTall : height left + 1 < cached)
    (hDouble : height rightRight < cachedLeft) :
    balance left key (.node cached
        (.node cachedLeft rightLeftLeft rightLeftKey rightLeftRight) rightKey rightRight) =
      mkNode (mkNode left key rightLeftLeft) rightLeftKey
        (mkNode rightLeftRight rightKey rightRight) := by
  unfold balance
  simp only [height_node, show ¬(cached + 1 < height left) by omega, ite_false,
    hTall, ite_true, show ¬(cachedLeft ≤ height rightRight) by omega]

/-- Rebalancing preserves correct cached heights. -/
public theorem cacheCorrect_balance {key : α} {left right : Tree α}
    (hLeft : CacheCorrect left) (hRight : CacheCorrect right) :
    CacheCorrect (balance left key right) := by
  by_cases hTallLeft : height right + 1 < height left
  · cases left with
    | empty => simp at hTallLeft
    | node cached leftLeft leftKey leftRight =>
      rcases hLeft with ⟨hLeftLeft, hLeftRight, -⟩
      simp only [height_node] at hTallLeft
      by_cases hSingle : height leftRight ≤ height leftLeft
      · rw [balance_left_single hTallLeft hSingle]
        exact cacheCorrect_mkNode hLeftLeft (cacheCorrect_mkNode hLeftRight hRight)
      · cases leftRight with
        | empty => simp at hSingle
        | node cachedRight leftRightLeft leftRightKey leftRightRight =>
          rcases hLeftRight with ⟨hLeftRightLeft, hLeftRightRight, -⟩
          simp only [height_node] at hSingle
          rw [balance_left_double hTallLeft (by omega : height leftLeft < cachedRight)]
          exact cacheCorrect_mkNode (cacheCorrect_mkNode hLeftLeft hLeftRightLeft)
            (cacheCorrect_mkNode hLeftRightRight hRight)
  · by_cases hTallRight : height left + 1 < height right
    · cases right with
      | empty => simp at hTallRight
      | node cached rightLeft rightKey rightRight =>
        rcases hRight with ⟨hRightLeft, hRightRight, -⟩
        simp only [height_node] at hTallRight
        by_cases hSingle : height rightLeft ≤ height rightRight
        · rw [balance_right_single hTallRight hSingle]
          exact cacheCorrect_mkNode (cacheCorrect_mkNode hLeft hRightLeft) hRightRight
        · cases rightLeft with
          | empty => simp at hSingle
          | node cachedLeft rightLeftLeft rightLeftKey rightLeftRight =>
            rcases hRightLeft with ⟨hRightLeftLeft, hRightLeftRight, -⟩
            simp only [height_node] at hSingle
            rw [balance_right_double hTallRight
              (by omega : height rightRight < cachedLeft)]
            exact cacheCorrect_mkNode (cacheCorrect_mkNode hLeft hRightLeftLeft)
              (cacheCorrect_mkNode hRightLeftRight hRightRight)
    · rw [balance_eq_mkNode_of_le (by omega) (by omega)]
      exact cacheCorrect_mkNode hLeft hRight

/-- Rebalancing adds at most one to the larger child height. -/
public theorem height_balance_le {key : α} {left right : Tree α}
    (hLeft : CacheCorrect left) (hRight : CacheCorrect right) :
    height (balance left key right) ≤ max (height left) (height right) + 1 := by
  by_cases hTallLeft : height right + 1 < height left
  · cases left with
    | empty => simp at hTallLeft
    | node cached leftLeft leftKey leftRight =>
      obtain ⟨hCacheLeftLeft, hCacheLeftRight, hCached⟩ := hLeft
      simp only [height_node] at hTallLeft hCached
      by_cases hSingle : height leftRight ≤ height leftLeft
      · rw [balance_left_single hTallLeft hSingle]
        simp only [height_node, height_mkNode]
        omega
      · cases leftRight with
        | empty => simp at hSingle
        | node cachedRight leftRightLeft leftRightKey leftRightRight =>
          obtain ⟨-, -, hCachedRight⟩ := hCacheLeftRight
          simp only [height_node] at hSingle hCached
          rw [balance_left_double hTallLeft (by omega : height leftLeft < cachedRight)]
          simp only [height_node, height_mkNode]
          omega
  · by_cases hTallRight : height left + 1 < height right
    · cases right with
      | empty => simp at hTallRight
      | node cached rightLeft rightKey rightRight =>
        obtain ⟨hCacheRightLeft, hCacheRightRight, hCached⟩ := hRight
        simp only [height_node] at hTallRight hCached
        by_cases hSingle : height rightLeft ≤ height rightRight
        · rw [balance_right_single hTallRight hSingle]
          simp only [height_node, height_mkNode]
          omega
        · cases rightLeft with
          | empty => simp at hSingle
          | node cachedLeft rightLeftLeft rightLeftKey rightLeftRight =>
            obtain ⟨-, -, hCachedLeft⟩ := hCacheRightLeft
            simp only [height_node] at hSingle hCached
            rw [balance_right_double hTallRight
              (by omega : height rightRight < cachedLeft)]
            simp only [height_node, height_mkNode]
            omega
    · rw [balance_eq_mkNode_of_le (by omega) (by omega)]
      simp only [height_mkNode]
      omega

/-- Rebalancing does not drop below the larger child height. -/
public theorem le_height_balance {key : α} {left right : Tree α}
    (hLeft : CacheCorrect left) (hRight : CacheCorrect right) :
    max (height left) (height right) ≤ height (balance left key right) := by
  by_cases hTallLeft : height right + 1 < height left
  · cases left with
    | empty => simp at hTallLeft
    | node cached leftLeft leftKey leftRight =>
      obtain ⟨hCacheLeftLeft, hCacheLeftRight, hCached⟩ := hLeft
      simp only [height_node] at hTallLeft hCached
      by_cases hSingle : height leftRight ≤ height leftLeft
      · rw [balance_left_single hTallLeft hSingle]
        simp only [height_node, height_mkNode]
        omega
      · cases leftRight with
        | empty => simp at hSingle
        | node cachedRight leftRightLeft leftRightKey leftRightRight =>
          obtain ⟨-, -, hCachedRight⟩ := hCacheLeftRight
          simp only [height_node] at hSingle hCached
          rw [balance_left_double hTallLeft (by omega : height leftLeft < cachedRight)]
          simp only [height_node, height_mkNode]
          omega
  · by_cases hTallRight : height left + 1 < height right
    · cases right with
      | empty => simp at hTallRight
      | node cached rightLeft rightKey rightRight =>
        obtain ⟨hCacheRightLeft, hCacheRightRight, hCached⟩ := hRight
        simp only [height_node] at hTallRight hCached
        by_cases hSingle : height rightLeft ≤ height rightRight
        · rw [balance_right_single hTallRight hSingle]
          simp only [height_node, height_mkNode]
          omega
        · cases rightLeft with
          | empty => simp at hSingle
          | node cachedLeft rightLeftLeft rightLeftKey rightLeftRight =>
            obtain ⟨-, -, hCachedLeft⟩ := hCacheRightLeft
            simp only [height_node] at hSingle hCached
            rw [balance_right_double hTallRight
              (by omega : height rightRight < cachedLeft)]
            simp only [height_node, height_mkNode]
            omega
    · rw [balance_eq_mkNode_of_le (by omega) (by omega)]
      simp only [height_mkNode]
      omega

/-- Rebalancing children whose heights differ by at most two produces a
balanced tree. This is the precondition that one insertion step maintains. -/
public theorem balanced_balance {key : α} {left right : Tree α}
    (hCacheLeft : CacheCorrect left) (hCacheRight : CacheCorrect right)
    (hBalLeft : Balanced left) (hBalRight : Balanced right)
    (hDiffLeft : height left ≤ height right + 2)
    (hDiffRight : height right ≤ height left + 2) :
    Balanced (balance left key right) := by
  by_cases hTallLeft : height right + 1 < height left
  · cases left with
    | empty => simp at hTallLeft
    | node cached leftLeft leftKey leftRight =>
      obtain ⟨hCacheLeftLeft, hCacheLeftRight, hCached⟩ := hCacheLeft
      obtain ⟨hBalLeftLeft, hBalLeftRight, hBalLeftA, hBalLeftB⟩ := hBalLeft
      simp only [height_node] at hTallLeft hDiffLeft hCached
      by_cases hSingle : height leftRight ≤ height leftLeft
      · rw [balance_left_single hTallLeft hSingle]
        refine balanced_mkNode hBalLeftLeft
          (balanced_mkNode hBalLeftRight hBalRight ?_ ?_) ?_ ?_ <;>
          (try simp only [height_mkNode]) <;> omega
      · cases leftRight with
        | empty => simp at hSingle
        | node cachedRight leftRightLeft leftRightKey leftRightRight =>
          obtain ⟨hCacheLRL, hCacheLRR, hCachedRight⟩ := hCacheLeftRight
          obtain ⟨hBalLRL, hBalLRR, hBalLRA, hBalLRB⟩ := hBalLeftRight
          simp only [height_node] at hSingle hCached hBalLeftA hBalLeftB
          rw [balance_left_double hTallLeft (by omega : height leftLeft < cachedRight)]
          refine balanced_mkNode (balanced_mkNode hBalLeftLeft hBalLRL ?_ ?_)
            (balanced_mkNode hBalLRR hBalRight ?_ ?_) ?_ ?_ <;>
            (try simp only [height_mkNode]) <;> omega
  · by_cases hTallRight : height left + 1 < height right
    · cases right with
      | empty => simp at hTallRight
      | node cached rightLeft rightKey rightRight =>
        obtain ⟨hCacheRightLeft, hCacheRightRight, hCached⟩ := hCacheRight
        obtain ⟨hBalRightLeft, hBalRightRight, hBalRightA, hBalRightB⟩ := hBalRight
        simp only [height_node] at hTallRight hDiffRight hCached
        by_cases hSingle : height rightLeft ≤ height rightRight
        · rw [balance_right_single hTallRight hSingle]
          refine balanced_mkNode (balanced_mkNode hBalLeft hBalRightLeft ?_ ?_)
            hBalRightRight ?_ ?_ <;> (try simp only [height_mkNode]) <;> omega
        · cases rightLeft with
          | empty => simp at hSingle
          | node cachedLeft rightLeftLeft rightLeftKey rightLeftRight =>
            obtain ⟨hCacheRLL, hCacheRLR, hCachedLeft⟩ := hCacheRightLeft
            obtain ⟨hBalRLL, hBalRLR, hBalRLA, hBalRLB⟩ := hBalRightLeft
            simp only [height_node] at hSingle hCached hBalRightA hBalRightB
            rw [balance_right_double hTallRight
              (by omega : height rightRight < cachedLeft)]
            refine balanced_mkNode (balanced_mkNode hBalLeft hBalRLL ?_ ?_)
              (balanced_mkNode hBalRLR hBalRightRight ?_ ?_) ?_ ?_ <;>
              (try simp only [height_mkNode]) <;> omega
    · rw [balance_eq_mkNode_of_le (by omega) (by omega)]
      exact balanced_mkNode hBalLeft hBalRight (by omega) (by omega)

/-- Rebalancing preserves the inorder traversal. -/
public theorem inorder_balance {key : α} {left right : Tree α} :
    inorder (balance left key right) = inorder left ++ key :: inorder right := by
  by_cases hTallLeft : height right + 1 < height left
  · cases left with
    | empty => simp at hTallLeft
    | node cached leftLeft leftKey leftRight =>
      simp only [height_node] at hTallLeft
      by_cases hSingle : height leftRight ≤ height leftLeft
      · rw [balance_left_single hTallLeft hSingle]
        simp [List.append_assoc]
      · cases leftRight with
        | empty => simp at hSingle
        | node cachedRight leftRightLeft leftRightKey leftRightRight =>
          simp only [height_node] at hSingle
          rw [balance_left_double hTallLeft (by omega : height leftLeft < cachedRight)]
          simp [List.append_assoc]
  · by_cases hTallRight : height left + 1 < height right
    · cases right with
      | empty => simp at hTallRight
      | node cached rightLeft rightKey rightRight =>
        simp only [height_node] at hTallRight
        by_cases hSingle : height rightLeft ≤ height rightRight
        · rw [balance_right_single hTallRight hSingle]
          simp [List.append_assoc]
        · cases rightLeft with
          | empty => simp at hSingle
          | node cachedLeft rightLeftLeft rightLeftKey rightLeftRight =>
            simp only [height_node] at hSingle
            rw [balance_right_double hTallRight
              (by omega : height rightRight < cachedLeft)]
            simp [List.append_assoc]
    · rw [balance_eq_mkNode_of_le (by omega) (by omega)]
      simp

/-- Rebalancing preserves structural membership. -/
public theorem mem_balance {x key : α} {left right : Tree α} :
    x ∈ balance left key right ↔ x ∈ left ∨ x = key ∨ x ∈ right := by
  rw [← mem_inorder, inorder_balance]
  simp [mem_inorder]

/-- Rebalancing preserves the search-tree ordering invariant. -/
public theorem ordered_balance [LinearOrder α] {key : α} {left right : Tree α}
    (hOrdLeft : Ordered left) (hOrdRight : Ordered right)
    (hAllLeft : All (· < key) left) (hAllRight : All (key < ·) right) :
    Ordered (balance left key right) := by
  by_cases hTallLeft : height right + 1 < height left
  · cases left with
    | empty => simp at hTallLeft
    | node cached leftLeft leftKey leftRight =>
      obtain ⟨hOrdLeftLeft, hOrdLeftRight, hAllLeftLeft, hAllLeftRight⟩ := hOrdLeft
      obtain ⟨hAllLeftLeftKey, hLeftKeyKey, hAllLeftRightKey⟩ := hAllLeft
      simp only [height_node] at hTallLeft
      by_cases hSingle : height leftRight ≤ height leftLeft
      · rw [balance_left_single hTallLeft hSingle]
        refine ordered_mkNode hOrdLeftLeft
          (ordered_mkNode hOrdLeftRight hOrdRight hAllLeftRightKey hAllRight)
          hAllLeftLeft ⟨hAllLeftRight, hLeftKeyKey, ?_⟩
        exact All_mono (p := (key < ·)) (q := (leftKey < ·))
          (fun _ ha => lt_trans hLeftKeyKey ha) right hAllRight
      · cases leftRight with
        | empty => simp at hSingle
        | node cachedRight leftRightLeft leftRightKey leftRightRight =>
          obtain ⟨hOrdLRL, hOrdLRR, hAllLRL, hAllLRR⟩ := hOrdLeftRight
          obtain ⟨hAllLRLKey, hLeftRightKeyKey, hAllLRRKey⟩ := hAllLeftRightKey
          obtain ⟨hAllLRLLeft, hLeftKeyLeftRightKey, hAllLRRLeft⟩ := hAllLeftRight
          simp only [height_node] at hSingle
          rw [balance_left_double hTallLeft (by omega : height leftLeft < cachedRight)]
          refine ordered_mkNode
            (ordered_mkNode hOrdLeftLeft hOrdLRL hAllLeftLeft hAllLRLLeft)
            (ordered_mkNode hOrdLRR hOrdRight hAllLRRKey hAllRight) ⟨?_, hLeftKeyLeftRightKey,
              hAllLRL⟩ ⟨hAllLRR, hLeftRightKeyKey, ?_⟩
          · exact All_mono (p := (· < leftKey)) (q := (· < leftRightKey))
              (fun _ ha => lt_trans ha hLeftKeyLeftRightKey) leftLeft hAllLeftLeft
          · exact All_mono (p := (key < ·)) (q := (leftRightKey < ·))
              (fun _ ha => lt_trans hLeftRightKeyKey ha) right hAllRight
  · by_cases hTallRight : height left + 1 < height right
    · cases right with
      | empty => simp at hTallRight
      | node cached rightLeft rightKey rightRight =>
        obtain ⟨hOrdRightLeft, hOrdRightRight, hAllRightLeft, hAllRightRight⟩ := hOrdRight
        obtain ⟨hAllRightLeftKey, hKeyRightKey, hAllRightRightKey⟩ := hAllRight
        simp only [height_node] at hTallRight
        by_cases hSingle : height rightLeft ≤ height rightRight
        · rw [balance_right_single hTallRight hSingle]
          refine ordered_mkNode
            (ordered_mkNode hOrdLeft hOrdRightLeft hAllLeft hAllRightLeftKey)
            hOrdRightRight ⟨?_, hKeyRightKey, hAllRightLeft⟩ hAllRightRight
          exact All_mono (p := (· < key)) (q := (· < rightKey))
            (fun _ ha => lt_trans ha hKeyRightKey) left hAllLeft
        · cases rightLeft with
          | empty => simp at hSingle
          | node cachedLeft rightLeftLeft rightLeftKey rightLeftRight =>
            obtain ⟨hOrdRLL, hOrdRLR, hAllRLL, hAllRLR⟩ := hOrdRightLeft
            obtain ⟨hAllRLLKey, hKeyRightLeftKey, hAllRLRKey⟩ := hAllRightLeftKey
            obtain ⟨hAllRLLRight, hRightLeftKeyRightKey, hAllRLRRight⟩ := hAllRightLeft
            simp only [height_node] at hSingle
            rw [balance_right_double hTallRight
              (by omega : height rightRight < cachedLeft)]
            refine ordered_mkNode
              (ordered_mkNode hOrdLeft hOrdRLL hAllLeft hAllRLLKey)
              (ordered_mkNode hOrdRLR hOrdRightRight hAllRLRRight hAllRightRight)
              ⟨?_, hKeyRightLeftKey, hAllRLL⟩ ⟨hAllRLR, hRightLeftKeyRightKey, ?_⟩
            · exact All_mono (p := (· < key)) (q := (· < rightLeftKey))
                (fun _ ha => lt_trans ha hKeyRightLeftKey) left hAllLeft
            · exact All_mono (p := (rightKey < ·)) (q := (rightLeftKey < ·))
                (fun _ ha => lt_trans hRightLeftKeyRightKey ha) rightRight hAllRightRight
    · rw [balance_eq_mkNode_of_le (by omega) (by omega)]
      exact ordered_mkNode hOrdLeft hOrdRight hAllLeft hAllRight

/-- Insertion preserves correct cached heights. -/
public theorem cacheCorrect_insert [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : CacheCorrect tree) : CacheCorrect (insert x tree) := by
  induction tree with
  | empty => exact cacheCorrect_mkNode trivial trivial
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hLeft, hRight, hCached⟩ := hTree
    by_cases hXLeft : x < key
    · simp only [insert, hXLeft, ite_true]
      exact cacheCorrect_balance (ihLeft hLeft) hRight
    · by_cases hXRight : key < x
      · simp only [insert, hXLeft, ite_false, hXRight, ite_true]
        exact cacheCorrect_balance hLeft (ihRight hRight)
      · have hEq : insert x (.node cached left key right) = .node cached left key right := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]
        exact ⟨hLeft, hRight, hCached⟩

/-- Insertion increases the cached height by at most one. -/
public theorem height_insert_le [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : CacheCorrect tree) : height (insert x tree) ≤ height tree + 1 := by
  induction tree with
  | empty => simp [insert]
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hLeft, hRight, hCached⟩ := hTree
    by_cases hXLeft : x < key
    · have hBound : height (balance (insert x left) key right) ≤
          max (height (insert x left)) (height right) + 1 :=
        height_balance_le (cacheCorrect_insert hLeft) hRight
      have hIH := ihLeft hLeft
      simp only [insert, hXLeft, ite_true, height_node]
      omega
    · by_cases hXRight : key < x
      · have hBound : height (balance left key (insert x right)) ≤
            max (height left) (height (insert x right)) + 1 :=
          height_balance_le hLeft (cacheCorrect_insert hRight)
        have hIH := ihRight hRight
        simp only [insert, hXLeft, ite_false, hXRight, ite_true, height_node]
        omega
      · have hEq : insert x (.node cached left key right) = .node cached left key right := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]
        omega

/-- Insertion never decreases the cached height of a balanced tree. -/
public theorem le_height_insert [LinearOrder α] {x : α} {tree : Tree α}
    (hCache : CacheCorrect tree) (hBal : Balanced tree) :
    height tree ≤ height (insert x tree) := by
  induction tree with
  | empty => simp [insert]
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hCacheL, hCacheR, hCached⟩ := hCache
    obtain ⟨hBalL, hBalR, hBalA, hBalB⟩ := hBal
    by_cases hXLeft : x < key
    · have hIH := ihLeft hCacheL hBalL
      by_cases hRot : height right + 1 < height (insert x left)
      · have hBound : max (height (insert x left)) (height right) ≤
            height (balance (insert x left) key right) :=
          le_height_balance (cacheCorrect_insert hCacheL) hCacheR
        simp only [insert, hXLeft, ite_true, height_node]
        omega
      · have hMk : balance (insert x left) key right = mkNode (insert x left) key right :=
          balance_eq_mkNode_of_le (by omega) (by omega)
        simp only [insert, hXLeft, ite_true, height_node, hMk, height_mkNode]
        omega
    · by_cases hXRight : key < x
      · have hIH := ihRight hCacheR hBalR
        by_cases hRot : height left + 1 < height (insert x right)
        · have hBound : max (height left) (height (insert x right)) ≤
              height (balance left key (insert x right)) :=
            le_height_balance hCacheL (cacheCorrect_insert hCacheR)
          simp only [insert, hXLeft, ite_false, hXRight, ite_true, height_node]
          omega
        · have hMk : balance left key (insert x right) = mkNode left key (insert x right) :=
            balance_eq_mkNode_of_le (by omega) (by omega)
          simp only [insert, hXLeft, ite_false, hXRight, ite_true, height_node, hMk,
            height_mkNode]
          omega
      · have hEq : insert x (.node cached left key right) = .node cached left key right := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]
        omega

/-- Insertion preserves the AVL balance invariant. -/
public theorem balanced_insert [LinearOrder α] {x : α} {tree : Tree α}
    (hCache : CacheCorrect tree) (hBal : Balanced tree) :
    Balanced (insert x tree) := by
  induction tree with
  | empty => exact balanced_mkNode trivial trivial (by simp) (by simp)
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hCacheL, hCacheR, hCached⟩ := hCache
    obtain ⟨hBalL, hBalR, hBalA, hBalB⟩ := hBal
    by_cases hXLeft : x < key
    · simp only [insert, hXLeft, ite_true]
      refine balanced_balance (cacheCorrect_insert hCacheL) hCacheR
        (ihLeft hCacheL hBalL) hBalR ?_ ?_
      · have hBound : height (insert x left) ≤ height left + 1 :=
          height_insert_le hCacheL
        omega
      · have hBound : height left ≤ height (insert x left) :=
          le_height_insert hCacheL hBalL
        omega
    · by_cases hXRight : key < x
      · simp only [insert, hXLeft, ite_false, hXRight, ite_true]
        refine balanced_balance hCacheL (cacheCorrect_insert hCacheR) hBalL
          (ihRight hCacheR hBalR) ?_ ?_
        · have hBound : height right ≤ height (insert x right) :=
            le_height_insert hCacheR hBalR
          omega
        · have hBound : height (insert x right) ≤ height right + 1 :=
            height_insert_le hCacheR
          omega
      · have hEq : insert x (.node cached left key right) = .node cached left key right := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]
        exact ⟨hBalL, hBalR, hBalA, hBalB⟩

/-- Inserting a key adds exactly that key to structural membership. -/
public theorem mem_insert [LinearOrder α] {x y : α} {tree : Tree α} :
    y ∈ insert x tree ↔ y = x ∨ y ∈ tree := by
  induction tree with
  | empty => simp [insert]
  | node cached left key right ihLeft ihRight =>
    by_cases hXLeft : x < key
    · simp only [insert, hXLeft, ite_true]
      simp [mem_balance, ihLeft, or_assoc, or_left_comm]
    · by_cases hXRight : key < x
      · simp only [insert, hXLeft, ite_false, hXRight, ite_true]
        simp [mem_balance, ihRight, or_left_comm]
      · have hEq : insert x (.node cached left key right) = .node cached left key right := by
          simp [insert, hXLeft, hXRight]
        have hxEq : x = key := le_antisymm (le_of_not_gt hXRight) (le_of_not_gt hXLeft)
        subst x
        rw [hEq]
        constructor
        · exact Or.inr
        · rintro (rfl | hy)
          · exact Or.inr (Or.inl rfl)
          · exact hy

private theorem all_insert [LinearOrder α] {p : α → Prop} {x : α} {tree : Tree α}
    (hx : p x) (hTree : All p tree) : All p (insert x tree) := by
  rw [all_iff_forall_mem] at hTree
  rw [all_iff_forall_mem]
  intro y hy
  rw [mem_insert] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact hTree y hy

/-- Insertion preserves the strict search-tree invariant. -/
public theorem ordered_insert [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : Ordered tree) : Ordered (insert x tree) := by
  induction tree with
  | empty =>
      simp [insert, mkNode, Ordered, toBinaryTree,
        BinarySearchTree.Ordered, BinarySearchTree.All]
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hLeft, hRight, hAllLeft, hAllRight⟩ := hTree
    by_cases hXLeft : x < key
    · simp only [insert, hXLeft, ite_true]
      exact ordered_balance (ihLeft hLeft) hRight (all_insert hXLeft hAllLeft) hAllRight
    · by_cases hXRight : key < x
      · simp only [insert, hXLeft, ite_false, hXRight, ite_true]
        exact ordered_balance hLeft (ihRight hRight) hAllLeft (all_insert hXRight hAllRight)
      · have hEq : insert x (.node cached left key right) = .node cached left key right := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]
        exact ⟨hLeft, hRight, hAllLeft, hAllRight⟩

private theorem contains_eq_bstContains [LinearOrder α] (x : α) (tree : Tree α) :
    contains x tree = BinarySearchTree.contains x (toBinaryTree tree) := by
  induction tree with
  | empty => rfl
  | node _ left key right ihLeft ihRight =>
      simp only [contains, toBinaryTree, BinarySearchTree.contains]
      by_cases hLeft : x < key
      · simp [hLeft, ihLeft]
      · by_cases hRight : key < x
        · simp [hLeft, hRight, ihRight]
        · simp [hLeft, hRight]

/-- Search is equivalent to structural membership for an ordered tree;
inherited from `BinarySearchTree` through `toBinaryTree`. -/
public theorem contains_eq_true_iff [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : Ordered tree) : contains x tree = true ↔ x ∈ tree := by
  rw [contains_eq_bstContains]
  exact BinarySearchTree.contains_eq_true_iff hTree

/-- Trees built by insertion have correct caches. -/
public theorem cacheCorrect_fromList [LinearOrder α] {xs : List α} :
    CacheCorrect (fromList xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact cacheCorrect_insert ih

/-- Trees built by insertion are balanced. -/
public theorem balanced_fromList [LinearOrder α] {xs : List α} :
    Balanced (fromList xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact balanced_insert cacheCorrect_fromList ih

/-- Building a tree by insertion always produces an ordered tree. -/
public theorem ordered_fromList [LinearOrder α] {xs : List α} :
    Ordered (fromList xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ordered_insert ih

/-- A key is in a tree built from a list exactly when it is in the list. -/
public theorem mem_fromList [LinearOrder α] {x : α} {xs : List α} :
    x ∈ fromList xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [fromList]
  | cons y ys ih => simp [fromList, mem_insert, ih]

end AvlTree
end Cslib.Algorithms.Lean
