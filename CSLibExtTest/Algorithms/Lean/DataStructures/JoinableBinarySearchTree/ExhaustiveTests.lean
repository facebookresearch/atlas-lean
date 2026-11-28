/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.RedBlackJoin
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.AvlJoin
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.TwoThreeJoin

/-!
# Exhaustive `by decide` sweep over all depth ≤ 2 trees

Every example below is a single `by decide` over an enumeration of all
trees of depth at most 2 (restricted, where the operation needs it, to
binary search trees / AVL trees / complete 2–3-trees). The operations
checked are the kernel-computable ones: the generic framework
instantiated with the trivial `join`, `baliL` / `baliR` / `paint`,
`balL` / `balR` / `avlJoin`, and `joinL23` / `joinR23` / `join23`.
The well-founded `joinL` / `joinR` / `rbtJoin` / `sjoinL` / `sjoinR` /
`sjoin` do not reduce in the kernel and are covered by the proved
theorems in the feature tests instead.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.Exhaustive

/-- Inorder key list. -/
private def keys {β : Type} : Tree Nat β → List Nat
  | .Leaf => []
  | .Node l (a, _) r => keys l ++ a :: keys r

/-- The trivial `JoinData`: `join` builds a node, `inv` is `True`. -/
private def naiveJoinData : JoinData Nat Unit where
  join l a r := Tree.Node l (a, ()) r
  inv _ := True
  inv_leaf := trivial
  set_join _ _ _ := rfl
  bst_join _ _ _ _ h := h
  inv_join _ _ _ _ _ := trivial
  inv_node _ _ _ _ := ⟨trivial, trivial⟩

/-- Insert into a sorted duplicate-free list, dropping duplicates. -/
private def insertOrd : Nat → List Nat → List Nat
  | x, [] => [x]
  | x, y :: ys =>
      if x < y then x :: y :: ys
      else if y < x then y :: insertOrd x ys
      else y :: ys

/-- Sorted merge of two sorted duplicate-free lists, dropping duplicates.
Defined by a fold so that it reduces in the kernel (the two-list
recursion would need well-founded recursion). -/
private def mergeDedup (xs ys : List Nat) : List Nat := xs.foldr insertOrd ys

/-- Sorted intersection of two sorted duplicate-free lists. -/
private def listInter (xs ys : List Nat) : List Nat :=
  xs.filter (fun x => ys.contains x)

/-- Sorted difference of two sorted duplicate-free lists. -/
private def listDiff (xs ys : List Nat) : List Nat :=
  xs.filter (fun x => !ys.contains x)

/-- Delete from a sorted duplicate-free list. -/
private def deleteOrd : Nat → List Nat → List Nat
  | _, [] => []
  | x, y :: ys => if x = y then ys else y :: deleteOrd x ys

/-- Boolean binary-search-tree check (all left keys `<` the root, all
right keys `>` the root, recursively). -/
private def isBST {β : Type} : Tree Nat β → Bool
  | .Leaf => true
  | .Node l (a, _) r =>
      isBST l && isBST r &&
        (keys l).all (fun x => decide (x < a)) &&
        (keys r).all (fun x => decide (a < x))

/-- All `Tree Nat Unit` trees of depth at most `n`, keys `{0, 1, 2}`. -/
private def treesUpTo : Nat → List (Tree Nat Unit)
  | 0 => [Tree.Leaf]
  | n + 1 => treesUpTo n ++
      (treesUpTo n).flatMap fun l =>
        (treesUpTo n).flatMap fun r =>
          [Tree.Node l (0, ()) r, Tree.Node l (1, ()) r, Tree.Node l (2, ()) r]

/-- All `Tree Nat Color` trees of depth at most `n`, key `{0}`. -/
private def colorTreesUpTo : Nat → List (Tree Nat Color)
  | 0 => [Tree.Leaf]
  | n + 1 => colorTreesUpTo n ++
      (colorTreesUpTo n).flatMap fun l =>
        (colorTreesUpTo n).flatMap fun r =>
          [Tree.Node l (0, Color.Red) r, Tree.Node l (0, Color.Black) r]

/-- Boolean AVL check, mirroring `avl` exactly. -/
private def isAVL : Tree Nat Nat → Bool
  | .Leaf => true
  | .Node l (_, n) r =>
      decide (((height l : ℤ) - (height r : ℤ)).natAbs ≤ 1) &&
        decide (n = max (height l) (height r) + 1) && isAVL l && isAVL r

/-- All `Tree Nat Nat` trees of depth at most `n`, keys `{0, 1, 2}`,
stored heights `{0, 1, 2}`. -/
private def avlTreesUpTo : Nat → List (Tree Nat Nat)
  | 0 => [Tree.Leaf]
  | n + 1 => avlTreesUpTo n ++
      (avlTreesUpTo n).flatMap fun l =>
        (avlTreesUpTo n).flatMap fun r =>
          [Tree.Node l (0, 0) r, Tree.Node l (0, 1) r, Tree.Node l (0, 2) r,
           Tree.Node l (1, 0) r, Tree.Node l (1, 1) r, Tree.Node l (1, 2) r,
           Tree.Node l (2, 0) r, Tree.Node l (2, 1) r, Tree.Node l (2, 2) r]

/-- Boolean completeness check, mirroring `complete23` exactly. -/
private def isComplete23 : Tree23 Nat → Bool
  | .Leaf => true
  | .Node2 l _ r =>
      decide (height23 l = height23 r) && isComplete23 l && isComplete23 r
  | .Node3 l _ m _ r =>
      decide (height23 l = height23 m) && decide (height23 m = height23 r) &&
        isComplete23 l && isComplete23 m && isComplete23 r

/-- All `Tree23 Nat` trees of depth at most `n`, key `{0}`. -/
private def tree23UpTo : Nat → List (Tree23 Nat)
  | 0 => [Tree23.Leaf]
  | n + 1 => tree23UpTo n ++
      (tree23UpTo n).flatMap fun l =>
        (tree23UpTo n).flatMap fun r =>
          ([Tree23.Node2 l 0 r] ++
            ((tree23UpTo n).flatMap fun m => [Tree23.Node3 l 0 m 0 r]))

/-- Generic `union` / `inter` / `diff` / `diff1` on all depth ≤ 2 BSTs. -/
example : ∀ t₁ ∈ (treesUpTo 2).filter isBST, ∀ t₂ ∈ (treesUpTo 2).filter isBST,
    keys (union naiveJoinData t₁ t₂) = mergeDedup (keys t₁) (keys t₂) ∧
    keys (inter naiveJoinData t₁ t₂) = listInter (keys t₁) (keys t₂) ∧
    keys (diff naiveJoinData t₁ t₂) = listDiff (keys t₁) (keys t₂) ∧
    keys (diff1 naiveJoinData t₁ t₂) = listDiff (keys t₁) (keys t₂) := by decide

/-- Generic `insert` / `delete` / `insert'` / `delete'` on all depth ≤ 2 BSTs. -/
example : ∀ t ∈ (treesUpTo 2).filter isBST, ∀ x ∈ [0, 1, 2],
    keys (insert naiveJoinData x t) = insertOrd x (keys t) ∧
    keys (delete naiveJoinData x t) = deleteOrd x (keys t) ∧
    keys (insert' naiveJoinData x t) = insertOrd x (keys t) ∧
    keys (delete' naiveJoinData x t) = deleteOrd x (keys t) := by decide

/-- Generic `split` on all depth ≤ 2 BSTs. -/
example : ∀ t ∈ (treesUpTo 2).filter isBST, ∀ x ∈ [0, 1, 2],
    keys (split naiveJoinData x t).1 = (keys t).filter (fun y => decide (y < x)) ∧
    keys (split naiveJoinData x t).2.2 = (keys t).filter (fun y => decide (x < y)) ∧
    (split naiveJoinData x t).2.1 = (keys t).contains x := by decide

/-- Generic `join2` on separated depth ≤ 2 BSTs (all left keys `<` all
right keys). -/
example : ∀ l ∈ (treesUpTo 2).filter isBST, ∀ r ∈ (treesUpTo 2).filter isBST,
    ((keys l).all (fun x => (keys r).all (fun y => decide (x < y)))) = true →
    keys (join2 naiveJoinData l r) = keys l ++ keys r := by decide

/-- Generic `split_min` on all depth ≤ 2 BSTs. -/
example : ∀ t ∈ (treesUpTo 2).filter isBST,
    (split_min naiveJoinData t).map (fun p => (p.1, keys p.2)) =
      (keys t).head?.map (fun m => (m, (keys t).tail)) := by decide

/-- `baliL` / `baliR` / `paint` on all depth ≤ 2 red–black-shaped trees. -/
example : ∀ l ∈ colorTreesUpTo 2, ∀ r ∈ colorTreesUpTo 2, ∀ a ∈ [0, 1],
    keys (baliL l a r) = keys l ++ a :: keys r ∧
    keys (baliR l a r) = keys l ++ a :: keys r ∧
    tsize (baliL l a r) = tsize l + tsize r + 1 ∧
    tsize (baliR l a r) = tsize l + tsize r + 1 ∧
    keys (paint Color.Black l) = keys l ∧ tsize (paint Color.Black l) = tsize l := by decide

/-- All `Tree Nat Nat` trees of depth at most `n`, key `{0}`, stored
heights `{0, 1, 2}` — a smaller enumeration for the `balL` / `balR`
sweep (the full one would exceed the kernel recursion depth). -/
private def avlTreesUpTo0 : Nat → List (Tree Nat Nat)
  | 0 => [Tree.Leaf]
  | n + 1 => avlTreesUpTo0 n ++
      (avlTreesUpTo0 n).flatMap fun l =>
        (avlTreesUpTo0 n).flatMap fun r =>
          [Tree.Node l (0, 0) r, Tree.Node l (0, 1) r, Tree.Node l (0, 2) r]

/-- `balL` / `balR` preserve inorder on all depth ≤ 2 stored-height trees. -/
example : ∀ l ∈ avlTreesUpTo0 2, ∀ r ∈ avlTreesUpTo0 2, ∀ a ∈ [0, 1, 2],
    keys (balL l a r) = keys l ++ a :: keys r ∧
    keys (balR l a r) = keys l ++ a :: keys r := by decide

/-- `avlJoin` preserves inorder on all depth ≤ 2 AVL trees. -/
example : ∀ l ∈ (avlTreesUpTo 2).filter isAVL, ∀ r ∈ (avlTreesUpTo 2).filter isAVL,
    ∀ a ∈ [0, 1, 2], keys (avlJoin l a r) = keys l ++ a :: keys r := by decide

set_option maxRecDepth 8192 in
/-- `avlJoin` on separated AVL BSTs: sorted merge plus the height bound. -/
example : ∀ l ∈ (avlTreesUpTo 2).filter (fun t => isAVL t && isBST t),
    ∀ r ∈ (avlTreesUpTo 2).filter (fun t => isAVL t && isBST t), ∀ a ∈ [0, 1, 2],
    ((keys l).all (fun x => decide (x < a))) = true →
    ((keys r).all (fun x => decide (a < x))) = true →
    keys (avlJoin l a r) = keys l ++ a :: keys r ∧
    (height (avlJoin l a r) = max (height l) (height r) ∨
      height (avlJoin l a r) = max (height l) (height r) + 1) := by decide

/-- `join23` on all depth ≤ 2 complete 2–3-trees: inorder, completeness,
and the height bound. -/
example : ∀ l ∈ (tree23UpTo 2).filter isComplete23,
    ∀ r ∈ (tree23UpTo 2).filter isComplete23, ∀ a ∈ [0, 1, 2],
    inorder23 (join23 l a r) = inorder23 l ++ a :: inorder23 r ∧
    isComplete23 (join23 l a r) = true ∧
    (height23 (join23 l a r) = max (height23 l) (height23 r) ∨
      height23 (join23 l a r) = max (height23 l) (height23 r) + 1) := by decide

/-- `joinL23` / `joinR23` on all depth ≤ 2 complete 2–3-trees, on
precondition (one side strictly shorter). -/
example : ∀ l ∈ (tree23UpTo 2).filter isComplete23,
    ∀ r ∈ (tree23UpTo 2).filter isComplete23, ∀ a ∈ [0, 1, 2],
    (height23 l < height23 r →
      inorder23 (treei (joinL23 l a r)) = inorder23 l ++ a :: inorder23 r ∧
      hi23 (joinL23 l a r) = height23 r) ∧
    (height23 r < height23 l →
      inorder23 (treei (joinR23 l a r)) = inorder23 l ++ a :: inorder23 r ∧
      hi23 (joinR23 l a r) = height23 l) := by decide

end Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.Exhaustive
