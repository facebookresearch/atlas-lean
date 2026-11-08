/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.AvlTree

/-!
# AVL tree deletion

Deletion for the height-balanced binary search trees of
`CSLibExt.Algorithms.Lean.DataStructures.AvlTree`. Deletion follows the search
path exactly as in an ordinary binary search tree and rebuilds every node on
that path with the rebalancing function `balance` from the parent module. A
deleted node with at most one child is replaced by that child. A deleted node
with two children is replaced by the minimum key of its right subtree, with
that minimum removed by `eraseMin`. Deletion can shrink the height of the
affected subtree by at most one, so at each rebuilt node the two children
differ in height by at most two, which is exactly the precondition of
`balanced_balance`.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace AvlTree

variable {α : Type u}

/--
The leftmost key of a tree, or the given default for the empty tree. For a
nonempty tree the result does not depend on the default: see
`inorder_eq_minD_cons_eraseMin`.
-/
public def minD : α → Tree α → α
  | default, .empty => default
  | _, .node _ left key _ => minD key left

/-- Remove the leftmost key of a tree, rebalancing on the way back up. -/
public def eraseMin : Tree α → Tree α
  | .empty => .empty
  | .node _ left key right =>
      match left with
      | .empty => right
      | .node _ _ _ _ => balance (eraseMin left) key right

/-- `eraseMin` under the name used for the successor step of deletion. -/
public def deleteMin : Tree α → Tree α :=
  eraseMin

/--
Delete a key, rebalancing every node on the search path. A deleted node with
two children takes the minimum key of its right subtree as its new key and
deletes that minimum with `eraseMin`.
-/
public def erase [LinearOrder α] (x : α) : Tree α → Tree α
  | .empty => .empty
  | .node _ left key right =>
      if x < key then balance (erase x left) key right
      else if key < x then balance left key (erase x right)
      else
        match left, right with
        | .empty, _ => right
        | _, .empty => left
        | _, _ => balance left (minD key right) (deleteMin right)

/-- `erase` under its alternative name. -/
public def delete [LinearOrder α] (x : α) (tree : Tree α) : Tree α :=
  erase x tree

/-! ## Membership and `All` -/

@[simp] private theorem mem_empty_iff {x : α} :
    x ∈ (Tree.empty : Tree α) ↔ False :=
  Iff.rfl

@[simp] private theorem mem_node_iff {x key : α} {cached : Nat} {left right : Tree α} :
    x ∈ Tree.node cached left key right ↔ x ∈ left ∨ x = key ∨ x ∈ right :=
  Iff.rfl

@[simp] private theorem mem_mkNode_iff {x key : α} {left right : Tree α} :
    x ∈ mkNode left key right ↔ x ∈ left ∨ x = key ∨ x ∈ right :=
  Iff.rfl

private theorem all_balance {p : α → Prop} {key : α} {left right : Tree α}
    (hLeft : All p left) (hKey : p key) (hRight : All p right) :
    All p (balance left key right) := by
  rw [all_iff_forall_mem]
  intro y hy
  rw [mem_balance] at hy
  rcases hy with hy | rfl | hy
  · exact (all_iff_forall_mem.mp hLeft) y hy
  · exact hKey
  · exact (all_iff_forall_mem.mp hRight) y hy

private theorem all_of_mem_subset {p : α → Prop} {small big : Tree α}
    (hSubset : ∀ y, y ∈ small → y ∈ big) (hBig : All p big) : All p small :=
  all_iff_forall_mem.mpr
    (fun y hy => (all_iff_forall_mem.mp hBig) y (hSubset y hy))

private theorem all_mono' {p q : α → Prop} (h : ∀ a, p a → q a) {tree : Tree α}
    (hTree : All p tree) : All q tree :=
  all_iff_forall_mem.mpr
    (fun y hy => h y ((all_iff_forall_mem.mp hTree) y hy))

/-! ## Height bounds for `balance` -/

/--
If two old children were balanced against each other and each new child has
shrunk by at most one, rebalancing the new children recovers at least the old
maximum height. This is the arithmetic heart of "deletion shrinks the height
by at most one": with no rotation the rebuilt node gains the `+1` of
`mkNode`, and with a rotation the tall side cannot be the side that shrank
past the old maximum.
-/
private theorem max_old_le_height_balance {key : α} {newLeft newRight : Tree α}
    {oldLeft oldRight : Nat}
    (hCacheLeft : CacheCorrect newLeft) (hCacheRight : CacheCorrect newRight)
    (hLeftLe : height newLeft ≤ oldLeft) (hLeftShrink : oldLeft ≤ height newLeft + 1)
    (hRightLe : height newRight ≤ oldRight)
    (hRightShrink : oldRight ≤ height newRight + 1)
    (hBalLeft : oldLeft ≤ oldRight + 1) (hBalRight : oldRight ≤ oldLeft + 1) :
    max oldLeft oldRight ≤ height (balance newLeft key newRight) := by
  by_cases hTallLeft : height newRight + 1 < height newLeft
  · have hWeak : max (height newLeft) (height newRight) ≤
        height (balance newLeft key newRight) :=
      le_height_balance hCacheLeft hCacheRight
    omega
  · by_cases hTallRight : height newLeft + 1 < height newRight
    · have hWeak : max (height newLeft) (height newRight) ≤
          height (balance newLeft key newRight) :=
        le_height_balance hCacheLeft hCacheRight
      omega
    · rw [balance_eq_mkNode_of_le (by omega) (by omega)]
      simp only [height_mkNode]
      omega

/-! ## The minimum key and `eraseMin` -/

@[simp] private theorem minD_empty {default : α} : minD default (.empty : Tree α) = default :=
  rfl

private theorem minD_node {default key : α} {cached : Nat} {left right : Tree α} :
    minD default (.node cached left key right) = minD key left :=
  rfl

private theorem eraseMin_node_empty {cached : Nat} {key : α} {right : Tree α} :
    eraseMin (.node cached .empty key right) = right := by
  simp [eraseMin]

private theorem eraseMin_node_node {cached cachedLeft : Nat} {key leftKey : α}
    {leftLeft leftRight right : Tree α} :
    eraseMin (.node cached (.node cachedLeft leftLeft leftKey leftRight) key right) =
      balance (eraseMin (.node cachedLeft leftLeft leftKey leftRight)) key right := by
  simp [eraseMin]

/-- The leftmost key of a nonempty tree is present in the tree. -/
public theorem minD_mem {default : α} {tree : Tree α} (hTree : tree ≠ .empty) :
    minD default tree ∈ tree := by
  induction tree generalizing default with
  | empty => exact absurd rfl hTree
  | node cached left key right ihLeft _ =>
    rw [minD_node]
    cases left with
    | empty => exact Or.inr (Or.inl rfl)
    | node cachedLeft leftLeft leftKey leftRight =>
      exact Or.inl (ihLeft (default := key) (by simp))

/-- Removing the minimum does not introduce any new keys. -/
private theorem mem_of_mem_eraseMin {y : α} {tree : Tree α}
    (hy : y ∈ eraseMin tree) : y ∈ tree := by
  induction tree with
  | empty => simp [eraseMin] at hy
  | node cached left key right ihLeft _ =>
    cases left with
    | empty =>
      rw [eraseMin_node_empty] at hy
      exact Or.inr (Or.inr hy)
    | node cachedLeft leftLeft leftKey leftRight =>
      rw [eraseMin_node_node, mem_balance] at hy
      rcases hy with hy | hy | hy
      · exact Or.inl (ihLeft hy)
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hy)

private theorem all_eraseMin {p : α → Prop} {tree : Tree α} (hTree : All p tree) :
    All p (eraseMin tree) :=
  all_of_mem_subset (fun _ hy => mem_of_mem_eraseMin hy) hTree

/-- Removing the minimum preserves correct cached heights. -/
public theorem cacheCorrect_eraseMin {tree : Tree α} (hTree : CacheCorrect tree) :
    CacheCorrect (eraseMin tree) := by
  induction tree with
  | empty => trivial
  | node cached left key right ihLeft _ =>
    obtain ⟨hLeft, hRight, -⟩ := hTree
    cases left with
    | empty =>
      rw [eraseMin_node_empty]
      exact hRight
    | node cachedLeft leftLeft leftKey leftRight =>
      rw [eraseMin_node_node]
      exact cacheCorrect_balance (ihLeft hLeft) hRight

/-- Removing the minimum never increases the height. -/
public theorem height_eraseMin_le {tree : Tree α} (hTree : CacheCorrect tree) :
    height (eraseMin tree) ≤ height tree := by
  induction tree with
  | empty => simp [eraseMin]
  | node cached left key right ihLeft _ =>
    obtain ⟨hLeft, hRight, hCached⟩ := hTree
    cases left with
    | empty =>
      rw [eraseMin_node_empty]
      simp only [height_node, height_empty] at hCached ⊢
      omega
    | node cachedLeft leftLeft leftKey leftRight =>
      rw [eraseMin_node_node]
      have hBound : height
            (balance (eraseMin (.node cachedLeft leftLeft leftKey leftRight)) key right) ≤
          max (height (eraseMin (.node cachedLeft leftLeft leftKey leftRight)))
            (height right) + 1 :=
        height_balance_le (cacheCorrect_eraseMin hLeft) hRight
      have hIH := ihLeft hLeft
      simp only [height_node] at hCached hBound hIH ⊢
      omega

/-- Removing the minimum shrinks the height of a balanced tree by at most one. -/
public theorem le_height_eraseMin {tree : Tree α}
    (hCache : CacheCorrect tree) (hBal : Balanced tree) :
    height tree ≤ height (eraseMin tree) + 1 := by
  induction tree with
  | empty => simp [eraseMin]
  | node cached left key right ihLeft _ =>
    obtain ⟨hCacheL, hCacheR, hCached⟩ := hCache
    obtain ⟨hBalL, hBalR, hBalA, hBalB⟩ := hBal
    cases left with
    | empty =>
      rw [eraseMin_node_empty]
      simp only [height_node, height_empty] at hCached ⊢
      omega
    | node cachedLeft leftLeft leftKey leftRight =>
      rw [eraseMin_node_node]
      have hMax : max (height (.node cachedLeft leftLeft leftKey leftRight)) (height right) ≤
          height (balance (eraseMin (.node cachedLeft leftLeft leftKey leftRight))
            key right) :=
        max_old_le_height_balance (cacheCorrect_eraseMin hCacheL) hCacheR
          (height_eraseMin_le hCacheL) (ihLeft hCacheL hBalL) (Nat.le_refl _)
          (Nat.le_succ _) hBalA hBalB
      simp only [height_node] at hCached hMax ⊢
      omega

/-- Removing the minimum preserves the AVL balance invariant. -/
public theorem balanced_eraseMin {tree : Tree α}
    (hCache : CacheCorrect tree) (hBal : Balanced tree) :
    Balanced (eraseMin tree) := by
  induction tree with
  | empty => trivial
  | node cached left key right ihLeft _ =>
    obtain ⟨hCacheL, hCacheR, -⟩ := hCache
    obtain ⟨hBalL, hBalR, hBalA, hBalB⟩ := hBal
    cases left with
    | empty =>
      rw [eraseMin_node_empty]
      exact hBalR
    | node cachedLeft leftLeft leftKey leftRight =>
      rw [eraseMin_node_node]
      refine balanced_balance (cacheCorrect_eraseMin hCacheL) hCacheR
        (ihLeft hCacheL hBalL) hBalR ?_ ?_
      · have hLe : height (eraseMin (.node cachedLeft leftLeft leftKey leftRight)) ≤
            height (.node cachedLeft leftLeft leftKey leftRight) :=
          height_eraseMin_le hCacheL
        omega
      · have hShrink : height (.node cachedLeft leftLeft leftKey leftRight) ≤
            height (eraseMin (.node cachedLeft leftLeft leftKey leftRight)) + 1 :=
          le_height_eraseMin hCacheL hBalL
        omega

/-- Removing the minimum preserves the search-tree ordering invariant. -/
public theorem ordered_eraseMin [LinearOrder α] {tree : Tree α}
    (hTree : Ordered tree) : Ordered (eraseMin tree) := by
  induction tree with
  | empty => trivial
  | node cached left key right ihLeft _ =>
    obtain ⟨hOrdL, hOrdR, hAllL, hAllR⟩ := hTree
    cases left with
    | empty =>
      rw [eraseMin_node_empty]
      exact hOrdR
    | node cachedLeft leftLeft leftKey leftRight =>
      rw [eraseMin_node_node]
      exact ordered_balance (ihLeft hOrdL) hOrdR (all_eraseMin hAllL) hAllR

/-- Every remaining key of an ordered tree is larger than the removed minimum. -/
public theorem all_minD_lt_eraseMin_of_ordered [LinearOrder α] {default : α} {tree : Tree α}
    (hTree : Ordered tree) : All (minD default tree < ·) (eraseMin tree) := by
  induction tree generalizing default with
  | empty => trivial
  | node cached left key right ihLeft _ =>
    obtain ⟨hOrdL, hOrdR, hAllL, hAllR⟩ := hTree
    cases left with
    | empty =>
      rw [minD_node, eraseMin_node_empty]
      exact hAllR
    | node cachedLeft leftLeft leftKey leftRight =>
      rw [minD_node, eraseMin_node_node]
      have hMinMem : minD key (.node cachedLeft leftLeft leftKey leftRight) ∈
          (.node cachedLeft leftLeft leftKey leftRight : Tree α) :=
        minD_mem (by simp)
      have hMinKey : minD key (.node cachedLeft leftLeft leftKey leftRight) < key :=
        (all_iff_forall_mem.mp hAllL) _ hMinMem
      refine all_balance (ihLeft (default := key) hOrdL) hMinKey ?_
      exact all_mono' (fun _ ha => lt_trans hMinKey ha) hAllR

/-- The inorder traversal of a nonempty tree starts with its minimum. -/
public theorem inorder_eq_minD_cons_eraseMin {default : α} {tree : Tree α}
    (hTree : tree ≠ .empty) :
    inorder tree = minD default tree :: inorder (eraseMin tree) := by
  induction tree generalizing default with
  | empty => exact absurd rfl hTree
  | node cached left key right ihLeft _ =>
    cases left with
    | empty => simp [minD_node, eraseMin_node_empty]
    | node cachedLeft leftLeft leftKey leftRight =>
      have hIH : inorder (.node cachedLeft leftLeft leftKey leftRight : Tree α) =
          minD key (.node cachedLeft leftLeft leftKey leftRight) ::
            inorder (eraseMin (.node cachedLeft leftLeft leftKey leftRight)) :=
        ihLeft (default := key) (by simp)
      simp only [inorder_node, minD_node, eraseMin_node_node, inorder_balance, hIH,
        List.cons_append]

/-! ## Deletion -/

private theorem erase_node_eq_left_empty [LinearOrder α] {x key : α} {cached : Nat}
    {right : Tree α} (hLeft : ¬ x < key) (hRight : ¬ key < x) :
    erase x (.node cached .empty key right) = right := by
  simp [erase, hLeft, hRight]

private theorem erase_node_eq_right_empty [LinearOrder α] {x key : α} {cached : Nat}
    {left : Tree α} (hLeft : ¬ x < key) (hRight : ¬ key < x) :
    erase x (.node cached left key .empty) = left := by
  cases left <;> simp [erase, hLeft, hRight]

private theorem erase_node_eq_both_node [LinearOrder α] {x key leftKey rightKey : α}
    {cached cachedLeft cachedRight : Nat}
    {leftLeft leftRight rightLeft rightRight : Tree α}
    (hLeft : ¬ x < key) (hRight : ¬ key < x) :
    erase x (.node cached (.node cachedLeft leftLeft leftKey leftRight) key
        (.node cachedRight rightLeft rightKey rightRight)) =
      balance (.node cachedLeft leftLeft leftKey leftRight)
        (minD key (.node cachedRight rightLeft rightKey rightRight))
        (eraseMin (.node cachedRight rightLeft rightKey rightRight)) := by
  simp [erase, deleteMin, hLeft, hRight]

/-- Deletion preserves correct cached heights. -/
public theorem cacheCorrect_erase [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : CacheCorrect tree) : CacheCorrect (erase x tree) := by
  induction tree with
  | empty => trivial
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hLeft, hRight, -⟩ := hTree
    by_cases hXLeft : x < key
    · simp only [erase, hXLeft, ite_true]
      exact cacheCorrect_balance (ihLeft hLeft) hRight
    · by_cases hXRight : key < x
      · simp only [erase, hXLeft, ite_false, hXRight, ite_true]
        exact cacheCorrect_balance hLeft (ihRight hRight)
      · cases left with
        | empty =>
          rw [erase_node_eq_left_empty hXLeft hXRight]
          exact hRight
        | node cachedLeft leftLeft leftKey leftRight =>
          cases right with
          | empty =>
            rw [erase_node_eq_right_empty hXLeft hXRight]
            exact hLeft
          | node cachedRight rightLeft rightKey rightRight =>
            rw [erase_node_eq_both_node hXLeft hXRight]
            exact cacheCorrect_balance hLeft (cacheCorrect_eraseMin hRight)

/-- Deletion never increases the height. -/
public theorem height_erase_le [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : CacheCorrect tree) : height (erase x tree) ≤ height tree := by
  induction tree with
  | empty => simp [erase]
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hLeft, hRight, hCached⟩ := hTree
    by_cases hXLeft : x < key
    · have hBound : height (balance (erase x left) key right) ≤
          max (height (erase x left)) (height right) + 1 :=
        height_balance_le (cacheCorrect_erase hLeft) hRight
      have hIH := ihLeft hLeft
      simp only [erase, hXLeft, ite_true, height_node]
      omega
    · by_cases hXRight : key < x
      · have hBound : height (balance left key (erase x right)) ≤
            max (height left) (height (erase x right)) + 1 :=
          height_balance_le hLeft (cacheCorrect_erase hRight)
        have hIH := ihRight hRight
        simp only [erase, hXLeft, ite_false, hXRight, ite_true, height_node]
        omega
      · cases left with
        | empty =>
          rw [erase_node_eq_left_empty hXLeft hXRight]
          simp only [height_node, height_empty] at hCached ⊢
          omega
        | node cachedLeft leftLeft leftKey leftRight =>
          cases right with
          | empty =>
            rw [erase_node_eq_right_empty hXLeft hXRight]
            simp only [height_node, height_empty] at hCached ⊢
            omega
          | node cachedRight rightLeft rightKey rightRight =>
            rw [erase_node_eq_both_node hXLeft hXRight]
            have hBound : height
                  (balance (.node cachedLeft leftLeft leftKey leftRight)
                    (minD key (.node cachedRight rightLeft rightKey rightRight))
                    (eraseMin (.node cachedRight rightLeft rightKey rightRight))) ≤
                max (height (.node cachedLeft leftLeft leftKey leftRight))
                  (height (eraseMin
                    (.node cachedRight rightLeft rightKey rightRight))) + 1 :=
              height_balance_le hLeft (cacheCorrect_eraseMin hRight)
            have hRightLe : height
                  (eraseMin (.node cachedRight rightLeft rightKey rightRight)) ≤
                height (.node cachedRight rightLeft rightKey rightRight) :=
              height_eraseMin_le hRight
            simp only [height_node] at hCached hBound hRightLe ⊢
            omega

/-- Deletion shrinks the height of a balanced tree by at most one. -/
public theorem le_height_erase [LinearOrder α] {x : α} {tree : Tree α}
    (hCache : CacheCorrect tree) (hBal : Balanced tree) :
    height tree ≤ height (erase x tree) + 1 := by
  induction tree with
  | empty => simp [erase]
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hCacheL, hCacheR, hCached⟩ := hCache
    obtain ⟨hBalL, hBalR, hBalA, hBalB⟩ := hBal
    by_cases hXLeft : x < key
    · have hMax : max (height left) (height right) ≤
          height (balance (erase x left) key right) :=
        max_old_le_height_balance (cacheCorrect_erase hCacheL) hCacheR
          (height_erase_le hCacheL) (ihLeft hCacheL hBalL) (Nat.le_refl _)
          (Nat.le_succ _) hBalA hBalB
      simp only [erase, hXLeft, ite_true, height_node]
      omega
    · by_cases hXRight : key < x
      · have hMax : max (height left) (height right) ≤
            height (balance left key (erase x right)) :=
          max_old_le_height_balance hCacheL (cacheCorrect_erase hCacheR)
            (Nat.le_refl _) (Nat.le_succ _) (height_erase_le hCacheR)
            (ihRight hCacheR hBalR) hBalA hBalB
        simp only [erase, hXLeft, ite_false, hXRight, ite_true, height_node]
        omega
      · cases left with
        | empty =>
          rw [erase_node_eq_left_empty hXLeft hXRight]
          simp only [height_node, height_empty] at hCached ⊢
          omega
        | node cachedLeft leftLeft leftKey leftRight =>
          cases right with
          | empty =>
            rw [erase_node_eq_right_empty hXLeft hXRight]
            simp only [height_node, height_empty] at hCached ⊢
            omega
          | node cachedRight rightLeft rightKey rightRight =>
            rw [erase_node_eq_both_node hXLeft hXRight]
            have hMax : max (height (.node cachedLeft leftLeft leftKey leftRight))
                  (height (.node cachedRight rightLeft rightKey rightRight)) ≤
                height (balance (.node cachedLeft leftLeft leftKey leftRight)
                  (minD key (.node cachedRight rightLeft rightKey rightRight))
                  (eraseMin (.node cachedRight rightLeft rightKey rightRight))) :=
              max_old_le_height_balance hCacheL (cacheCorrect_eraseMin hCacheR)
                (Nat.le_refl _) (Nat.le_succ _) (height_eraseMin_le hCacheR)
                (le_height_eraseMin hCacheR hBalR) hBalA hBalB
            simp only [height_node] at hCached hMax ⊢
            omega

/-- Deletion preserves the AVL balance invariant. -/
public theorem balanced_erase [LinearOrder α] {x : α} {tree : Tree α}
    (hCache : CacheCorrect tree) (hBal : Balanced tree) :
    Balanced (erase x tree) := by
  induction tree with
  | empty => trivial
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hCacheL, hCacheR, -⟩ := hCache
    obtain ⟨hBalL, hBalR, hBalA, hBalB⟩ := hBal
    by_cases hXLeft : x < key
    · simp only [erase, hXLeft, ite_true]
      refine balanced_balance (cacheCorrect_erase hCacheL) hCacheR
        (ihLeft hCacheL hBalL) hBalR ?_ ?_
      · have hLe : height (erase x left) ≤ height left := height_erase_le hCacheL
        omega
      · have hShrink : height left ≤ height (erase x left) + 1 :=
          le_height_erase hCacheL hBalL
        omega
    · by_cases hXRight : key < x
      · simp only [erase, hXLeft, ite_false, hXRight, ite_true]
        refine balanced_balance hCacheL (cacheCorrect_erase hCacheR) hBalL
          (ihRight hCacheR hBalR) ?_ ?_
        · have hShrink : height right ≤ height (erase x right) + 1 :=
            le_height_erase hCacheR hBalR
          omega
        · have hLe : height (erase x right) ≤ height right := height_erase_le hCacheR
          omega
      · cases left with
        | empty =>
          rw [erase_node_eq_left_empty hXLeft hXRight]
          exact hBalR
        | node cachedLeft leftLeft leftKey leftRight =>
          cases right with
          | empty =>
            rw [erase_node_eq_right_empty hXLeft hXRight]
            exact hBalL
          | node cachedRight rightLeft rightKey rightRight =>
            rw [erase_node_eq_both_node hXLeft hXRight]
            refine balanced_balance hCacheL (cacheCorrect_eraseMin hCacheR) hBalL
              (balanced_eraseMin hCacheR hBalR) ?_ ?_
            · have hShrink : height (.node cachedRight rightLeft rightKey rightRight) ≤
                  height (eraseMin
                    (.node cachedRight rightLeft rightKey rightRight)) + 1 :=
                le_height_eraseMin hCacheR hBalR
              omega
            · have hLe : height
                    (eraseMin (.node cachedRight rightLeft rightKey rightRight)) ≤
                  height (.node cachedRight rightLeft rightKey rightRight) :=
                height_eraseMin_le hCacheR
              omega

/-- Deletion does not introduce any new keys. -/
private theorem mem_of_mem_erase [LinearOrder α] {x y : α} {tree : Tree α}
    (hy : y ∈ erase x tree) : y ∈ tree := by
  induction tree with
  | empty => simp [erase] at hy
  | node cached left key right ihLeft ihRight =>
    by_cases hXLeft : x < key
    · simp only [erase, hXLeft, ite_true, mem_balance] at hy
      rcases hy with hy | hy | hy
      · exact Or.inl (ihLeft hy)
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hy)
    · by_cases hXRight : key < x
      · simp only [erase, hXLeft, ite_false, hXRight, ite_true, mem_balance] at hy
        rcases hy with hy | hy | hy
        · exact Or.inl hy
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (ihRight hy))
      · cases left with
        | empty =>
          rw [erase_node_eq_left_empty hXLeft hXRight] at hy
          exact Or.inr (Or.inr hy)
        | node cachedLeft leftLeft leftKey leftRight =>
          cases right with
          | empty =>
            rw [erase_node_eq_right_empty hXLeft hXRight] at hy
            exact Or.inl hy
          | node cachedRight rightLeft rightKey rightRight =>
            rw [erase_node_eq_both_node hXLeft hXRight, mem_balance] at hy
            rcases hy with hy | hy | hy
            · exact Or.inl hy
            · rw [hy]
              exact Or.inr (Or.inr (minD_mem
                (tree := (.node cachedRight rightLeft rightKey rightRight :
                  Tree α)) (by simp)))
            · exact Or.inr (Or.inr (mem_of_mem_eraseMin hy))

private theorem all_erase [LinearOrder α] {p : α → Prop} {x : α} {tree : Tree α}
    (hTree : All p tree) : All p (erase x tree) :=
  all_of_mem_subset (fun _ hy => mem_of_mem_erase hy) hTree

/-- Deletion preserves the strict search-tree invariant. -/
public theorem ordered_erase [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : Ordered tree) : Ordered (erase x tree) := by
  induction tree with
  | empty => trivial
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hOrdL, hOrdR, hAllL, hAllR⟩ := hTree
    by_cases hXLeft : x < key
    · simp only [erase, hXLeft, ite_true]
      exact ordered_balance (ihLeft hOrdL) hOrdR (all_erase hAllL) hAllR
    · by_cases hXRight : key < x
      · simp only [erase, hXLeft, ite_false, hXRight, ite_true]
        exact ordered_balance hOrdL (ihRight hOrdR) hAllL (all_erase hAllR)
      · cases left with
        | empty =>
          rw [erase_node_eq_left_empty hXLeft hXRight]
          exact hOrdR
        | node cachedLeft leftLeft leftKey leftRight =>
          cases right with
          | empty =>
            rw [erase_node_eq_right_empty hXLeft hXRight]
            exact hOrdL
          | node cachedRight rightLeft rightKey rightRight =>
            rw [erase_node_eq_both_node hXLeft hXRight]
            have hMinMem : minD key (.node cachedRight rightLeft rightKey rightRight) ∈
                (.node cachedRight rightLeft rightKey rightRight : Tree α) :=
              minD_mem (by simp)
            have hKeyMin : key < minD key (.node cachedRight rightLeft rightKey rightRight) :=
              (all_iff_forall_mem.mp hAllR) _ hMinMem
            refine ordered_balance hOrdL (ordered_eraseMin hOrdR)
              (all_mono' (fun _ ha => lt_trans ha hKeyMin) hAllL) ?_
            exact all_minD_lt_eraseMin_of_ordered (default := key) hOrdR

private theorem list_erase_cons_tail_of_ne [LinearOrder α] {a b : α} {l : List α}
    (h : b ≠ a) : (b :: l).erase a = b :: l.erase a :=
  List.erase_cons_tail (fun hb => h (beq_iff_eq.mp hb))

private theorem list_erase_append_of_not_mem_left [LinearOrder α] {x : α}
    {left right : List α} (hx : x ∉ left) :
    (left ++ right).erase x = left ++ right.erase x := by
  rw [List.erase_append, ite_eq_right hx]

private theorem list_erase_append_of_not_mem_right [LinearOrder α] {x : α}
    {left right : List α} (hx : x ∉ right) :
    (left ++ right).erase x = left.erase x ++ right := by
  by_cases hxLeft : x ∈ left
  · rw [List.erase_append, ite_eq_left hxLeft]
  · rw [List.erase_append, ite_eq_right hxLeft, List.erase_of_not_mem hx,
      List.erase_of_not_mem hxLeft]

/-- Deleting a key erases it from the inorder traversal of an ordered tree. -/
public theorem inorder_erase [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : Ordered tree) : inorder (erase x tree) = (inorder tree).erase x := by
  induction tree with
  | empty => simp [erase]
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hOrdL, hOrdR, hAllL, hAllR⟩ := hTree
    by_cases hXLeft : x < key
    · have hxRight : x ∉ inorder right := by
        rw [mem_inorder]
        intro hx
        exact lt_asymm hXLeft ((all_iff_forall_mem.mp hAllR) x hx)
      have hxCons : x ∉ key :: inorder right := by
        intro hx
        rw [List.mem_cons] at hx
        rcases hx with hx | hx
        · exact ne_of_lt hXLeft hx
        · exact hxRight hx
      simp only [erase, hXLeft, ite_true, inorder_balance, inorder_node, ihLeft hOrdL]
      exact (list_erase_append_of_not_mem_right hxCons).symm
    · by_cases hXRight : key < x
      · have hxLeft : x ∉ inorder left := by
          rw [mem_inorder]
          intro hx
          exact lt_asymm hXRight ((all_iff_forall_mem.mp hAllL) x hx)
        simp only [erase, hXLeft, ite_false, hXRight, ite_true, inorder_balance,
          inorder_node, ihRight hOrdR]
        rw [list_erase_append_of_not_mem_left hxLeft,
          list_erase_cons_tail_of_ne (ne_of_lt hXRight)]
      · have hxEq : x = key := le_antisymm (le_of_not_gt hXRight) (le_of_not_gt hXLeft)
        subst x
        have hOuter : inorder (.node cached left key right : Tree α) =
            inorder left ++ key :: inorder right :=
          inorder_node key left right
        have hKeyLeft : key ∉ inorder left := by
          rw [mem_inorder]
          intro hx
          exact lt_irrefl key ((all_iff_forall_mem.mp hAllL) key hx)
        cases left with
        | empty =>
          rw [erase_node_eq_left_empty hXLeft hXRight, hOuter]
          simp
        | node cachedLeft leftLeft leftKey leftRight =>
          cases right with
          | empty =>
            rw [erase_node_eq_right_empty hXLeft hXRight, hOuter]
            simp only [inorder_empty]
            rw [list_erase_append_of_not_mem_left hKeyLeft, List.erase_cons_head,
              List.append_nil]
          | node cachedRight rightLeft rightKey rightRight =>
            rw [erase_node_eq_both_node hXLeft hXRight, inorder_balance, hOuter,
              list_erase_append_of_not_mem_left hKeyLeft, List.erase_cons_head,
              inorder_eq_minD_cons_eraseMin (default := key)
                (tree := (.node cachedRight rightLeft rightKey rightRight : Tree α))
                (by simp)]

private theorem mem_eraseMin_or_eq_minD {default y : α} {tree : Tree α}
    (hy : y ∈ tree) : y ∈ eraseMin tree ∨ y = minD default tree := by
  by_cases hEmpty : tree = .empty
  · subst hEmpty
    simp at hy
  · have hInorder : inorder tree = minD default tree :: inorder (eraseMin tree) :=
      inorder_eq_minD_cons_eraseMin hEmpty
    have hyInorder : y ∈ inorder tree := mem_inorder.mpr hy
    rw [hInorder, List.mem_cons] at hyInorder
    rcases hyInorder with hyEq | hyInorder
    · exact Or.inr hyEq
    · exact Or.inl (mem_inorder.mp hyInorder)

/-- Deletion keeps every key other than the deleted one, ordered or not. -/
public theorem mem_erase_of_mem [LinearOrder α] {x y : α} {tree : Tree α}
    (hy : y ∈ tree) (hxy : y ≠ x) : y ∈ erase x tree := by
  induction tree with
  | empty => simp at hy
  | node cached left key right ihLeft ihRight =>
    by_cases hXLeft : x < key
    · simp only [erase, hXLeft, ite_true, mem_balance]
      rcases hy with hy | hy | hy
      · exact Or.inl (ihLeft hy)
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hy)
    · by_cases hXRight : key < x
      · simp only [erase, hXLeft, ite_false, hXRight, ite_true, mem_balance]
        rcases hy with hy | hy | hy
        · exact Or.inl hy
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (ihRight hy))
      · have hxEq : x = key := le_antisymm (le_of_not_gt hXRight) (le_of_not_gt hXLeft)
        cases left with
        | empty =>
          rw [erase_node_eq_left_empty hXLeft hXRight]
          rcases hy with hy | hy | hy
          · exact False.elim hy
          · exact absurd (hy.trans hxEq.symm) hxy
          · exact hy
        | node cachedLeft leftLeft leftKey leftRight =>
          cases right with
          | empty =>
            rw [erase_node_eq_right_empty hXLeft hXRight]
            rcases hy with hy | hy | hy
            · exact hy
            · exact absurd (hy.trans hxEq.symm) hxy
            · exact False.elim hy
          | node cachedRight rightLeft rightKey rightRight =>
            rw [erase_node_eq_both_node hXLeft hXRight, mem_balance]
            rcases hy with hy | hy | hy
            · exact Or.inl hy
            · exact absurd (hy.trans hxEq.symm) hxy
            · rcases mem_eraseMin_or_eq_minD (default := key)
                (tree := (.node cachedRight rightLeft rightKey rightRight :
                  Tree α)) hy with h | h
              · exact Or.inr (Or.inr h)
              · exact Or.inr (Or.inl h)

/-- The deleted key is absent after deletion from an ordered tree. -/
public theorem not_mem_erase_self [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : Ordered tree) : x ∉ erase x tree := by
  induction tree with
  | empty => simp [erase]
  | node cached left key right ihLeft ihRight =>
    obtain ⟨hOrdL, hOrdR, hAllL, hAllR⟩ := hTree
    by_cases hXLeft : x < key
    · simp only [erase, hXLeft, ite_true, mem_balance]
      rintro (hx | hx | hx)
      · exact ihLeft hOrdL hx
      · exact ne_of_lt hXLeft hx
      · exact lt_asymm hXLeft ((all_iff_forall_mem.mp hAllR) x hx)
    · by_cases hXRight : key < x
      · simp only [erase, hXLeft, ite_false, hXRight, ite_true, mem_balance]
        rintro (hx | hx | hx)
        · exact lt_asymm hXRight ((all_iff_forall_mem.mp hAllL) x hx)
        · exact ne_of_gt hXRight hx
        · exact ihRight hOrdR hx
      · have hxEq : x = key := le_antisymm (le_of_not_gt hXRight) (le_of_not_gt hXLeft)
        subst x
        cases left with
        | empty =>
          rw [erase_node_eq_left_empty hXLeft hXRight]
          intro hx
          exact lt_irrefl key ((all_iff_forall_mem.mp hAllR) key hx)
        | node cachedLeft leftLeft leftKey leftRight =>
          cases right with
          | empty =>
            rw [erase_node_eq_right_empty hXLeft hXRight]
            intro hx
            exact lt_irrefl key ((all_iff_forall_mem.mp hAllL) key hx)
          | node cachedRight rightLeft rightKey rightRight =>
            rw [erase_node_eq_both_node hXLeft hXRight, mem_balance]
            rintro (hx | hx | hx)
            · exact lt_irrefl key ((all_iff_forall_mem.mp hAllL) key hx)
            · have hMinMem : minD key (.node cachedRight rightLeft rightKey rightRight) ∈
                  (.node cachedRight rightLeft rightKey rightRight : Tree α) :=
                minD_mem (by simp)
              exact ne_of_lt ((all_iff_forall_mem.mp hAllR) _ hMinMem) hx
            · exact lt_irrefl key
                ((all_iff_forall_mem.mp hAllR) key (mem_of_mem_eraseMin hx))

/-- Deletion from an ordered tree removes exactly the deleted key. -/
public theorem mem_erase [LinearOrder α] {x y : α} {tree : Tree α}
    (hTree : Ordered tree) : y ∈ erase x tree ↔ y ∈ tree ∧ y ≠ x := by
  constructor
  · intro hy
    refine ⟨mem_of_mem_erase hy, ?_⟩
    rintro rfl
    exact not_mem_erase_self hTree hy
  · rintro ⟨hy, hxy⟩
    exact mem_erase_of_mem hy hxy

/-! ## The same results for `delete` and `deleteMin` -/

/-- Deletion, under the name `delete`, preserves correct cached heights. -/
public theorem cacheCorrect_delete [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : CacheCorrect tree) : CacheCorrect (delete x tree) :=
  cacheCorrect_erase hTree

/-- Deletion, under the name `delete`, preserves the balance invariant. -/
public theorem balanced_delete [LinearOrder α] {x : α} {tree : Tree α}
    (hCache : CacheCorrect tree) (hBal : Balanced tree) :
    Balanced (delete x tree) :=
  balanced_erase hCache hBal

/-- Deletion, under the name `delete`, preserves the ordering invariant. -/
public theorem ordered_delete [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : Ordered tree) : Ordered (delete x tree) :=
  ordered_erase hTree

/-- Deleting a key with `delete` erases it from the inorder traversal. -/
public theorem inorder_delete [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : Ordered tree) : inorder (delete x tree) = (inorder tree).erase x :=
  inorder_erase hTree

/-- `deleteMin` preserves correct cached heights. -/
public theorem cacheCorrect_deleteMin {tree : Tree α} (hTree : CacheCorrect tree) :
    CacheCorrect (deleteMin tree) :=
  cacheCorrect_eraseMin hTree

/-- `deleteMin` preserves the AVL balance invariant. -/
public theorem balanced_deleteMin {tree : Tree α}
    (hCache : CacheCorrect tree) (hBal : Balanced tree) :
    Balanced (deleteMin tree) :=
  balanced_eraseMin hCache hBal

/-- `deleteMin` preserves the search-tree ordering invariant. -/
public theorem ordered_deleteMin [LinearOrder α] {tree : Tree α}
    (hTree : Ordered tree) : Ordered (deleteMin tree) :=
  ordered_eraseMin hTree

end AvlTree
end Cslib.Algorithms.Lean
