/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Tree.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# Binary search trees

This module develops pure, unbalanced binary search trees directly over Mathlib's
`BinaryTree`. Insertion ignores an already-present key. `rank` and `select` are
traversal specifications and do not claim cached order-statistic navigation.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace BinarySearchTree

/-- Structural membership, independent of the search-tree invariant. -/
public def Mem {α : Type u} (x : α) : BinaryTree α → Prop
  | .nil => False
  | .node key left right => Mem x left ∨ x = key ∨ Mem x right

public instance {α : Type u} : Membership α (BinaryTree α) :=
  ⟨fun tree x => Mem x tree⟩

@[simp] private theorem mem_nil {α : Type u} {x : α} :
    x ∈ (BinaryTree.nil : BinaryTree α) ↔ False :=
  Iff.rfl

@[simp] private theorem mem_node {α : Type u} {x key : α}
    {left right : BinaryTree α} :
    x ∈ BinaryTree.node key left right ↔ x ∈ left ∨ x = key ∨ x ∈ right :=
  Iff.rfl

/-- Append the inorder traversal of a tree to an existing suffix in linear time. -/
public def inorderAux {α : Type u} : BinaryTree α → List α → List α
  | .nil, suffix => suffix
  | .node key left right, suffix =>
      inorderAux left (key :: inorderAux right suffix)

private theorem inorderAux_append {α : Type u} (tree : BinaryTree α)
    (xs ys : List α) :
    inorderAux tree (xs ++ ys) = inorderAux tree xs ++ ys := by
  induction tree generalizing xs with
  | nil => rfl
  | node key left right ihLeft ihRight =>
      simp only [inorderAux]
      rw [ihRight]
      change inorderAux left ((key :: inorderAux right xs) ++ ys) =
        inorderAux left (key :: inorderAux right xs) ++ ys
      exact ihLeft _

/-- The linear-time inorder traversal of a tree. -/
public def inorder {α : Type u} (tree : BinaryTree α) : List α :=
  inorderAux tree []

@[simp] public theorem inorder_nil {α : Type u} :
    inorder (.nil : BinaryTree α) = [] :=
  rfl

@[simp] public theorem inorder_node {α : Type u} (key : α)
    (left right : BinaryTree α) :
    inorder (.node key left right) = inorder left ++ key :: inorder right := by
  change inorderAux left (key :: inorderAux right []) =
    inorderAux left [] ++ key :: inorderAux right []
  simpa using inorderAux_append left [] (key :: inorderAux right [])

/-- `All p tree` states that every key in `tree` satisfies `p`. -/
public def All {α : Type u} (p : α → Prop) : BinaryTree α → Prop
  | .nil => True
  | .node key left right => All p left ∧ p key ∧ All p right

/-- Every left key is smaller and every right key is larger, recursively. -/
public def Ordered {α : Type u} [LT α] : BinaryTree α → Prop
  | .nil => True
  | .node key left right =>
      Ordered left ∧ Ordered right ∧ All (· < key) left ∧ All (key < ·) right

/--
Search a tree by following comparisons from its root.

Unlike `BinaryTree.indexOf`, this returns only membership as a Boolean;
`BinaryTree.indexOf` returns a `PosNum` encoding the root-to-node path.
-/
public def contains {α : Type u} [LinearOrder α] (x : α) : BinaryTree α → Bool
  | .nil => false
  | .node key left right =>
      if x < key then contains x left
      else if key < x then contains x right
      else true

/-- Insert a key, leaving an existing equal key unchanged. -/
public def insert {α : Type u} [LinearOrder α] (x : α) : BinaryTree α → BinaryTree α
  | .nil => .node x .nil .nil
  | tree@(.node key left right) =>
      if x < key then .node key (insert x left) right
      else if key < x then .node key left (insert x right)
      else tree

/-- The number of keys strictly smaller than `x`, computed from inorder traversal. -/
public def rank {α : Type u} [LinearOrder α] (x : α) (tree : BinaryTree α) : Nat :=
  ((inorder tree).filter (· < x)).length

/-- The key at the zero-based inorder position, if that position exists. -/
public def select {α : Type u} (tree : BinaryTree α) (index : Nat) : Option α :=
  (inorder tree)[index]?

/-- Build a tree by inserting the list from right to left. -/
public def fromList {α : Type u} [LinearOrder α] : List α → BinaryTree α
  | [] => .nil
  | x :: xs => insert x (fromList xs)

/-- `All` is equivalent to universal quantification over structural membership. -/
public theorem all_iff_forall_mem {α : Type u} {p : α → Prop}
    {tree : BinaryTree α} :
    All p tree ↔ ∀ x, x ∈ tree → p x := by
  induction tree with
  | nil => simp [All]
  | node key left right ihLeft ihRight =>
    simp only [All, mem_node, ihLeft, ihRight]
    constructor
    · rintro ⟨hLeft, hKey, hRight⟩ x (hx | hx | hx)
      · exact hLeft x hx
      · simpa [hx] using hKey
      · exact hRight x hx
    · intro h
      exact ⟨fun x hx => h x (Or.inl hx), h key (Or.inr (Or.inl rfl)),
        fun x hx => h x (Or.inr (Or.inr hx))⟩

/-- Inorder traversal contains exactly the structurally present keys. -/
public theorem mem_inorder {α : Type u} {x : α} {tree : BinaryTree α} :
    x ∈ inorder tree ↔ x ∈ tree := by
  induction tree with
  | nil => simp
  | node key left right ihLeft ihRight =>
    simp [ihLeft, ihRight, or_left_comm]

private theorem all_insert {α : Type u} [LinearOrder α] {p : α → Prop} {x : α}
    {tree : BinaryTree α} (hx : p x) (hTree : All p tree) :
    All p (insert x tree) := by
  induction tree with
  | nil => simpa [insert, All] using hx
  | node key left right ihLeft ihRight =>
    simp only [insert]
    split_ifs <;> simp_all [All]

/-- Inserting a key adds exactly that key to structural membership. -/
public theorem mem_insert {α : Type u} [LinearOrder α] {x y : α}
    {tree : BinaryTree α} :
    y ∈ insert x tree ↔ y = x ∨ y ∈ tree := by
  induction tree with
  | nil => simp [insert]
  | node key left right ihLeft ihRight =>
    by_cases hxKey : x < key
    · simp [insert, hxKey, ihLeft, or_assoc, or_left_comm]
    · by_cases hKeyX : key < x
      · simp [insert, hxKey, hKeyX, ihRight, or_left_comm]
      · have hxEq : x = key := le_antisymm (le_of_not_gt hKeyX) (le_of_not_gt hxKey)
        subst x
        have hKeyKey : ¬key < key := lt_irrefl key
        rw [insert]
        simp only [hKeyKey, ite_false]
        constructor
        · exact Or.inr
        · rintro (rfl | hy)
          · exact Or.inr (Or.inl rfl)
          · exact hy

/-- Insertion preserves the strict search-tree invariant. -/
public theorem ordered_insert {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} (hTree : Ordered tree) : Ordered (insert x tree) := by
  induction tree with
  | nil => simp [insert, Ordered, All]
  | node key left right ihLeft ihRight =>
    simp only [insert]
    split_ifs with hxKey hKeyX
    · rcases hTree with ⟨hLeft, hRight, hAllLeft, hAllRight⟩
      exact ⟨ihLeft hLeft, hRight, all_insert hxKey hAllLeft, hAllRight⟩
    · rcases hTree with ⟨hLeft, hRight, hAllLeft, hAllRight⟩
      exact ⟨hLeft, ihRight hRight, hAllLeft, all_insert hKeyX hAllRight⟩
    · exact hTree

/-- Search is equivalent to structural membership for an ordered tree. -/
public theorem contains_eq_true_iff {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} (hTree : Ordered tree) :
    contains x tree = true ↔ x ∈ tree := by
  induction tree with
  | nil => simp [contains]
  | node key left right ihLeft ihRight =>
    rcases hTree with ⟨hLeft, hRight, hAllLeft, hAllRight⟩
    by_cases hxKey : x < key
    · have hxNotRight : ¬x ∈ right := by
        intro hxRight
        have hKeyX := (all_iff_forall_mem.mp hAllRight) x hxRight
        exact lt_asymm hxKey hKeyX
      simp [contains, hxKey, ihLeft hLeft, hxNotRight, ne_of_lt hxKey]
    · by_cases hKeyX : key < x
      · have hxNotLeft : ¬x ∈ left := by
          intro hxLeft
          have hxKey' := (all_iff_forall_mem.mp hAllLeft) x hxLeft
          exact lt_asymm hKeyX hxKey'
        simp [contains, hxKey, hKeyX, ihRight hRight, hxNotLeft, ne_of_gt hKeyX]
      · have hxEq : x = key := le_antisymm (le_of_not_gt hKeyX) (le_of_not_gt hxKey)
        subst x
        have hKeyKey : ¬key < key := lt_irrefl key
        simp [contains, hKeyKey]

/-- The inorder traversal of an ordered tree is strictly increasing. -/
public theorem ordered_inorder {α : Type u} [LinearOrder α]
    {tree : BinaryTree α} (hTree : Ordered tree) :
    List.Pairwise (· < ·) (inorder tree) := by
  induction tree with
  | nil => simp
  | node key left right ihLeft ihRight =>
    rcases hTree with ⟨hLeft, hRight, hAllLeft, hAllRight⟩
    rw [inorder_node, List.pairwise_append]
    refine ⟨ihLeft hLeft, ?_, ?_⟩
    · rw [List.pairwise_cons]
      exact ⟨fun x hx => (all_iff_forall_mem.mp hAllRight) x (mem_inorder.mp hx),
        ihRight hRight⟩
    · intro x hx y hy
      rw [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact (all_iff_forall_mem.mp hAllLeft) x (mem_inorder.mp hx)
      · exact lt_trans ((all_iff_forall_mem.mp hAllLeft) x (mem_inorder.mp hx))
          ((all_iff_forall_mem.mp hAllRight) y (mem_inorder.mp hy))

/-- The inorder traversal of an ordered tree has no duplicate keys. -/
public theorem inorder_nodup {α : Type u} [LinearOrder α]
    {tree : BinaryTree α} (hTree : Ordered tree) : (inorder tree).Nodup :=
  (ordered_inorder hTree).nodup

/-- Building a tree by insertion always produces an ordered tree. -/
public theorem ordered_fromList {α : Type u} [LinearOrder α] {xs : List α} :
    Ordered (fromList xs) := by
  induction xs with
  | nil => simp [fromList, Ordered]
  | cons x xs ih => exact ordered_insert ih

/-- A key is in a tree built from a list exactly when it is in the list. -/
public theorem mem_fromList {α : Type u} [LinearOrder α] {x : α} {xs : List α} :
    x ∈ fromList xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [fromList]
  | cons y ys ih => simp [fromList, mem_insert, ih]

/-- Canonical node count agrees with the length of inorder traversal. -/
public theorem numNodes_eq_length_inorder {α : Type u} {tree : BinaryTree α} :
    tree.numNodes = (inorder tree).length := by
  induction tree with
  | nil => simp
  | node key left right ihLeft ihRight =>
    simp [ihLeft, ihRight, Nat.add_comm, Nat.add_left_comm]

/-- Inserting a present key preserves the canonical node count. -/
public theorem numNodes_insert_of_mem {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} (hTree : Ordered tree) (hx : x ∈ tree) :
    (insert x tree).numNodes = tree.numNodes := by
  induction tree with
  | nil => simp at hx
  | node key left right ihLeft ihRight =>
    rcases hTree with ⟨hLeft, hRight, hAllLeft, hAllRight⟩
    by_cases hxKey : x < key
    · have hxLeft : x ∈ left := by
        rcases hx with hxLeft | hxEq | hxRight
        · exact hxLeft
        · exact (ne_of_lt hxKey hxEq).elim
        · have hKeyX := (all_iff_forall_mem.mp hAllRight) x hxRight
          exact (lt_asymm hxKey hKeyX).elim
      simp [insert, hxKey, ihLeft hLeft hxLeft]
    · by_cases hKeyX : key < x
      · have hxRight : x ∈ right := by
          rcases hx with hxLeft | hxEq | hxRight
          · have hxKey' := (all_iff_forall_mem.mp hAllLeft) x hxLeft
            exact (lt_asymm hKeyX hxKey').elim
          · exact (ne_of_gt hKeyX hxEq).elim
          · exact hxRight
        simp [insert, hxKey, hKeyX, ihRight hRight hxRight]
      · simp [insert, hxKey, hKeyX]

/-- Inserting an absent key increases the canonical node count by one. -/
public theorem numNodes_insert_of_not_mem {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} (hx : ¬x ∈ tree) :
    (insert x tree).numNodes = tree.numNodes + 1 := by
  induction tree with
  | nil => simp [insert]
  | node key left right ihLeft ihRight =>
    by_cases hxKey : x < key
    · have hxLeft : ¬x ∈ left := fun h => hx (Or.inl h)
      simp [insert, hxKey, ihLeft hxLeft, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
    · by_cases hKeyX : key < x
      · have hxRight : ¬x ∈ right := fun h => hx (Or.inr (Or.inr h))
        simp [insert, hxKey, hKeyX, ihRight hxRight, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]
      · have hxEq : x = key := le_antisymm (le_of_not_gt hKeyX) (le_of_not_gt hxKey)
        exact (hx (Or.inr (Or.inl hxEq))).elim

/-- `rank` counts the inorder keys that are strictly below the query. -/
public theorem rank_eq_count_inorder {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} :
    rank x tree = ((inorder tree).filter (· < x)).length :=
  rfl

/-- `select` agrees with optional list indexing of inorder traversal. -/
public theorem select_eq_getElem?_inorder {α : Type u} {tree : BinaryTree α}
    {index : Nat} :
    select tree index = (inorder tree)[index]? :=
  rfl

private theorem filter_lt_eq_nil_of_forall_gt {α : Type u} [LinearOrder α] {a : α}
    {xs : List α} (h : ∀ x ∈ xs, a < x) : xs.filter (· < a) = [] := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    have hab : a < b := h b (by simp)
    have hbs : ∀ x ∈ bs, a < x := by
      intro x hx
      exact h x (by simp [hx])
    simp [not_lt_of_ge (le_of_lt hab), ih hbs]

private theorem selectList_rank {α : Type u} [LinearOrder α] {xs : List α}
    (hxs : List.Pairwise (· < ·) xs) {x : α} (hx : x ∈ xs) :
    xs[((xs.filter (· < x)).length)]? = some x := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
    rw [List.pairwise_cons] at hxs
    rcases hxs with ⟨ha, has⟩
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · have hnone := filter_lt_eq_nil_of_forall_gt ha
      simp [hnone]
    · have hax : a < x := ha x hx
      simp [hax, ih has hx]

private theorem rankList_select {α : Type u} [LinearOrder α] {xs : List α}
    (hxs : List.Pairwise (· < ·) xs) {index : Nat} {x : α}
    (hselect : xs[index]? = some x) : (xs.filter (· < x)).length = index := by
  induction xs generalizing index with
  | nil => simp at hselect
  | cons a as ih =>
    rw [List.pairwise_cons] at hxs
    rcases hxs with ⟨ha, has⟩
    cases index with
    | zero =>
      simp at hselect
      subst x
      have hnone := filter_lt_eq_nil_of_forall_gt ha
      simp [hnone]
    | succ index =>
      simp only [List.getElem?_cons_succ] at hselect
      have hx : x ∈ as := List.mem_of_getElem? hselect
      have hax : a < x := ha x hx
      simp [hax, ih has hselect]

/-- Selecting the rank of a present key returns that key. -/
public theorem select_rank {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} (hTree : Ordered tree) (hx : x ∈ tree) :
    select tree (rank x tree) = some x := by
  exact selectList_rank (ordered_inorder hTree) (mem_inorder.mpr hx)

/-- A successfully selected key has rank equal to its selected index. -/
public theorem rank_select {α : Type u} [LinearOrder α] {tree : BinaryTree α}
    {index : Nat} {x : α} (hTree : Ordered tree)
    (hSelect : select tree index = some x) : rank x tree = index := by
  exact rankList_select (ordered_inorder hTree) hSelect

end BinarySearchTree
end Cslib.Algorithms.Lean
