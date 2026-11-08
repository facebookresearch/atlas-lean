/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree

/-!
# Binary search tree deletion

Deletion for the pure, unbalanced binary search trees of
`CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree`. When the deleted
key sits at a node, its two subtrees are spliced together with `join`, so a
leaf or one-child node is replaced by its remaining subtree and a two-child
node by the concatenation of both. Membership of every other key is preserved
for arbitrary trees; that the deleted key itself disappears, that `Ordered`
is preserved, and the traversal specification `inorder_delete` assume the
strict invariant `Ordered`, matching `contains_eq_true_iff` in the parent
module.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace BinarySearchTree

/--
Splice two trees end to end, keeping every key of the first tree before every
key of the second in the inorder traversal. `ordered_join` gives the side
condition under which the splice of two ordered trees stays ordered.
-/
public def join {α : Type u} : BinaryTree α → BinaryTree α → BinaryTree α
  | .nil, right => right
  | .node key leftLeft leftRight, right =>
      .node key leftLeft (join leftRight right)

/-- Delete a key, splicing the subtrees of a deleted node together with `join`. -/
public def delete {α : Type u} [LinearOrder α] (x : α) :
    BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node key left right =>
      if x < key then .node key (delete x left) right
      else if key < x then .node key left (delete x right)
      else join left right

@[simp] private theorem mem_nil {α : Type u} {x : α} :
    x ∈ (BinaryTree.nil : BinaryTree α) ↔ False :=
  Iff.rfl

@[simp] private theorem mem_node {α : Type u} {x key : α}
    {left right : BinaryTree α} :
    x ∈ BinaryTree.node key left right ↔ x ∈ left ∨ x = key ∨ x ∈ right :=
  Iff.rfl

/-- A key is in a splice exactly when it is in one of the two parts. -/
public theorem mem_join {α : Type u} {x : α} {left right : BinaryTree α} :
    x ∈ join left right ↔ x ∈ left ∨ x ∈ right := by
  induction left with
  | nil => simp [join]
  | node key leftLeft leftRight _ ihRight =>
    simp only [join, mem_node, ihRight]
    constructor
    · rintro (hx | hx | hx | hx)
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr (Or.inl hx))
      · exact Or.inl (Or.inr (Or.inr hx))
      · exact Or.inr hx
    · rintro ((hx | hx | hx) | hx)
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr hx))

/-- The inorder traversal of a splice appends the two traversals. -/
public theorem inorder_join {α : Type u} {left right : BinaryTree α} :
    inorder (join left right) = inorder left ++ inorder right := by
  induction left with
  | nil => simp [join]
  | node key leftLeft leftRight _ ihRight =>
    simp only [join, inorder_node, ihRight]
    rw [List.append_assoc, List.cons_append]

private theorem all_join {α : Type u} {p : α → Prop} {left right : BinaryTree α}
    (hLeft : All p left) (hRight : All p right) : All p (join left right) := by
  refine all_iff_forall_mem.mpr (fun x hx => ?_)
  rw [mem_join] at hx
  rcases hx with hx | hx
  · exact (all_iff_forall_mem.mp hLeft) x hx
  · exact (all_iff_forall_mem.mp hRight) x hx

/--
Splicing two ordered trees stays ordered when every key of the left tree is
smaller than every key of the right tree.
-/
public theorem ordered_join {α : Type u} [LT α] {left right : BinaryTree α}
    (hLeft : Ordered left) (hRight : Ordered right)
    (hSeparated : ∀ a ∈ left, ∀ b ∈ right, a < b) :
    Ordered (join left right) := by
  induction left with
  | nil => simpa [join] using hRight
  | node key leftLeft leftRight _ ihRight =>
    rcases hLeft with ⟨hLeftLeft, hLeftRight, hAllLeftLeft, hAllLeftRight⟩
    have hSeparatedRight : ∀ a ∈ leftRight, ∀ b ∈ right, a < b :=
      fun a ha b hb => hSeparated a (Or.inr (Or.inr ha)) b hb
    have hKeyRight : All (key < ·) right :=
      all_iff_forall_mem.mpr
        (fun b hb => hSeparated key (Or.inr (Or.inl rfl)) b hb)
    simp only [join]
    exact ⟨hLeftLeft, ihRight hLeftRight hSeparatedRight, hAllLeftLeft,
      all_join hAllLeftRight hKeyRight⟩

private theorem mem_of_mem_delete {α : Type u} [LinearOrder α] {x y : α}
    {tree : BinaryTree α} (hy : y ∈ delete x tree) : y ∈ tree := by
  induction tree with
  | nil => simp [delete] at hy
  | node key left right ihLeft ihRight =>
    by_cases hxKey : x < key
    · simp only [delete, ite_eq_left hxKey, mem_node] at hy
      rcases hy with hy | hy | hy
      · exact Or.inl (ihLeft hy)
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hy)
    · by_cases hKeyX : key < x
      · simp only [delete, ite_eq_right hxKey, ite_eq_left hKeyX, mem_node] at hy
        rcases hy with hy | hy | hy
        · exact Or.inl hy
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (ihRight hy))
      · simp only [delete, ite_eq_right hxKey, ite_eq_right hKeyX] at hy
        rw [mem_join] at hy
        rcases hy with hy | hy
        · exact Or.inl hy
        · exact Or.inr (Or.inr hy)

/-- Deletion keeps every key other than the deleted one, ordered or not. -/
public theorem mem_delete_of_mem {α : Type u} [LinearOrder α] {x y : α}
    {tree : BinaryTree α} (hy : y ∈ tree) (hxy : y ≠ x) :
    y ∈ delete x tree := by
  induction tree with
  | nil => exact (mem_nil.mp hy).elim
  | node key left right ihLeft ihRight =>
    rw [mem_node] at hy
    by_cases hxKey : x < key
    · simp only [delete, ite_eq_left hxKey, mem_node]
      rcases hy with hy | hy | hy
      · exact Or.inl (ihLeft hy)
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hy)
    · by_cases hKeyX : key < x
      · simp only [delete, ite_eq_right hxKey, ite_eq_left hKeyX, mem_node]
        rcases hy with hy | hy | hy
        · exact Or.inl hy
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (ihRight hy))
      · have hxEq : x = key :=
          le_antisymm (le_of_not_gt hKeyX) (le_of_not_gt hxKey)
        simp only [delete, ite_eq_right hxKey, ite_eq_right hKeyX, mem_join]
        rcases hy with hy | hy | hy
        · exact Or.inl hy
        · exact absurd (hy.trans hxEq.symm) hxy
        · exact Or.inr hy

/-- The deleted key is absent after deletion from an ordered tree. -/
public theorem not_mem_delete_self {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} (hTree : Ordered tree) : x ∉ delete x tree := by
  induction tree with
  | nil => simp [delete]
  | node key left right ihLeft ihRight =>
    rcases hTree with ⟨hLeft, hRight, hAllLeft, hAllRight⟩
    by_cases hxKey : x < key
    · simp only [delete, ite_eq_left hxKey, mem_node]
      rintro (hx | hx | hx)
      · exact ihLeft hLeft hx
      · exact ne_of_lt hxKey hx
      · exact lt_asymm hxKey ((all_iff_forall_mem.mp hAllRight) x hx)
    · by_cases hKeyX : key < x
      · simp only [delete, ite_eq_right hxKey, ite_eq_left hKeyX, mem_node]
        rintro (hx | hx | hx)
        · exact lt_asymm hKeyX ((all_iff_forall_mem.mp hAllLeft) x hx)
        · exact ne_of_gt hKeyX hx
        · exact ihRight hRight hx
      · have hxEq : x = key :=
          le_antisymm (le_of_not_gt hKeyX) (le_of_not_gt hxKey)
        simp only [delete, ite_eq_right hxKey, ite_eq_right hKeyX, mem_join]
        subst x
        rintro (hx | hx)
        · exact lt_irrefl key ((all_iff_forall_mem.mp hAllLeft) key hx)
        · exact lt_irrefl key ((all_iff_forall_mem.mp hAllRight) key hx)

/-- Deletion from an ordered tree removes exactly the deleted key. -/
public theorem mem_delete {α : Type u} [LinearOrder α] {x y : α}
    {tree : BinaryTree α} (hTree : Ordered tree) :
    y ∈ delete x tree ↔ y ∈ tree ∧ y ≠ x := by
  constructor
  · intro hy
    refine ⟨mem_of_mem_delete hy, ?_⟩
    rintro rfl
    exact not_mem_delete_self hTree hy
  · rintro ⟨hy, hxy⟩
    exact mem_delete_of_mem hy hxy

private theorem all_delete {α : Type u} [LinearOrder α] {p : α → Prop} {x : α}
    {tree : BinaryTree α} (hTree : All p tree) : All p (delete x tree) :=
  all_iff_forall_mem.mpr
    (fun y hy => (all_iff_forall_mem.mp hTree) y (mem_of_mem_delete hy))

/-- Deletion preserves the strict search-tree invariant. -/
public theorem ordered_delete {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} (hTree : Ordered tree) :
    Ordered (delete x tree) := by
  induction tree with
  | nil => simp [delete, Ordered]
  | node key left right ihLeft ihRight =>
    rcases hTree with ⟨hLeft, hRight, hAllLeft, hAllRight⟩
    by_cases hxKey : x < key
    · simp only [delete, ite_eq_left hxKey]
      exact ⟨ihLeft hLeft, hRight, all_delete hAllLeft, hAllRight⟩
    · by_cases hKeyX : key < x
      · simp only [delete, ite_eq_right hxKey, ite_eq_left hKeyX]
        exact ⟨hLeft, ihRight hRight, hAllLeft, all_delete hAllRight⟩
      · simp only [delete, ite_eq_right hxKey, ite_eq_right hKeyX]
        exact ordered_join hLeft hRight (fun a ha b hb =>
          lt_trans ((all_iff_forall_mem.mp hAllLeft) a ha)
            ((all_iff_forall_mem.mp hAllRight) b hb))

private theorem erase_cons_tail_of_ne {α : Type u} [LinearOrder α] {a b : α}
    {l : List α} (h : b ≠ a) : (b :: l).erase a = b :: l.erase a :=
  List.erase_cons_tail (fun hb => h (beq_iff_eq.mp hb))

private theorem erase_append_of_not_mem_left {α : Type u} [LinearOrder α]
    {x : α} {left right : List α} (hx : x ∉ left) :
    (left ++ right).erase x = left ++ right.erase x := by
  rw [List.erase_append, ite_eq_right hx]

private theorem erase_append_of_not_mem_right {α : Type u} [LinearOrder α]
    {x : α} {left right : List α} (hx : x ∉ right) :
    (left ++ right).erase x = left.erase x ++ right := by
  by_cases hxLeft : x ∈ left
  · rw [List.erase_append, ite_eq_left hxLeft]
  · rw [List.erase_append, ite_eq_right hxLeft, List.erase_of_not_mem hx,
      List.erase_of_not_mem hxLeft]

/-- Deleting a key erases it from the inorder traversal of an ordered tree. -/
public theorem inorder_delete {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} (hTree : Ordered tree) :
    inorder (delete x tree) = (inorder tree).erase x := by
  induction tree with
  | nil => simp [delete]
  | node key left right ihLeft ihRight =>
    rcases hTree with ⟨hLeft, hRight, hAllLeft, hAllRight⟩
    by_cases hxKey : x < key
    · have hxRight : x ∉ inorder right := by
        rw [mem_inorder]
        intro hx
        exact lt_asymm hxKey ((all_iff_forall_mem.mp hAllRight) x hx)
      have hxCons : x ∉ key :: inorder right := by
        intro hx
        rw [List.mem_cons] at hx
        rcases hx with hx | hx
        · exact ne_of_lt hxKey hx
        · exact hxRight hx
      simp only [delete, ite_eq_left hxKey, inorder_node, ihLeft hLeft]
      exact (erase_append_of_not_mem_right hxCons).symm
    · by_cases hKeyX : key < x
      · have hxLeft : x ∉ inorder left := by
          rw [mem_inorder]
          intro hx
          exact lt_asymm hKeyX ((all_iff_forall_mem.mp hAllLeft) x hx)
        simp only [delete, ite_eq_right hxKey, ite_eq_left hKeyX, inorder_node,
          ihRight hRight]
        rw [erase_append_of_not_mem_left hxLeft,
          erase_cons_tail_of_ne (ne_of_lt hKeyX)]
      · have hxEq : x = key :=
          le_antisymm (le_of_not_gt hKeyX) (le_of_not_gt hxKey)
        subst x
        have hKeyLeft : key ∉ inorder left := by
          rw [mem_inorder]
          intro hx
          exact lt_irrefl key ((all_iff_forall_mem.mp hAllLeft) key hx)
        simp only [delete, ite_eq_right hxKey, inorder_join, inorder_node]
        rw [erase_append_of_not_mem_left hKeyLeft, List.erase_cons_head]

end BinarySearchTree
end Cslib.Algorithms.Lean
