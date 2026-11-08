/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree
public import Mathlib.Data.List.Nodup
public import Mathlib.Order.Defs.LinearOrder

/-!
# Red-black trees

This module develops pure functional red-black trees with Okasaki's insertion.
The invariants are the usual ones, stated separately: `Ordered` is the strict
binary-search-tree invariant, inherited from `BinarySearchTree` through the
color-erasing projection `erase` (as in `OrderStatisticTree`), `RedOk` forbids a
red node with a red child, and `Balanced` states that every root-to-leaf path
contains the same number of black nodes, where the count along the left spine
is computed by `blackHeight`. A tree is `Valid` when it satisfies all three
invariants and has a black root. Membership, `All`, and inorder traversal are
likewise inherited through `erase`; only the color invariants, `blackHeight`,
and Okasaki's rebalancing insertion are red-black-specific.

Insertion follows Okasaki: an unchecked insertion `ins` may create a red-red
redex at the root (the relaxed invariant `AlmostRedOk`), `balance` repairs a
redex below a black node, and the public `insert` recolors the root black.
Insertion preserves `blackHeight` exactly before the final recoloring, which
can raise it by one.

Deletion is out of scope for this module and is a staged follow-up.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace RedBlackTree

/-- The color of a red-black tree node. -/
public inductive Color where
  | red
  | black
  deriving DecidableEq, Repr

/-- A red-black tree: each node carries a color, a key, and two subtrees. -/
public inductive Tree (α : Type u) where
  | empty
  | node (color : Color) (left : Tree α) (key : α) (right : Tree α)
deriving DecidableEq, Repr

/-- Remove colors, yielding the underlying binary search tree. -/
public def erase {α : Type u} : Tree α → BinaryTree α
  | .empty => .nil
  | .node _ left key right => .node key (erase left) (erase right)

@[simp] public theorem erase_empty {α : Type u} :
    erase (.empty : Tree α) = .nil :=
  rfl

@[simp] public theorem erase_node {α : Type u} {color : Color}
    {left right : Tree α} {key : α} :
    erase (.node color left key right) = .node key (erase left) (erase right) :=
  rfl

/-- Structural membership, inherited from `BinarySearchTree` through `erase`. -/
public def Mem {α : Type u} (x : α) (tree : Tree α) : Prop :=
  BinarySearchTree.Mem x (erase tree)

public instance {α : Type u} : Membership α (Tree α) :=
  ⟨fun tree x => Mem x tree⟩

@[simp] private theorem mem_empty {α : Type u} {x : α} :
    x ∈ (Tree.empty : Tree α) ↔ False :=
  Iff.rfl

@[simp] private theorem mem_node {α : Type u} {x key : α} {color : Color}
    {left right : Tree α} :
    x ∈ Tree.node color left key right ↔ x ∈ left ∨ x = key ∨ x ∈ right :=
  Iff.rfl

/-- Append the inorder traversal of a tree to an existing suffix in linear
time; inherited from `BinarySearchTree` through `erase`. -/
public def inorderAux {α : Type u} (tree : Tree α) (suffix : List α) : List α :=
  BinarySearchTree.inorderAux (erase tree) suffix

/-- The linear-time inorder traversal of a tree, inherited from
`BinarySearchTree` through `erase`. -/
public def inorder {α : Type u} (tree : Tree α) : List α :=
  BinarySearchTree.inorder (erase tree)

@[simp] public theorem inorder_empty {α : Type u} :
    inorder (.empty : Tree α) = [] :=
  rfl

@[simp] public theorem inorder_node {α : Type u} {color : Color} (key : α)
    (left right : Tree α) :
    inorder (.node color left key right) =
      inorder left ++ key :: inorder right :=
  BinarySearchTree.inorder_node key (erase left) (erase right)

/-- `All p tree` states that every key in `tree` satisfies `p`; it is
`BinarySearchTree.All` of the color-erased tree. -/
public def All {α : Type u} (p : α → Prop) (tree : Tree α) : Prop :=
  BinarySearchTree.All p (erase tree)

/-- Every left key is smaller and every right key is larger, recursively; it is
`BinarySearchTree.Ordered` of the color-erased tree. -/
public def Ordered {α : Type u} [LT α] (tree : Tree α) : Prop :=
  BinarySearchTree.Ordered (erase tree)

/-- Membership in a red-black tree is `BinarySearchTree` membership in its
color-erased tree, by definition. -/
public theorem mem_erase {α : Type u} {x : α} {tree : Tree α} :
    x ∈ tree ↔ x ∈ erase tree :=
  Iff.rfl

/-- `All` on a red-black tree is `BinarySearchTree.All` of its color-erased
tree, by definition. -/
public theorem all_erase {α : Type u} {p : α → Prop} {tree : Tree α} :
    All p tree ↔ BinarySearchTree.All p (erase tree) :=
  Iff.rfl

/-- Ordering of a red-black tree is `BinarySearchTree.Ordered` of its
color-erased tree, by definition. -/
public theorem ordered_erase {α : Type u} [LT α] {tree : Tree α} :
    Ordered tree ↔ BinarySearchTree.Ordered (erase tree) :=
  Iff.rfl

/-- The inorder traversal of a red-black tree is the `BinarySearchTree`
inorder traversal of its color-erased tree, by definition. -/
public theorem inorder_erase {α : Type u} (tree : Tree α) :
    inorder tree = BinarySearchTree.inorder (erase tree) :=
  rfl

/-- The color of the root of a tree; the empty tree counts as black. -/
public def colorOf {α : Type u} : Tree α → Color
  | .empty => .black
  | .node color _ _ _ => color

/-- The red invariant: no red node has a red child. -/
public def RedOk {α : Type u} : Tree α → Prop
  | .empty => True
  | .node .red left _ right =>
      RedOk left ∧ RedOk right ∧ colorOf left = .black ∧ colorOf right = .black
  | .node .black left _ right => RedOk left ∧ RedOk right

/-- `RedOk` everywhere except possibly a red-red redex at the root.

This is the intermediate invariant of Okasaki's unchecked insertion. -/
public def AlmostRedOk {α : Type u} : Tree α → Prop
  | .empty => True
  | .node _ left _ right => RedOk left ∧ RedOk right

/-- The number of black nodes on a root-to-leaf path, counting the leaf. -/
public def blackHeight {α : Type u} : Tree α → Nat
  | .empty => 1
  | .node .red left _ _ => blackHeight left
  | .node .black left _ _ => blackHeight left + 1

/-- All root-to-leaf paths contain the same number of black nodes. -/
public def Balanced {α : Type u} : Tree α → Prop
  | .empty => True
  | .node _ left _ right =>
      Balanced left ∧ Balanced right ∧ blackHeight left = blackHeight right

/-- A valid red-black tree: ordered, red-invariant, balanced, black root. -/
public def Valid {α : Type u} [LT α] (tree : Tree α) : Prop :=
  Ordered tree ∧ RedOk tree ∧ Balanced tree ∧ colorOf tree = .black

/-- Search a tree by following comparisons from its root. -/
public def contains {α : Type u} [LinearOrder α] (x : α) : Tree α → Bool
  | .empty => false
  | .node _ left key right =>
      if x < key then contains x left
      else if key < x then contains x right
      else true

/-- Okasaki's rebalancing: repair a red-red redex below a black node. -/
def balance {α : Type u} : Color → Tree α → α → Tree α → Tree α
  | .black, .node .red (.node .red a x b) y c, z, d =>
      .node .red (.node .black a x b) y (.node .black c z d)
  | .black, .node .red a x (.node .red b y c), z, d =>
      .node .red (.node .black a x b) y (.node .black c z d)
  | .black, a, x, .node .red (.node .red b y c) z d =>
      .node .red (.node .black a x b) y (.node .black c z d)
  | .black, a, x, .node .red b y (.node .red c z d) =>
      .node .red (.node .black a x b) y (.node .black c z d)
  | color, left, key, right => .node color left key right

/-- Unchecked insertion; the result may violate `RedOk` at the root. -/
def ins {α : Type u} [LinearOrder α] (x : α) : Tree α → Tree α
  | .empty => .node .red .empty x .empty
  | tree@(.node color left key right) =>
      if x < key then balance color (ins x left) key right
      else if key < x then balance color left key (ins x right)
      else tree

/-- Recolor the root of a tree black. -/
def makeBlack {α : Type u} : Tree α → Tree α
  | .empty => .empty
  | .node _ left key right => .node .black left key right

/-- Recoloring the root black is invisible after erasing colors. -/
public theorem erase_makeBlack {α : Type u} {tree : Tree α} :
    erase (makeBlack tree) = erase tree := by
  cases tree <;> rfl

/-- Insert a key, leaving an existing equal key unchanged. -/
public def insert {α : Type u} [LinearOrder α] (x : α) (tree : Tree α) :
    Tree α :=
  makeBlack (ins x tree)

/-- Build a tree by inserting the list from right to left. -/
public def fromList {α : Type u} [LinearOrder α] : List α → Tree α
  | [] => .empty
  | x :: xs => insert x (fromList xs)

/-- `All` is equivalent to universal quantification over structural
membership; inherited from `BinarySearchTree`. -/
public theorem all_iff_forall_mem {α : Type u} {p : α → Prop} {tree : Tree α} :
    All p tree ↔ ∀ x, x ∈ tree → p x :=
  BinarySearchTree.all_iff_forall_mem

/-- Inorder traversal contains exactly the structurally present keys;
inherited from `BinarySearchTree`. -/
public theorem mem_inorder {α : Type u} {x : α} {tree : Tree α} :
    x ∈ inorder tree ↔ x ∈ tree :=
  BinarySearchTree.mem_inorder

/-- The inorder traversal of an ordered tree is strictly increasing;
inherited from `BinarySearchTree`. -/
public theorem ordered_inorder {α : Type u} [LinearOrder α] {tree : Tree α}
    (h : Ordered tree) : List.Pairwise (· < ·) (inorder tree) :=
  BinarySearchTree.ordered_inorder h

private theorem ordered_of_pairwise_inorder {α : Type u} [LinearOrder α]
    {tree : Tree α} (h : List.Pairwise (· < ·) (inorder tree)) : Ordered tree := by
  induction tree with
  | empty => trivial
  | node color left key right ihLeft ihRight =>
    rw [inorder_node, List.pairwise_append] at h
    rcases h with ⟨hLeft, hCons, hCross⟩
    rw [List.pairwise_cons] at hCons
    refine ⟨ihLeft hLeft, ihRight hCons.2, ?_, ?_⟩
    · exact all_iff_forall_mem.mpr fun y hy =>
        hCross y (mem_inorder.mpr hy) key (by simp)
    · exact all_iff_forall_mem.mpr fun y hy => hCons.1 y (mem_inorder.mpr hy)

private theorem balance_red {α : Type u} {left right : Tree α} {key : α} :
    balance .red left key right = .node .red left key right :=
  rfl

private theorem inorder_balance {α : Type u} (color : Color) (left : Tree α)
    (key : α) (right : Tree α) :
    inorder (balance color left key right) =
      inorder (Tree.node color left key right) := by
  cases color with
  | red => simp [balance_red]
  | black =>
    cases left with
    | empty =>
      cases right with
      | empty => simp [balance]
      | node cr a yy b =>
        cases cr <;> cases a <;> cases b <;>
          (try cases ‹Color›) <;> (try cases ‹Color›) <;>
          simp [balance, List.append_assoc]
    | node cl a yy b =>
      cases cl with
      | black =>
        cases right with
        | empty => simp [balance]
        | node cr e z f =>
          cases cr <;> cases e <;> cases f <;>
            (try cases ‹Color›) <;> (try cases ‹Color›) <;>
            simp [balance, List.append_assoc]
      | red =>
        cases a <;> cases b <;>
          (try cases ‹Color›) <;> (try cases ‹Color›) <;>
          cases right with
          | empty => simp [balance, List.append_assoc]
          | node cr e z f =>
            cases cr <;> cases e <;> cases f <;>
              (try cases ‹Color›) <;> (try cases ‹Color›) <;>
              simp [balance, List.append_assoc]

private theorem mem_balance {α : Type u} {y : α} (color : Color) (left : Tree α)
    (key : α) (right : Tree α) :
    y ∈ balance color left key right ↔ y ∈ Tree.node color left key right := by
  rw [← mem_inorder, ← mem_inorder, inorder_balance]

private theorem all_balance {α : Type u} {p : α → Prop} {color : Color}
    {left right : Tree α} {key : α} :
    All p (balance color left key right) ↔
      All p (Tree.node color left key right) := by
  simp only [all_iff_forall_mem, mem_balance]

private theorem blackHeight_balance {α : Type u} (color : Color) (left : Tree α)
    (key : α) (right : Tree α) :
    blackHeight (balance color left key right) =
      blackHeight (Tree.node color left key right) := by
  cases color with
  | red => simp [balance_red]
  | black =>
    cases left with
    | empty =>
      cases right with
      | empty => simp [balance]
      | node cr a yy b =>
        cases cr <;> cases a <;> cases b <;>
          (try cases ‹Color›) <;> (try cases ‹Color›) <;>
          simp [balance, blackHeight]
    | node cl a yy b =>
      cases cl with
      | black =>
        cases right with
        | empty => simp [balance]
        | node cr e z f =>
          cases cr <;> cases e <;> cases f <;>
            (try cases ‹Color›) <;> (try cases ‹Color›) <;>
            simp [balance, blackHeight]
      | red =>
        cases a <;> cases b <;>
          (try cases ‹Color›) <;> (try cases ‹Color›) <;>
          cases right with
          | empty => simp [balance, blackHeight]
          | node cr e z f =>
            cases cr <;> cases e <;> cases f <;>
              (try cases ‹Color›) <;> (try cases ‹Color›) <;>
              simp [balance, blackHeight]

private theorem balanced_balance {α : Type u} {color : Color} {left right : Tree α}
    {key : α} (hLeft : Balanced left) (hRight : Balanced right)
    (hEq : blackHeight left = blackHeight right) :
    Balanced (balance color left key right) := by
  cases color with
  | red =>
    rw [balance_red]
    exact ⟨hLeft, hRight, hEq⟩
  | black =>
    cases left with
    | empty =>
      cases right with
      | empty => simp [balance, Balanced]
      | node cr a yy b =>
        cases cr <;> cases a <;> cases b <;>
          (try cases ‹Color›) <;> (try cases ‹Color›) <;>
          simp_all [balance, Balanced, blackHeight] <;> omega
    | node cl a yy b =>
      cases cl with
      | black =>
        cases right with
        | empty => simp_all [balance, Balanced, blackHeight]
        | node cr e z f =>
          cases cr <;> cases e <;> cases f <;>
            (try cases ‹Color›) <;> (try cases ‹Color›) <;>
            simp_all [balance, Balanced, blackHeight] <;> omega
      | red =>
        cases a <;> cases b <;>
          (try cases ‹Color›) <;> (try cases ‹Color›) <;>
          cases right with
          | empty => simp_all [balance, Balanced, blackHeight] <;> omega
          | node cr e z f =>
            cases cr <;> cases e <;> cases f <;>
              (try cases ‹Color›) <;> (try cases ‹Color›) <;>
              simp_all [balance, Balanced, blackHeight] <;> omega

private theorem redOk_balance_black_left {α : Type u} {left right : Tree α} {key : α}
    (hLeft : AlmostRedOk left) (hRight : RedOk right) :
    RedOk (balance .black left key right) := by
  cases left with
  | empty =>
    cases right with
    | empty => simp [balance, RedOk]
    | node cr a yy b =>
      cases cr <;> cases a <;> cases b <;>
        (try cases ‹Color›) <;> (try cases ‹Color›) <;>
        simp_all [balance, RedOk, AlmostRedOk, colorOf]
  | node cl a yy b =>
    cases cl with
    | black =>
      cases right with
      | empty => simp_all [balance, RedOk, AlmostRedOk]
      | node cr e z f =>
        cases cr <;> cases e <;> cases f <;>
          (try cases ‹Color›) <;> (try cases ‹Color›) <;>
          simp_all [balance, RedOk, AlmostRedOk, colorOf]
    | red =>
      cases a <;> cases b <;>
        (try cases ‹Color›) <;> (try cases ‹Color›) <;>
        cases right with
        | empty => simp_all [balance, RedOk, AlmostRedOk, colorOf]
        | node cr e z f =>
          cases cr <;> cases e <;> cases f <;>
            (try cases ‹Color›) <;> (try cases ‹Color›) <;>
            simp_all [balance, RedOk, AlmostRedOk, colorOf]

private theorem redOk_balance_black_right {α : Type u} {left right : Tree α} {key : α}
    (hLeft : RedOk left) (hRight : AlmostRedOk right) :
    RedOk (balance .black left key right) := by
  cases left with
  | empty =>
    cases right with
    | empty => simp [balance, RedOk]
    | node cr a yy b =>
      cases cr <;> cases a <;> cases b <;>
        (try cases ‹Color›) <;> (try cases ‹Color›) <;>
        simp_all [balance, RedOk, AlmostRedOk, colorOf]
  | node cl a yy b =>
    cases cl with
    | black =>
      cases right with
      | empty => simp_all [balance, RedOk, AlmostRedOk]
      | node cr e z f =>
        cases cr <;> cases e <;> cases f <;>
          (try cases ‹Color›) <;> (try cases ‹Color›) <;>
          simp_all [balance, RedOk, AlmostRedOk, colorOf]
    | red =>
      cases a <;> cases b <;>
        (try cases ‹Color›) <;> (try cases ‹Color›) <;>
        cases right with
        | empty => simp_all [balance, RedOk, AlmostRedOk, colorOf]
        | node cr e z f =>
          cases cr <;> cases e <;> cases f <;>
            (try cases ‹Color›) <;> (try cases ‹Color›) <;>
            simp_all [balance, RedOk, AlmostRedOk, colorOf]

private theorem all_mono {α : Type u} {p q : α → Prop} (h : ∀ y, p y → q y)
    {tree : Tree α} (hAll : All p tree) : All q tree :=
  all_iff_forall_mem.mpr fun y hy => h y (all_iff_forall_mem.mp hAll y hy)

private theorem ordered_balance {α : Type u} [LinearOrder α] {color : Color}
    {left right : Tree α} {key : α} (hLeft : Ordered left)
    (hRight : Ordered right) (hAllLeft : All (· < key) left)
    (hAllRight : All (key < ·) right) :
    Ordered (balance color left key right) := by
  apply ordered_of_pairwise_inorder
  rw [inorder_balance, inorder_node, List.pairwise_append]
  refine ⟨ordered_inorder hLeft, ?_, ?_⟩
  · rw [List.pairwise_cons]
    exact ⟨fun y hy => (all_iff_forall_mem.mp hAllRight) y (mem_inorder.mp hy),
      ordered_inorder hRight⟩
  · intro a ha b hb
    rw [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact (all_iff_forall_mem.mp hAllLeft) a (mem_inorder.mp ha)
    · exact lt_trans ((all_iff_forall_mem.mp hAllLeft) a (mem_inorder.mp ha))
        ((all_iff_forall_mem.mp hAllRight) b (mem_inorder.mp hb))

private theorem all_ins {α : Type u} [LinearOrder α] {p : α → Prop} {x : α}
    {tree : Tree α} (hx : p x) (h : All p tree) : All p (ins x tree) := by
  induction tree with
  | empty =>
      simpa [ins, All, BinarySearchTree.All, erase] using hx
  | node color left key right ihLeft ihRight =>
    rcases h with ⟨hLeft, hKey, hRight⟩
    simp only [ins]
    split_ifs
    · exact all_balance.mpr ⟨ihLeft hLeft, hKey, hRight⟩
    · exact all_balance.mpr ⟨hLeft, hKey, ihRight hRight⟩
    · exact ⟨hLeft, hKey, hRight⟩

private theorem mem_ins {α : Type u} [LinearOrder α] {x y : α} {tree : Tree α} :
    y ∈ ins x tree ↔ y = x ∨ y ∈ tree := by
  induction tree with
  | empty => simp [ins]
  | node color left key right ihLeft ihRight =>
    by_cases hxKey : x < key
    · simp [ins, hxKey, mem_balance, ihLeft]
      tauto
    · by_cases hKeyX : key < x
      · simp [ins, hxKey, hKeyX, mem_balance, ihRight]
        tauto
      · have hxEq : x = key := le_antisymm (le_of_not_gt hKeyX) (le_of_not_gt hxKey)
        subst x
        have hKeyKey : ¬key < key := lt_irrefl key
        have hIns : ins key (Tree.node color left key right) =
            Tree.node color left key right := by
          simp [ins, hKeyKey]
        rw [hIns]
        simp only [mem_node]
        tauto

private theorem ordered_ins {α : Type u} [LinearOrder α] {x : α} {tree : Tree α}
    (h : Ordered tree) : Ordered (ins x tree) := by
  induction tree with
  | empty =>
      simp [ins, Ordered, BinarySearchTree.Ordered, BinarySearchTree.All,
        erase]
  | node color left key right ihLeft ihRight =>
    rcases h with ⟨hLeft, hRight, hAllLeft, hAllRight⟩
    simp only [ins]
    split_ifs with hxKey hKeyX
    · exact ordered_balance (ihLeft hLeft) hRight (all_ins hxKey hAllLeft)
        hAllRight
    · exact ordered_balance hLeft (ihRight hRight) hAllLeft
        (all_ins hKeyX hAllRight)
    · exact ⟨hLeft, hRight, hAllLeft, hAllRight⟩

private theorem blackHeight_ins {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} : blackHeight (ins x tree) = blackHeight tree := by
  induction tree with
  | empty => rfl
  | node color left key right ihLeft ihRight =>
    cases color <;> simp only [ins] <;> split_ifs <;>
      simp [blackHeight_balance, blackHeight, ihLeft]

private theorem balanced_ins {α : Type u} [LinearOrder α] {x : α} {tree : Tree α}
    (h : Balanced tree) : Balanced (ins x tree) := by
  induction tree with
  | empty => simp [ins, Balanced]
  | node color left key right ihLeft ihRight =>
    rcases h with ⟨hLeft, hRight, hEq⟩
    simp only [ins]
    split_ifs
    · refine balanced_balance (ihLeft hLeft) hRight ?_
      rwa [blackHeight_ins]
    · refine balanced_balance hLeft (ihRight hRight) ?_
      rwa [blackHeight_ins]
    · exact ⟨hLeft, hRight, hEq⟩

private theorem RedOk.almost {α : Type u} {tree : Tree α} (h : RedOk tree) :
    AlmostRedOk tree := by
  cases tree with
  | empty => trivial
  | node color left key right =>
    cases color with
    | red => exact ⟨h.1, h.2.1⟩
    | black => exact h

private theorem almostRedOk_ins {α : Type u} [LinearOrder α] {x : α} {tree : Tree α}
    (h : RedOk tree) :
    AlmostRedOk (ins x tree) ∧ (colorOf tree = .black → RedOk (ins x tree)) := by
  induction tree with
  | empty => exact ⟨⟨trivial, trivial⟩, fun _ => ⟨trivial, trivial, rfl, rfl⟩⟩
  | node color left key right ihLeft ihRight =>
    cases color with
    | red =>
      rcases h with ⟨hLeft, hRight, hcLeft, hcRight⟩
      simp only [ins]
      split_ifs
      · exact ⟨⟨(ihLeft hLeft).2 hcLeft, hRight⟩, by simp [colorOf]⟩
      · exact ⟨⟨hLeft, (ihRight hRight).2 hcRight⟩, by simp [colorOf]⟩
      · exact ⟨⟨hLeft, hRight⟩, by simp [colorOf]⟩
    | black =>
      rcases h with ⟨hLeft, hRight⟩
      simp only [ins]
      split_ifs
      · have hb : RedOk (balance .black (ins x left) key right) :=
          redOk_balance_black_left (ihLeft hLeft).1 hRight
        exact ⟨hb.almost, fun _ => hb⟩
      · have hb : RedOk (balance .black left key (ins x right)) :=
          redOk_balance_black_right hLeft (ihRight hRight).1
        exact ⟨hb.almost, fun _ => hb⟩
      · exact ⟨⟨hLeft, hRight⟩, fun _ => ⟨hLeft, hRight⟩⟩

private theorem mem_makeBlack {α : Type u} {y : α} {tree : Tree α} :
    y ∈ makeBlack tree ↔ y ∈ tree := by
  cases tree <;> simp [makeBlack]

private theorem ordered_makeBlack {α : Type u} [LT α] {tree : Tree α}
    (h : Ordered tree) : Ordered (makeBlack tree) := by
  cases tree <;> exact h

private theorem balanced_makeBlack {α : Type u} {tree : Tree α} (h : Balanced tree) :
    Balanced (makeBlack tree) := by
  cases tree <;> exact h

private theorem redOk_makeBlack {α : Type u} {tree : Tree α} (h : AlmostRedOk tree) :
    RedOk (makeBlack tree) := by
  cases tree <;> exact h

private theorem colorOf_makeBlack {α : Type u} {tree : Tree α} :
    colorOf (makeBlack tree) = .black := by
  cases tree <;> rfl

private theorem blackHeight_makeBlack {α : Type u} {tree : Tree α} :
    blackHeight (makeBlack tree) = blackHeight tree ∨
      blackHeight (makeBlack tree) = blackHeight tree + 1 := by
  cases tree with
  | empty => exact Or.inl rfl
  | node color left key right =>
    cases color <;> simp [makeBlack, blackHeight]

/-- Inserting a key adds exactly that key to structural membership. -/
public theorem mem_insert {α : Type u} [LinearOrder α] {x y : α} {tree : Tree α} :
    y ∈ insert x tree ↔ y = x ∨ y ∈ tree := by
  simp only [insert, mem_makeBlack, mem_ins]

/-- Insertion preserves the strict search-tree invariant. -/
public theorem ordered_insert {α : Type u} [LinearOrder α] {x : α} {tree : Tree α}
    (h : Ordered tree) : Ordered (insert x tree) :=
  ordered_makeBlack (ordered_ins h)

/-- Insertion preserves the red invariant. -/
public theorem redOk_insert {α : Type u} [LinearOrder α] {x : α} {tree : Tree α}
    (h : RedOk tree) : RedOk (insert x tree) :=
  redOk_makeBlack (almostRedOk_ins h).1

/-- Insertion preserves black-height balance. -/
public theorem balanced_insert {α : Type u} [LinearOrder α] {x : α} {tree : Tree α}
    (h : Balanced tree) : Balanced (insert x tree) :=
  balanced_makeBlack (balanced_ins h)

/-- Insertion preserves `blackHeight` up to the final root recoloring. -/
public theorem blackHeight_insert {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} :
    blackHeight (insert x tree) = blackHeight tree ∨
      blackHeight (insert x tree) = blackHeight tree + 1 := by
  show blackHeight (makeBlack (ins x tree)) = blackHeight tree ∨
    blackHeight (makeBlack (ins x tree)) = blackHeight tree + 1
  rcases blackHeight_makeBlack (tree := ins x tree) with h | h
  · exact Or.inl (h.trans blackHeight_ins)
  · exact Or.inr (by rw [h, blackHeight_ins])

/-- Insertion yields a valid tree from the three structural invariants
`Ordered`, `RedOk`, and `Balanced`; the input root need not be black,
since `insert` recolors the root black. -/
public theorem valid_insert_of_invariants {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hOrdered : Ordered tree) (hRedOk : RedOk tree)
    (hBalanced : Balanced tree) : Valid (insert x tree) :=
  ⟨ordered_insert hOrdered, redOk_insert hRedOk, balanced_insert hBalanced,
    colorOf_makeBlack⟩

/-- Insertion preserves validity of a red-black tree. -/
public theorem valid_insert {α : Type u} [LinearOrder α] {x : α} {tree : Tree α}
    (h : Valid tree) : Valid (insert x tree) :=
  valid_insert_of_invariants h.1 h.2.1 h.2.2.1

private theorem contains_eq_bstContains {α : Type u} [LinearOrder α] (x : α)
    (tree : Tree α) :
    contains x tree = BinarySearchTree.contains x (erase tree) := by
  induction tree with
  | empty => rfl
  | node _ left key right ihLeft ihRight =>
      simp only [contains, erase, BinarySearchTree.contains]
      by_cases hLeft : x < key
      · simp [hLeft, ihLeft]
      · by_cases hRight : key < x
        · simp [hLeft, hRight, ihRight]
        · simp [hLeft, hRight]

/-- Search is equivalent to structural membership for an ordered tree;
inherited from `BinarySearchTree` through `erase`. -/
public theorem contains_eq_true_iff {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (h : Ordered tree) :
    contains x tree = true ↔ x ∈ tree := by
  rw [contains_eq_bstContains]
  exact BinarySearchTree.contains_eq_true_iff h

/-- The inorder traversal of an ordered tree has no duplicate keys. -/
public theorem inorder_nodup {α : Type u} [LinearOrder α] {tree : Tree α}
    (h : Ordered tree) : (inorder tree).Nodup :=
  (ordered_inorder h).nodup

/-- The empty tree is a valid red-black tree. -/
public theorem valid_empty {α : Type u} [LT α] : Valid (.empty : Tree α) :=
  ⟨trivial, trivial, trivial, rfl⟩

/-- Building a tree by insertion always produces a valid tree. -/
public theorem valid_fromList {α : Type u} [LinearOrder α] {xs : List α} :
    Valid (fromList xs) := by
  induction xs with
  | nil => exact valid_empty
  | cons x xs ih => exact valid_insert ih

/-- A key is in a tree built from a list exactly when it is in the list. -/
public theorem mem_fromList {α : Type u} [LinearOrder α] {x : α} {xs : List α} :
    x ∈ fromList xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [fromList]
  | cons y ys ih => simp [fromList, mem_insert, ih]

end RedBlackTree
end Cslib.Algorithms.Lean
