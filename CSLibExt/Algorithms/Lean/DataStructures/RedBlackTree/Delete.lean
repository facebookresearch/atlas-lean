/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree
public import Mathlib.Data.List.Sort

/-!
# Red-black tree deletion

Deletion for the red-black trees of
`CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree`, in two stages.
First, `del` is the ordinary unbalanced binary-search-tree deletion: it
follows comparisons from the root and splices the two subtrees of a deleted
node together with `join`, ignoring colors, so the result need not satisfy
`RedOk` or `Balanced`. Second, `rebalance` rebuilds a valid red-black tree
from the inorder traversal of the intermediate tree by repeated Okasaki
insertion (`fromList`), whose validity is already established in the parent
module. The public `delete` is the composite: it satisfies the same inorder
specification as unbalanced deletion (`inorder_delete`), removes exactly the
deleted key (`mem_delete`), and always produces a `Valid` tree
(`valid_delete`). The traversal and membership specifications assume the
strict invariant `Ordered`, matching `contains_eq_true_iff` in the parent
module.

This delete-by-rebuild takes linearithmic time in the size of the tree, not
the logarithmic time of a double-black (Kahrs) deletion that repairs the
black-height invariant locally along the search path; the staged invariant
proofs here deliberately reuse `valid_fromList` instead of a local repair.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace RedBlackTree

/--
**Splicing two red-black trees.** The splice of a red-black tree $t$ with a red-black tree $s$ is
defined by recursion on $t$. The splice of the empty tree with $s$ is $s$. The splice of the node
with color $c$, left subtree $l$, key $k$ and right subtree $r$ with $s$ is the node with color
$c$, left subtree $l$, key $k$ and right subtree the splice of $r$ with $s$.

So $s$ becomes the right subtree of the rightmost node of $t$, and all existing colors are kept.
-/
public def join {α : Type u} : Tree α → Tree α → Tree α
  | .empty, right => right
  | .node color left key right, other =>
      .node color left key (join right other)

/--
**Unbalanced red-black tree deletion.** For a key $x$ of a linearly ordered type, unbalanced
deletion of $x$ from a red-black tree is defined by recursion on the tree. The empty tree stays
empty. At a node with color $c$, left subtree $l$, key $k$ and right subtree $r$: if $x < k$, the
result is the node with color $c$, left subtree the unbalanced deletion of $x$ from $l$, key $k$
and right subtree $r$; if $k < x$, it is the node with color $c$, left subtree $l$, key $k$ and
right subtree the unbalanced deletion of $x$ from $r$; otherwise (so $x = k$) it is the splice of
$l$ with $r$.

Colors are kept, so the result need not satisfy the red invariant or be black-height balanced.
-/
def del {α : Type u} [LinearOrder α] (x : α) : Tree α → Tree α
  | .empty => .empty
  | .node color left key right =>
      if x < key then .node color (del x left) key right
      else if key < x then .node color left key (del x right)
      else join left right

/-- **Rebuilding a red-black tree from its keys.** For a linearly ordered key type, the rebuild of
a red-black tree $t$ is the tree obtained from the empty tree by inserting the keys of the inorder
traversal of $t$ one at a time with Okasaki insertion, starting from the last key.

The result is a valid red-black tree whose keys are exactly the keys of $t$. -/
def rebalance {α : Type u} [LinearOrder α] (tree : Tree α) : Tree α :=
  fromList (inorder tree)

/-- **Red-black tree deletion by rebuilding.** For a key $x$ of a linearly ordered type and a
red-black tree $t$, deleting $x$ from $t$ by rebuilding first forms the unbalanced deletion of
$x$ from $t$, then rebalances it: starting from the empty tree, it inserts the keys of the inorder
traversal of that tree one at a time, from the last key to the first. -/
public def delete {α : Type u} [LinearOrder α] (x : α) (tree : Tree α) :
    Tree α :=
  rebalance (del x tree)

@[simp] private theorem mem_empty_delete {α : Type u} {x : α} :
    x ∈ (Tree.empty : Tree α) ↔ False :=
  Iff.rfl

@[simp] private theorem mem_node_delete {α : Type u} {x key : α}
    {color : Color} {left right : Tree α} :
    x ∈ Tree.node color left key right ↔ x ∈ left ∨ x = key ∨ x ∈ right :=
  Iff.rfl

/-- **Membership in a splice.** For red-black trees $t$ and $s$ with keys of any type, a key $x$
belongs to the splice of $t$ with $s$ if and only if $x$ belongs to $t$ or $x$ belongs to $s$. -/
public theorem mem_join {α : Type u} {x : α} {left right : Tree α} :
    x ∈ join left right ↔ x ∈ left ∨ x ∈ right := by
  induction left with
  | empty => simp [join]
  | node color leftLeft key leftRight _ ihRight =>
    simp only [join, mem_node_delete, ihRight]
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

/-- **Inorder traversal of a splice.** For red-black trees $t$ and $s$ with keys of any type,
the inorder traversal of the splice of $t$ with $s$ is the inorder traversal of $t$ followed by the
inorder traversal of $s$. -/
public theorem inorder_join {α : Type u} {left right : Tree α} :
    inorder (join left right) = inorder left ++ inorder right := by
  induction left with
  | empty => simp [join]
  | node color leftLeft key leftRight _ ihRight =>
    simp only [join, inorder_node, ihRight]
    rw [List.append_assoc, List.cons_append]

private theorem all_join {α : Type u} {p : α → Prop} {left right : Tree α}
    (hLeft : All p left) (hRight : All p right) : All p (join left right) := by
  refine all_iff_forall_mem.mpr (fun x hx => ?_)
  rw [mem_join] at hx
  rcases hx with hx | hx
  · exact (all_iff_forall_mem.mp hLeft) x hx
  · exact (all_iff_forall_mem.mp hRight) x hx

/--
**Joining separated ordered trees preserves order.** Let $<$ be a relation on the keys, and let
$L$ and $R$ be red-black trees that are ordered for $<$ such that $a < b$ for every key $a$ of $L$
and every key $b$ of $R$. Then the join of $L$ and $R$, obtained by putting $R$ in place of the
empty right subtree of the rightmost node of $L$ (or $R$ itself if $L$ is empty) and keeping all
colors, is ordered.
-/
public theorem ordered_join {α : Type u} [LT α] {left right : Tree α}
    (hLeft : Ordered left) (hRight : Ordered right)
    (hSeparated : ∀ a ∈ left, ∀ b ∈ right, a < b) :
    Ordered (join left right) := by
  induction left with
  | empty => simpa [join] using hRight
  | node color leftLeft key leftRight _ ihRight =>
    rcases hLeft with ⟨hLeftLeft, hLeftRight, hAllLeftLeft, hAllLeftRight⟩
    have hSeparatedRight : ∀ a ∈ leftRight, ∀ b ∈ right, a < b :=
      fun a ha b hb => hSeparated a (Or.inr (Or.inr ha)) b hb
    have hKeyRight : All (key < ·) right :=
      all_iff_forall_mem.mpr
        (fun b hb => hSeparated key (Or.inr (Or.inl rfl)) b hb)
    simp only [join]
    exact ⟨hLeftLeft, ihRight hLeftRight hSeparatedRight, hAllLeftLeft,
      all_join hAllLeftRight hKeyRight⟩

private theorem mem_of_mem_del {α : Type u} [LinearOrder α] {x y : α}
    {tree : Tree α} (hy : y ∈ del x tree) : y ∈ tree := by
  induction tree with
  | empty => simp [del] at hy
  | node color left key right ihLeft ihRight =>
    by_cases hxKey : x < key
    · simp only [del, ite_eq_left hxKey, mem_node_delete] at hy
      rcases hy with hy | hy | hy
      · exact Or.inl (ihLeft hy)
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hy)
    · by_cases hKeyX : key < x
      · simp only [del, ite_eq_right hxKey, ite_eq_left hKeyX,
          mem_node_delete] at hy
        rcases hy with hy | hy | hy
        · exact Or.inl hy
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (ihRight hy))
      · simp only [del, ite_eq_right hxKey, ite_eq_right hKeyX] at hy
        rw [mem_join] at hy
        rcases hy with hy | hy
        · exact Or.inl hy
        · exact Or.inr (Or.inr hy)

private theorem mem_del_of_mem {α : Type u} [LinearOrder α] {x y : α}
    {tree : Tree α} (hy : y ∈ tree) (hxy : y ≠ x) : y ∈ del x tree := by
  induction tree with
  | empty => exact (mem_empty_delete.mp hy).elim
  | node color left key right ihLeft ihRight =>
    rw [mem_node_delete] at hy
    by_cases hxKey : x < key
    · simp only [del, ite_eq_left hxKey, mem_node_delete]
      rcases hy with hy | hy | hy
      · exact Or.inl (ihLeft hy)
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hy)
    · by_cases hKeyX : key < x
      · simp only [del, ite_eq_right hxKey, ite_eq_left hKeyX, mem_node_delete]
        rcases hy with hy | hy | hy
        · exact Or.inl hy
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (ihRight hy))
      · have hxEq : x = key :=
          le_antisymm (le_of_not_gt hKeyX) (le_of_not_gt hxKey)
        simp only [del, ite_eq_right hxKey, ite_eq_right hKeyX, mem_join]
        rcases hy with hy | hy | hy
        · exact Or.inl hy
        · exact absurd (hy.trans hxEq.symm) hxy
        · exact Or.inr hy

private theorem not_mem_del_self {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Ordered tree) : x ∉ del x tree := by
  induction tree with
  | empty => simp [del]
  | node color left key right ihLeft ihRight =>
    rcases hTree with ⟨hLeft, hRight, hAllLeft, hAllRight⟩
    by_cases hxKey : x < key
    · simp only [del, ite_eq_left hxKey, mem_node_delete]
      rintro (hx | hx | hx)
      · exact ihLeft hLeft hx
      · exact ne_of_lt hxKey hx
      · exact lt_asymm hxKey ((all_iff_forall_mem.mp hAllRight) x hx)
    · by_cases hKeyX : key < x
      · simp only [del, ite_eq_right hxKey, ite_eq_left hKeyX, mem_node_delete]
        rintro (hx | hx | hx)
        · exact lt_asymm hKeyX ((all_iff_forall_mem.mp hAllLeft) x hx)
        · exact ne_of_gt hKeyX hx
        · exact ihRight hRight hx
      · have hxEq : x = key :=
          le_antisymm (le_of_not_gt hKeyX) (le_of_not_gt hxKey)
        simp only [del, ite_eq_right hxKey, ite_eq_right hKeyX, mem_join]
        subst x
        rintro (hx | hx)
        · exact lt_irrefl key ((all_iff_forall_mem.mp hAllLeft) key hx)
        · exact lt_irrefl key ((all_iff_forall_mem.mp hAllRight) key hx)

private theorem mem_del {α : Type u} [LinearOrder α] {x y : α}
    {tree : Tree α} (hTree : Ordered tree) :
    y ∈ del x tree ↔ y ∈ tree ∧ y ≠ x := by
  constructor
  · intro hy
    refine ⟨mem_of_mem_del hy, ?_⟩
    rintro rfl
    exact not_mem_del_self hTree hy
  · rintro ⟨hy, hxy⟩
    exact mem_del_of_mem hy hxy

private theorem all_del {α : Type u} [LinearOrder α] {p : α → Prop} {x : α}
    {tree : Tree α} (hTree : All p tree) : All p (del x tree) :=
  all_iff_forall_mem.mpr
    (fun y hy => (all_iff_forall_mem.mp hTree) y (mem_of_mem_del hy))

private theorem ordered_del {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Ordered tree) : Ordered (del x tree) := by
  induction tree with
  | empty => simp [del, Ordered, BinarySearchTree.Ordered]
  | node color left key right ihLeft ihRight =>
    rcases hTree with ⟨hLeft, hRight, hAllLeft, hAllRight⟩
    by_cases hxKey : x < key
    · simp only [del, ite_eq_left hxKey]
      exact ⟨ihLeft hLeft, hRight, all_del hAllLeft, hAllRight⟩
    · by_cases hKeyX : key < x
      · simp only [del, ite_eq_right hxKey, ite_eq_left hKeyX]
        exact ⟨hLeft, ihRight hRight, hAllLeft, all_del hAllRight⟩
      · simp only [del, ite_eq_right hxKey, ite_eq_right hKeyX]
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

private theorem inorder_del {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Ordered tree) :
    inorder (del x tree) = (inorder tree).erase x := by
  induction tree with
  | empty => simp [del]
  | node color left key right ihLeft ihRight =>
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
      simp only [del, ite_eq_left hxKey, inorder_node, ihLeft hLeft]
      exact (erase_append_of_not_mem_right hxCons).symm
    · by_cases hKeyX : key < x
      · have hxLeft : x ∉ inorder left := by
          rw [mem_inorder]
          intro hx
          exact lt_asymm hKeyX ((all_iff_forall_mem.mp hAllLeft) x hx)
        simp only [del, ite_eq_right hxKey, ite_eq_left hKeyX, inorder_node,
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
        simp only [del, ite_eq_right hxKey, inorder_join, inorder_node]
        rw [erase_append_of_not_mem_left hKeyLeft, List.erase_cons_head]

private theorem mem_rebalance {α : Type u} [LinearOrder α] {y : α}
    {tree : Tree α} : y ∈ rebalance tree ↔ y ∈ tree := by
  simp only [rebalance, mem_fromList, mem_inorder]

private theorem inorder_fromList_of_pairwise {α : Type u} [LinearOrder α]
    {l : List α} (h : List.Pairwise (· < ·) l) :
    inorder (fromList l) = l :=
  List.Pairwise.eq_of_mem_iff (ordered_inorder valid_fromList.1) h
    (fun a => by rw [mem_inorder, mem_fromList])

private theorem inorder_rebalance {α : Type u} [LinearOrder α] {tree : Tree α}
    (hTree : Ordered tree) : inorder (rebalance tree) = inorder tree :=
  inorder_fromList_of_pairwise (ordered_inorder hTree)

private theorem valid_rebalance {α : Type u} [LinearOrder α] {tree : Tree α} :
    Valid (rebalance tree) :=
  valid_fromList

/-- **Membership after deletion by rebuilding.** Let $x$ and $y$ be keys of a linearly ordered
type and let $t$ be an ordered red-black tree. Then $y$ belongs to the tree obtained from $t$ by
deleting $x$ by rebuilding if and only if $y$ belongs to $t$ and $y \ne x$. -/
public theorem mem_delete {α : Type u} [LinearOrder α] {x y : α}
    {tree : Tree α} (hTree : Ordered tree) :
    y ∈ delete x tree ↔ y ∈ tree ∧ y ≠ x := by
  show y ∈ rebalance (del x tree) ↔ y ∈ tree ∧ y ≠ x
  rw [mem_rebalance, mem_del hTree]

/-- **The deleted key is absent after deletion by rebuilding.** Let $x$ be a key of a linearly
ordered type and let $t$ be an ordered red-black tree. Then $x$ does not belong to the tree
obtained from $t$ by deleting $x$ by rebuilding. -/
public theorem not_mem_delete_self {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Ordered tree) : x ∉ delete x tree :=
  fun hx => ((mem_delete hTree).mp hx).2 rfl

/-- **Inorder traversal after deletion by rebuilding.** Let $x$ be a key of a linearly ordered
type and let $t$ be an ordered red-black tree. Then the inorder traversal of the tree obtained from
$t$ by deleting $x$ by rebuilding is the inorder traversal of $t$ with the first occurrence of $x$
removed (it is unchanged if $x$ does not occur). -/
public theorem inorder_delete {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Ordered tree) :
    inorder (delete x tree) = (inorder tree).erase x := by
  show inorder (rebalance (del x tree)) = (inorder tree).erase x
  rw [inorder_rebalance (ordered_del hTree), inorder_del hTree]

/-- **Red-black deletion yields a valid red-black tree.** For every linearly ordered key type,
every key $x$ and every red-black tree $t$, the tree obtained by deleting $x$ from $t$ is a valid
red-black tree: it is ordered, no red node has a red child, every root-to-leaf path contains the
same number of black nodes, and its root is black (the empty tree counts as black). No hypothesis
on $t$ is needed.

The result is valid because deletion rebuilds the tree by repeated insertion, which always
produces a valid red-black tree. -/
public theorem valid_delete {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} : Valid (delete x tree) :=
  valid_rebalance

/-- **Red-black deletion yields an ordered tree.** For every linearly ordered key type, every key
$x$ and every red-black tree $t$, the tree obtained by deleting $x$ from $t$ is ordered: at every
node, all keys in the left subtree are strictly smaller than the node's key and all keys in the
right subtree are strictly larger. No hypothesis on $t$ is needed. -/
public theorem ordered_delete {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} : Ordered (delete x tree) :=
  valid_rebalance.1

/-- **Red-black deletion yields a tree with no red-red edge.** For every linearly ordered key
type, every key $x$ and every red-black tree $t$, the tree obtained by deleting $x$ from $t$
satisfies the red invariant: no red node has a red child. No hypothesis on $t$ is needed. -/
public theorem redOk_delete {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} : RedOk (delete x tree) :=
  valid_rebalance.2.1

/-- **Deletion by rebuilding is black-height balanced.** For every linearly ordered type of
keys, every key $x$ and every red-black tree $t$, with no hypothesis on $t$, the tree obtained
from $t$ by deleting $x$ by rebuilding is black-height balanced. -/
public theorem balanced_delete {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} : Balanced (delete x tree) :=
  valid_rebalance.2.2.1

/-- **Deletion by rebuilding gives a black root.** For every linearly ordered type of keys,
every key $x$ and every red-black tree $t$, with no hypothesis on $t$, the root of the tree
obtained from $t$ by deleting $x$ by rebuilding is black, where the empty tree counts as having
a black root. -/
public theorem colorOf_delete {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} : colorOf (delete x tree) = .black :=
  valid_rebalance.2.2.2

end RedBlackTree
end Cslib.Algorithms.Lean
