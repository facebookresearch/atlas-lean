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

/-- **Red-black node colors.** The colors of red-black tree nodes are the two values red and
black. -/
public inductive Color where
  | red
  | black
  deriving DecidableEq, Repr

/-- **Red-black tree data type.** A red-black tree with keys in a type $\alpha$ is either empty or
a node consisting of a color (red or black), a left subtree, a key in $\alpha$, and a right
subtree.

No ordering, color or balance invariant is imposed by the type itself. -/
public inductive Tree (α : Type u) where
  | empty
  | node (color : Color) (left : Tree α) (key : α) (right : Tree α)
deriving DecidableEq, Repr

/-- **Color erasure.** The color erasure of a red-black tree is the binary tree obtained by
forgetting the node colors: the empty tree goes to the empty binary tree, and a node with key $k$
and subtrees $l$ and $r$ goes to the binary-tree node with key $k$ whose subtrees are the color
erasures of $l$ and $r$. -/
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

/-- **Membership in a red-black tree.** An element $x$ is a member of a red-black tree $t$ when $x$
is a member of the binary tree obtained from $t$ by erasing its colors, that is, when $x$ equals
the key of some node of $t$.

Membership is structural: it does not use the search-tree ordering. -/
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

/-- **Inorder traversal onto a suffix.** For a red-black tree $t$ and a list $s$, this is the
accumulator form of the binary-search-tree inorder traversal applied to the color erasure of $t$:
for the empty tree it returns $s$, and for a node with key $k$ and subtrees $l$ and $r$ it returns
the result for $l$ with suffix the list $k$ followed by $u$, where $u$ is the result for $r$ with
suffix $s$.

Thus the result lists the keys of $t$ in inorder followed by $s$, in time linear in the size
of $t$. -/
public def inorderAux {α : Type u} (tree : Tree α) (suffix : List α) : List α :=
  BinarySearchTree.inorderAux (erase tree) suffix

/-- **Inorder traversal of a red-black tree.** The inorder traversal of a red-black tree $t$ is
the binary-search-tree inorder traversal of the color erasure of $t$, computed in linear time
with an accumulator starting from the empty list. It lists the keys of $t$ from left to right:
the empty tree gives the empty list, and a node with key $k$ and subtrees $l$ and $r$ gives the
traversal of $l$, then $k$, then the traversal of $r$. -/
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

/-- **Predicate holding at every key of a red-black tree.** For a predicate $p$ on $\alpha$ and a
red-black tree $t$ with keys in $\alpha$, $p$ holds at every key of $t$ when $p$ holds at every key
of the binary search tree obtained from $t$ by erasing colors. -/
public def All {α : Type u} (p : α → Prop) (tree : Tree α) : Prop :=
  BinarySearchTree.All p (erase tree)

/-- **Ordered red-black tree.** Let $\alpha$ be a type with a relation $<$. A red-black tree with
keys in $\alpha$ is ordered when, at every node with key $k$, every key $y$ in the left subtree
satisfies $y < k$ and every key $z$ in the right subtree satisfies $k < z$.

Equivalently, the binary tree obtained by erasing the colors is an ordered binary search tree. -/
public def Ordered {α : Type u} [LT α] (tree : Tree α) : Prop :=
  BinarySearchTree.Ordered (erase tree)

/-- **Red-black membership is membership in the underlying binary tree.** For every red-black tree
$t$ and every $x$, $x$ is a member of $t$ if and only if $x$ is a member of the binary tree obtained
from $t$ by erasing its colors.

This holds by definition. -/
public theorem mem_erase {α : Type u} {x : α} {tree : Tree α} :
    x ∈ tree ↔ x ∈ erase tree :=
  Iff.rfl

/-- **All keys of a red-black tree via its color erasure.** For every predicate $p$ on $\alpha$
and every red-black tree $t$ with keys in $\alpha$, $p$ holds at every key of $t$ if and only if
$p$ holds at every key of the binary search tree obtained from $t$ by erasing colors. This holds
by definition. -/
public theorem all_erase {α : Type u} {p : α → Prop} {tree : Tree α} :
    All p tree ↔ BinarySearchTree.All p (erase tree) :=
  Iff.rfl

/-- **A red-black tree is ordered exactly when its underlying binary tree is.** For keys with a
relation $<$, a red-black tree $t$ is ordered if and only if the binary tree obtained from $t$ by
erasing its colors is an ordered binary search tree.

This holds by definition. -/
public theorem ordered_erase {α : Type u} [LT α] {tree : Tree α} :
    Ordered tree ↔ BinarySearchTree.Ordered (erase tree) :=
  Iff.rfl

/-- **Inorder traversal ignores colors.** For every red-black tree $t$, the inorder traversal of
$t$ equals the binary-search-tree inorder traversal of the color erasure of $t$; this holds by
definition. -/
public theorem inorder_erase {α : Type u} (tree : Tree α) :
    inorder tree = BinarySearchTree.inorder (erase tree) :=
  rfl

/-- **Root color.** The root color of a red-black tree is the color of its root node; the empty
tree has root color black. -/
public def colorOf {α : Type u} : Tree α → Color
  | .empty => .black
  | .node color _ _ _ => color

/-- **Red property of red-black trees.** A red-black tree satisfies the red property when no red
node has a red child, where empty subtrees count as black. -/
public def RedOk {α : Type u} : Tree α → Prop
  | .empty => True
  | .node .red left _ right =>
      RedOk left ∧ RedOk right ∧ colorOf left = .black ∧ colorOf right = .black
  | .node .black left _ right => RedOk left ∧ RedOk right

/-- **Red invariant away from the root.** A red-black tree satisfies the relaxed red invariant
when it is empty, or when its left and right subtrees both satisfy the red invariant (no red node
has a red child). The root itself is unconstrained, so a red root may have a red child.

This is the intermediate invariant of Okasaki's unchecked insertion. -/
public def AlmostRedOk {α : Type u} : Tree α → Prop
  | .empty => True
  | .node _ left _ right => RedOk left ∧ RedOk right

/-- **Black height.** The black height of a red-black tree is the number of black nodes on its
leftmost root-to-leaf path, counting the empty leaf as one black node: the empty tree has black
height $1$, a red node has the black height of its left subtree, and a black node has the black
height of its left subtree plus $1$. -/
public def blackHeight {α : Type u} : Tree α → Nat
  | .empty => 1
  | .node .red left _ _ => blackHeight left
  | .node .black left _ _ => blackHeight left + 1

/-- **Black-height balanced red-black tree.** A red-black tree is balanced when every root-to-leaf
path contains the same number of black nodes. Recursively: the empty tree is balanced, and a node
is balanced when both of its subtrees are balanced and have the same black height (the number of
black nodes on the leftmost root-to-leaf path, counting the leaf). -/
public def Balanced {α : Type u} : Tree α → Prop
  | .empty => True
  | .node _ left _ right =>
      Balanced left ∧ Balanced right ∧ blackHeight left = blackHeight right

/-- **Valid red-black tree.** Let $\alpha$ be a type with a relation $<$. A red-black tree with
keys in $\alpha$ is valid when it is ordered, satisfies the red property (no red node has a red
child), is balanced (every root-to-leaf path contains the same number of black nodes), and its
root is black, where the empty tree counts as black. -/
public def Valid {α : Type u} [LT α] (tree : Tree α) : Prop :=
  Ordered tree ∧ RedOk tree ∧ Balanced tree ∧ colorOf tree = .black

/-- **Search in a red-black tree.** Searching a red-black tree over a linearly ordered type for a
key $x$ returns a Boolean, ignoring colors: the empty tree gives false, and at a node with key $k$
the search continues in the left subtree if $x < k$, continues in the right subtree if $k < x$,
and returns true otherwise. -/
public def contains {α : Type u} [LinearOrder α] (x : α) : Tree α → Bool
  | .empty => false
  | .node _ left key right =>
      if x < key then contains x left
      else if key < x then contains x right
      else true

/-- **Okasaki's rebalancing.** Given a color $c$, red-black trees $l$ and $r$, and a key $k$,
rebalancing produces a tree as follows. Suppose $c$ is black and one of these configurations
occurs, taking the first that applies: $l$ is a red node with a red left child; $l$ is a red node
with a red right child; $r$ is a red node with a red left child; $r$ is a red node with a red
right child. The black root and the two red nodes then hold three keys and leave four subtrees,
which read in inorder as $t_1, x, t_2, y, t_3, z, t_4$. The result is a red node with key $y$, left
child the black node with subtrees $t_1, t_2$ and key $x$, and right child the black node with
subtrees $t_3, t_4$ and key $z$. In every other case the result is the node with color $c$, left
subtree $l$, key $k$ and right subtree $r$. -/
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

/-- **Unchecked red-black insertion.** For keys from a linearly ordered type, the unchecked
insertion of $x$ into a red-black tree is defined by recursion on the tree. Inserting $x$ into the
empty tree gives a red node with key $x$ and two empty subtrees. Inserting $x$ into a node with
color $c$, left subtree $l$, key $k$ and right subtree $r$ gives: if $x < k$, Okasaki's
rebalancing of color $c$, left subtree the insertion of $x$ into $l$, key $k$ and right subtree
$r$; if $k < x$, Okasaki's rebalancing of color $c$, left subtree $l$, key $k$ and right subtree
the insertion of $x$ into $r$; otherwise the node itself, unchanged.

The result may have a red root with a red child, so it need not satisfy the red invariant. -/
def ins {α : Type u} [LinearOrder α] (x : α) : Tree α → Tree α
  | .empty => .node .red .empty x .empty
  | tree@(.node color left key right) =>
      if x < key then balance color (ins x left) key right
      else if key < x then balance color left key (ins x right)
      else tree

/-- **Blackening the root.** Recoloring the root of a red-black tree black leaves the empty tree
unchanged and turns a node with any color, left subtree $l$, key $k$ and right subtree $r$ into the
black node with left subtree $l$, key $k$ and right subtree $r$. -/
def makeBlack {α : Type u} : Tree α → Tree α
  | .empty => .empty
  | .node _ left key right => .node .black left key right

/-- **Recoloring the root black does not change the color erasure.** For every red-black
tree $t$, the color erasure of the tree obtained from $t$ by recoloring its root black (the empty
tree is left unchanged) equals the color erasure of $t$. -/
public theorem erase_makeBlack {α : Type u} {tree : Tree α} :
    erase (makeBlack tree) = erase tree := by
  cases tree <;> rfl

/-- **Red-black tree insertion.** For keys from a linearly ordered type, inserting $x$ into a
red-black tree $t$ gives the unchecked insertion of $x$ into $t$ with its root recolored black. -/
public def insert {α : Type u} [LinearOrder α] (x : α) (tree : Tree α) :
    Tree α :=
  makeBlack (ins x tree)

/-- **Red-black tree from a list.** The red-black tree built from a list over a linearly ordered
type inserts the elements of the list into the empty tree from right to left: the empty list
gives the empty tree, and a list with head $x$ and tail $xs$ gives the insertion of $x$ into the
tree built from $xs$. -/
public def fromList {α : Type u} [LinearOrder α] : List α → Tree α
  | [] => .empty
  | x :: xs => insert x (fromList xs)

/-- **All keys versus members of a red-black tree.** For every predicate $p$ on $\alpha$ and every
red-black tree $t$ with keys in $\alpha$, $p$ holds at every key of $t$ if and only if $p(x)$ holds
for every $x \in \alpha$ that is a (structural) member of $t$. -/
public theorem all_iff_forall_mem {α : Type u} {p : α → Prop} {tree : Tree α} :
    All p tree ↔ ∀ x, x ∈ tree → p x :=
  BinarySearchTree.all_iff_forall_mem

/-- **Membership in the inorder traversal of a red-black tree.** For every red-black tree $t$ and
every $x$, $x$ occurs in the inorder traversal of $t$ if and only if $x$ is a member of $t$. -/
public theorem mem_inorder {α : Type u} {x : α} {tree : Tree α} :
    x ∈ inorder tree ↔ x ∈ tree :=
  BinarySearchTree.mem_inorder

/-- **The inorder traversal of an ordered red-black tree is strictly increasing.** For keys from a
linearly ordered type, if a red-black tree $t$ is ordered, then every entry of the inorder
traversal of $t$ is strictly smaller than every later entry. -/
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

/-- **Membership after insertion into a red-black tree.** For keys from a linearly ordered type, a
key $y$ is a member of the red-black tree obtained by inserting $x$ into $t$ if and only if $y = x$
or $y$ is a member of $t$. -/
public theorem mem_insert {α : Type u} [LinearOrder α] {x y : α} {tree : Tree α} :
    y ∈ insert x tree ↔ y = x ∨ y ∈ tree := by
  simp only [insert, mem_makeBlack, mem_ins]

/-- **Red-black insertion preserves the search-tree order.** Let $\alpha$ be a linearly ordered
type, $x \in \alpha$ a key, and $t$ a red-black tree with keys in $\alpha$. If $t$ is ordered (at
every node with key $k$, every key in the left subtree is less than $k$ and every key in the right
subtree is greater than $k$), then the tree obtained by inserting $x$ into $t$ is ordered. -/
public theorem ordered_insert {α : Type u} [LinearOrder α] {x : α} {tree : Tree α}
    (h : Ordered tree) : Ordered (insert x tree) :=
  ordered_makeBlack (ordered_ins h)

/-- **Red-black insertion preserves the red property.** Let $\alpha$ be a linearly ordered type,
$x \in \alpha$ a key, and $t$ a red-black tree with keys in $\alpha$. If no red node of $t$ has a
red child, then no red node of the tree obtained by inserting $x$ into $t$ has a red child. -/
public theorem redOk_insert {α : Type u} [LinearOrder α] {x : α} {tree : Tree α}
    (h : RedOk tree) : RedOk (insert x tree) :=
  redOk_makeBlack (almostRedOk_ins h).1

/-- **Red-black insertion preserves black-height balance.** Let $\alpha$ be a linearly ordered type.
If a red-black tree $t$ with keys in $\alpha$ is balanced (every root-to-leaf path contains the same
number of black nodes), then for every $x \in \alpha$ the tree obtained by inserting $x$ into $t$ is
balanced. -/
public theorem balanced_insert {α : Type u} [LinearOrder α] {x : α} {tree : Tree α}
    (h : Balanced tree) : Balanced (insert x tree) :=
  balanced_makeBlack (balanced_ins h)

/-- **Insertion raises the black height by at most one.** Let $\alpha$ be a linearly ordered type.
For every red-black tree $t$ with keys in $\alpha$ and every $x \in \alpha$, the black height of the
tree obtained by inserting $x$ into $t$ equals either the black height of $t$ or the black height of
$t$ plus one.

Any increase comes from recoloring the root black at the end of insertion. -/
public theorem blackHeight_insert {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} :
    blackHeight (insert x tree) = blackHeight tree ∨
      blackHeight (insert x tree) = blackHeight tree + 1 := by
  show blackHeight (makeBlack (ins x tree)) = blackHeight tree ∨
    blackHeight (makeBlack (ins x tree)) = blackHeight tree + 1
  rcases blackHeight_makeBlack (tree := ins x tree) with h | h
  · exact Or.inl (h.trans blackHeight_ins)
  · exact Or.inr (by rw [h, blackHeight_ins])

/-- **Red-black insertion yields a valid tree from the invariants.** Let $\alpha$ be a linearly
ordered type, $x \in \alpha$ a key, and $t$ a red-black tree with keys in $\alpha$ that is
ordered, satisfies the red property (no red node has a red child), and is balanced (every
root-to-leaf path contains the same number of black nodes). Then the tree obtained by inserting
$x$ into $t$ is valid.

The root of $t$ need not be black, since insertion recolors the root black. -/
public theorem valid_insert_of_invariants {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hOrdered : Ordered tree) (hRedOk : RedOk tree)
    (hBalanced : Balanced tree) : Valid (insert x tree) :=
  ⟨ordered_insert hOrdered, redOk_insert hRedOk, balanced_insert hBalanced,
    colorOf_makeBlack⟩

/-- **Red-black insertion preserves validity.** Let $\alpha$ be a linearly ordered type and
$x \in \alpha$. If $t$ is a valid red-black tree with keys in $\alpha$, then the tree obtained by
inserting $x$ into $t$ is also valid. -/
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

/-- **Search in an ordered red-black tree is correct.** Let $t$ be a red-black tree over a
linearly ordered type that is ordered (every left key is smaller and every right key larger,
recursively). Then for every key $x$, the search for $x$ in $t$ returns true if and only if $x$
is a key of some node of $t$. -/
public theorem contains_eq_true_iff {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (h : Ordered tree) :
    contains x tree = true ↔ x ∈ tree := by
  rw [contains_eq_bstContains]
  exact BinarySearchTree.contains_eq_true_iff h

/-- **Ordered red-black trees have duplicate-free inorder traversals.** For a red-black tree $t$
over a linearly ordered type that is ordered (every left key is smaller and every right key
larger, recursively), the inorder traversal of $t$ contains no key twice. -/
public theorem inorder_nodup {α : Type u} [LinearOrder α] {tree : Tree α}
    (h : Ordered tree) : (inorder tree).Nodup :=
  (ordered_inorder h).nodup

/-- **The empty red-black tree is valid.** For every type $\alpha$ with a relation $<$, the empty
red-black tree with keys in $\alpha$ is a valid red-black tree. -/
public theorem valid_empty {α : Type u} [LT α] : Valid (.empty : Tree α) :=
  ⟨trivial, trivial, trivial, rfl⟩

/-- **Red-black trees built from a list are valid.** Let $\alpha$ be a linearly ordered type. For
every list $l$ of elements of $\alpha$, the red-black tree obtained from the empty tree by
inserting the elements of $l$ one at a time, from the last to the first, is valid. -/
public theorem valid_fromList {α : Type u} [LinearOrder α] {xs : List α} :
    Valid (fromList xs) := by
  induction xs with
  | nil => exact valid_empty
  | cons x xs ih => exact valid_insert ih

/-- **Membership in a red-black tree built from a list.** For keys from a linearly ordered type and
every list $xs$, a key $x$ is a member of the red-black tree built from $xs$ by successive
insertion if and only if $x$ occurs in $xs$. -/
public theorem mem_fromList {α : Type u} [LinearOrder α] {x : α} {xs : List α} :
    x ∈ fromList xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [fromList]
  | cons y ys ih => simp [fromList, mem_insert, ih]

end RedBlackTree
end Cslib.Algorithms.Lean
