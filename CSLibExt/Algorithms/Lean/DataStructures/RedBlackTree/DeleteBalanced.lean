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
# Red-black tree deletion by double-black bubbles

Logarithmic deletion for the red-black trees of
`CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree`, by the classic
double-black (Kahrs) method. Unlike `RedBlackTree.delete`, which
rebuilds the whole tree from its inorder traversal, `deleteBal` here repairs
the black-height invariant locally along the search path.

A deletion that removes a black node leaves its subtree one black node short
on every root-to-leaf path. The shortfall is represented by a *double-black*
root: the auxiliary type `BBTree` is either a genuine tree (`.regular`), a
double-black empty tree (`.emptyBB`, the result of deleting a black leaf), or
a double-black node (`.nodeBB`) whose children are genuine trees. Only the
root of a `BBTree` can be double black; this bubble invariant is built into
the type, since the children of `.nodeBB` have the parent module's type
`Tree`. The extended root color is `BColor`, with `.doubleBlack` counting as
two black nodes for `bhBB`, so a balanced tree and its double-black
counterpart have the same `bhBB` as the original `blackHeight`.

The core `del` descends once from the root. When the recursive result is
double black, `balLeft`/`balRight` (through `fixLeft`/`fixRight`) repair it
against its sibling: a red far nephew is repaired by a single rotation, a red
near nephew by a double rotation, and two black nephews by reddening the
sibling and bubbling the double black to the parent (a red sibling is first
rotated to the parent's place, reducing to the black-sibling cases under a
red parent). Deleting a node with two children promotes its successor, the
minimum key of the right subtree. The public `deleteBal` finishes with
`blacken`, which absorbs a remaining double black at the root. Every step
except the single descent touches O(1) nodes, so `deleteBal` visits
O(height) nodes.

The specifications match `RedBlackTree.Delete`, with their preconditions
kept distinct: for an ordered tree (`Ordered tree`),
`inorder_deleteBal` erases the key from the inorder traversal and
`mem_deleteBal` removes exactly the deleted key; for a tree satisfying
the three structural invariants `Ordered`, `RedOk`, and `Balanced`,
`valid_deleteBal_of_invariants` concludes that the result again
satisfies the red-black invariants (the input root need not be black),
and `valid_deleteBal` wraps it for `Valid tree`. Deleting from a tree
without the structural invariants need not produce a valid one.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace RedBlackTree
namespace DeleteBalanced

/-- **Extended root colors.** An extended color is one of three values: red, black or double
black.

Double black marks the root of a tree after a deletion and counts as two black nodes in its black
height. -/
public inductive BColor where
  | red
  | black
  | doubleBlack
  deriving DecidableEq

/-- **Trees with a possibly double-black root.** A tree with a possibly double-black root over a
type $\alpha$ is one of the following: a genuine red-black tree over $\alpha$; the double-black
empty tree; or a double-black node consisting of a left subtree, a key in $\alpha$ and a right
subtree, where both subtrees are genuine red-black trees. Hence a double black can occur only at
the root. -/
public inductive BBTree (α : Type u) where
  | regular (tree : Tree α)
  | emptyBB
  | nodeBB (left : Tree α) (key : α) (right : Tree α)

/-- **Inorder traversal of a possibly double-black tree.** The inorder traversal of a red-black
tree whose root may be double black ignores the double-black mark: a genuine tree gives its
inorder traversal, the double-black empty tree gives the empty list, and a double-black node with
left child $l$, key $k$ and right child $r$ gives the inorder traversal of $l$, followed by $k$,
followed by the inorder traversal of $r$. -/
public def inorderBB {α : Type u} : BBTree α → List α
  | .regular tree => inorder tree
  | .emptyBB => []
  | .nodeBB left key right => inorder left ++ key :: inorder right

/-- **Black height of a possibly double-black tree.** The black height of a genuine red-black tree
is its usual black height. The double-black empty tree has black height $2$, and a double-black
node with left subtree $L$ has black height $h(L) + 2$, where $h(L)$ is the usual black height of
$L$. Thus a double-black root counts as two black nodes, where the usual black height counts the
empty tree as one.

For an ordered, balanced red-black tree satisfying the red invariant, deleting any key by the
double-black descent, before the root is blackened, yields a tree whose black height in this sense
equals the black height of the original tree. -/
public def bhBB {α : Type u} : BBTree α → Nat
  | .regular tree => blackHeight tree
  | .emptyBB => 2
  | .nodeBB left _ _ => blackHeight left + 2

/-- **Black-height balance of a possibly double-black tree.** A tree whose root may be double
black is balanced when it is a genuine red-black tree that is balanced, when it is the
double-black empty tree, or when it is a double-black node whose left and right subtrees are both
balanced and have the same black height. -/
public def BalancedBB {α : Type u} : BBTree α → Prop
  | .regular tree => Balanced tree
  | .emptyBB => True
  | .nodeBB left _ right =>
      Balanced left ∧ Balanced right ∧ blackHeight left = blackHeight right

/-- **Red invariant for trees with a possibly double-black root.** A tree whose root may be
double black satisfies the red invariant in the following cases: a genuine red-black tree
satisfies it when it satisfies the usual red invariant (no red node has a red child); the
double-black empty tree always satisfies it; and a double-black node with left subtree $l$ and
right subtree $r$ satisfies it when both $l$ and $r$ satisfy the usual red invariant. -/
public def RedOkBB {α : Type u} : BBTree α → Prop
  | .regular tree => RedOk tree
  | .emptyBB => True
  | .nodeBB left _ right => RedOk left ∧ RedOk right

/-- **Extended root color.** The extended color of a tree whose root may be double black is the
color of its root, red or black, when it is a genuine red-black tree, where the empty tree counts
as black; it is double black for the double-black empty tree and for every double-black node. -/
public def colorBB {α : Type u} : BBTree α → BColor
  | .regular tree =>
      match colorOf tree with
      | .red => .red
      | .black => .black
  | .emptyBB => .doubleBlack
  | .nodeBB _ _ _ => .doubleBlack

/-- **Adding a black to the root.** Add one black to the root of a red-black tree, producing a
tree whose root may be double black: the empty tree becomes the double-black empty tree, a red
root becomes black, and a black root becomes double black. -/
public def incrBlack {α : Type u} : Tree α → BBTree α
  | .empty => .emptyBB
  | .node .red left key right => .regular (.node .black left key right)
  | .node .black left key right => .nodeBB left key right

/-- **Recoloring the root black.** For a red-black tree $t$, this is the tree obtained from $t$
by coloring its root black: the empty tree stays empty, and a node with left subtree $l$, key
$k$ and right subtree $r$, of either color, becomes the black node with left subtree $l$, key
$k$ and right subtree $r$. -/
public def rootBlack {α : Type u} : Tree α → Tree α
  | .empty => .empty
  | .node _ left key right => .node .black left key right

/-- **Absorbing a double-black root.** Blackening sends a tree whose root may be double black to
a genuine red-black tree by changing only its root: a genuine tree has its root recolored black
(the empty tree stays empty), the double-black empty tree becomes the empty tree, and a
double-black node becomes the black node with the same subtrees and key. -/
public def blacken {α : Type u} : BBTree α → Tree α
  | .regular tree => rootBlack tree
  | .emptyBB => .empty
  | .nodeBB left key right => .node .black left key right

/-- **Leftmost key of a red-black tree.** For a red-black tree $t$ over a type $\alpha$, the
leftmost key of $t$ is either a key in $\alpha$ or undefined. It is undefined when $t$ is empty.
When $t$ is a node, of either color, with left subtree $l$ and key $k$, it is the leftmost key of
$l$ if that is defined, and $k$ otherwise. Hence the leftmost key is defined exactly when $t$ is
nonempty.

Under the search-tree invariant the leftmost key is the minimum key of the tree. -/
def minKey {α : Type u} : Tree α → Option α
  | .empty => none
  | .node _ left key _ =>
      match minKey left with
      | some s => some s
      | none => some key

/-- **Left repair after double-black deletion.** Write $\mathrm{R}$ and $\mathrm{B}$ for red and
black, and $N(c, T, y, T')$ for the node of color $c$ with left subtree $T$, key $y$ and right
subtree $T'$. Given a color $c$, a tree $D$, a key $k$ and a tree $S$, the left repair returns a
tree whose root may be double black, by the first case that applies. If
$S = N(\mathrm{B}, T_1, y, N(\mathrm{R}, T_2, z, T_3))$ or, failing that,
$S = N(\mathrm{B}, N(\mathrm{R}, T_1, y, T_2), z, T_3)$, it returns
$N(c, N(\mathrm{B}, D, k, T_1), y, N(\mathrm{B}, T_2, z, T_3))$. Otherwise, if
$S = N(\mathrm{B}, T_1, y, T_2)$, it returns $N(\mathrm{B}, D, k, N(\mathrm{R}, T_1, y, T_2))$ when
$c$ is red, and the double-black node with left child $D$, key $k$ and right child
$N(\mathrm{R}, T_1, y, T_2)$ when $c$ is black. In the next three cases $c$ is not used. If
$S = N(\mathrm{R}, N(\mathrm{B}, T_1, y, N(\mathrm{R}, T_2, z, T_3)), w, T_4)$ or, failing that,
$S = N(\mathrm{R}, N(\mathrm{B}, N(\mathrm{R}, T_1, y, T_2), z, T_3), w, T_4)$, it returns
$N(\mathrm{B}, N(\mathrm{R}, N(\mathrm{B}, D, k, T_1), y, N(\mathrm{B}, T_2, z, T_3)), w, T_4)$.
Otherwise, if $S = N(\mathrm{R}, N(\mathrm{B}, T_1, y, T_2), w, T_3)$, it returns
$N(\mathrm{B}, N(\mathrm{B}, D, k, N(\mathrm{R}, T_1, y, T_2)), w, T_3)$. In every remaining case
it returns $N(c, D, k, S)$.

The repair is meant for a deficient left subtree $D$ whose double black has been absorbed, so
that $D$ has one black node fewer than its sibling $S$ on every root-to-leaf path. -/
def fixLeft {α : Type u} : Color → Tree α → α → Tree α → BBTree α
  | color, left, key, .node .black rl rk (.node .red rrl rrk rrr) =>
      .regular (.node color (.node .black left key rl) rk
        (.node .black rrl rrk rrr))
  | color, left, key, .node .black (.node .red rll rlk rlr) rk rr =>
      .regular (.node color (.node .black left key rll) rlk
        (.node .black rlr rk rr))
  | .red, left, key, .node .black rl rk rr =>
      .regular (.node .black left key (.node .red rl rk rr))
  | .black, left, key, .node .black rl rk rr =>
      .nodeBB left key (.node .red rl rk rr)
  | _, left, key, .node .red (.node .black rll rlk (.node .red rrl rrk rrr)) rk rr =>
      .regular (.node .black
        (.node .red (.node .black left key rll) rlk (.node .black rrl rrk rrr))
        rk rr)
  | _, left, key, .node .red (.node .black (.node .red a y b) rlk rlr) rk rr =>
      .regular (.node .black
        (.node .red (.node .black left key a) y (.node .black b rlk rlr))
        rk rr)
  | _, left, key, .node .red (.node .black rll rlk rlr) rk rr =>
      .regular (.node .black
        (.node .black left key (.node .red rll rlk rlr)) rk rr)
  | color, left, key, right => .regular (.node color left key right)

/-- **Right repair after double-black deletion.** Write $\mathrm{R}$ and $\mathrm{B}$ for red and
black, and $N(c, T, y, T')$ for the node of color $c$ with left subtree $T$, key $y$ and right
subtree $T'$. Given a color $c$, a tree $S$, a key $k$ and a tree $D$, the right repair returns a
tree whose root may be double black, by the first case that applies. If
$S = N(\mathrm{B}, N(\mathrm{R}, T_1, y, T_2), z, T_3)$ or, failing that,
$S = N(\mathrm{B}, T_1, y, N(\mathrm{R}, T_2, z, T_3))$, it returns
$N(c, N(\mathrm{B}, T_1, y, T_2), z, N(\mathrm{B}, T_3, k, D))$. Otherwise, if
$S = N(\mathrm{B}, T_1, y, T_2)$, it returns $N(\mathrm{B}, N(\mathrm{R}, T_1, y, T_2), k, D)$ when
$c$ is red, and the double-black node with left child $N(\mathrm{R}, T_1, y, T_2)$, key $k$ and
right child $D$ when $c$ is black. In the next three cases $c$ is not used. If
$S = N(\mathrm{R}, T_1, y, N(\mathrm{B}, N(\mathrm{R}, T_2, z, T_3), w, T_4))$ or, failing that,
$S = N(\mathrm{R}, T_1, y, N(\mathrm{B}, T_2, z, N(\mathrm{R}, T_3, w, T_4)))$, it returns
$N(\mathrm{B}, T_1, y, N(\mathrm{R}, N(\mathrm{B}, T_2, z, T_3), w, N(\mathrm{B}, T_4, k, D)))$.
Otherwise, if $S = N(\mathrm{R}, T_1, y, N(\mathrm{B}, T_2, z, T_3))$, it returns
$N(\mathrm{B}, T_1, y, N(\mathrm{B}, N(\mathrm{R}, T_2, z, T_3), k, D))$. In every remaining case
it returns $N(c, S, k, D)$.

The repair is the mirror image of the left repair, meant for a deficient right subtree $D$ whose
double black has been absorbed, so that $D$ has one black node fewer than its sibling $S$ on
every root-to-leaf path. -/
def fixRight {α : Type u} : Color → Tree α → α → Tree α → BBTree α
  | color, .node .black (.node .red lrl lrk lrr) lk lr, key, right =>
      .regular (.node color (.node .black lrl lrk lrr) lk
        (.node .black lr key right))
  | color, .node .black ll lk (.node .red lrl lrk lrr), key, right =>
      .regular (.node color (.node .black ll lk lrl) lrk
        (.node .black lrr key right))
  | .red, .node .black ll lk lr, key, right =>
      .regular (.node .black (.node .red ll lk lr) key right)
  | .black, .node .black ll lk lr, key, right =>
      .nodeBB (.node .red ll lk lr) key right
  | _, .node .red ll lk (.node .black (.node .red a y b) mk mr), key, right =>
      .regular (.node .black ll lk
        (.node .red (.node .black a y b) mk (.node .black mr key right)))
  | _, .node .red ll lk (.node .black ml mk (.node .red a y b)), key, right =>
      .regular (.node .black ll lk
        (.node .red (.node .black ml mk a) y (.node .black b key right)))
  | _, .node .red ll lk (.node .black ml mk mr), key, right =>
      .regular (.node .black ll lk
        (.node .black (.node .red ml mk mr) key right))
  | color, left, key, right => .regular (.node color left key right)

/-- **Rebalancing after deletion from the left subtree.** Let $c$ be a color, $L$ a tree whose
root may be double black, $k$ a key and $R$ a red-black tree. If $L$ is a genuine red-black tree,
the result is the genuine node with color $c$, left subtree $L$, key $k$ and right subtree $R$.
Otherwise the double black of $L$ is absorbed first: a double-black empty tree becomes the empty
tree, and a double-black node becomes the black node with the same children and key. The result is
then the left-deficit repair (Fix Left) applied to the color $c$, the absorbed tree, the key $k$
and the sibling $R$; it may again have a double-black root. -/
def balLeft {α : Type u} (color : Color) (left : BBTree α) (key : α)
    (right : Tree α) : BBTree α :=
  match left with
  | .regular tree => .regular (.node color tree key right)
  | .emptyBB => fixLeft color .empty key right
  | .nodeBB l k r => fixLeft color (.node .black l k r) key right

/-- **Rebalancing after deletion from the right subtree.** Let $c$ be a color, $L$ a red-black
tree, $k$ a key and $R$ a tree whose root may be double black. If $R$ is a genuine red-black
tree, the result is the genuine node with color $c$, left subtree $L$, key $k$ and right subtree
$R$. Otherwise the double black of $R$ is absorbed first: a double-black empty tree becomes the
empty tree, and a double-black node becomes the black node with the same children and key. The
result is then the right-deficit repair (Fix Right) applied to the color $c$, the sibling $L$, the
key $k$ and the absorbed tree; it may again have a double-black root. -/
def balRight {α : Type u} (color : Color) (left : Tree α) (key : α)
    (right : BBTree α) : BBTree α :=
  match right with
  | .regular tree => .regular (.node color left key tree)
  | .emptyBB => fixRight color left key .empty
  | .nodeBB l k r => fixRight color left key (.node .black l k r)

/-- **Double-black deletion.** For a key $x$ of a linearly ordered type, deleting $x$ from a
red-black tree returns a tree whose root may be double black, by recursion on the tree. The
empty tree gives the empty tree. At a node of color $c$ with left subtree $l$, key $k$ and right
subtree $r$: if $x < k$, the result is the left reassembly of color $c$, the deletion of $x$
from $l$, key $k$ and $r$; if $k < x$, it is the right reassembly of color $c$, $l$, key $k$ and
the deletion of $x$ from $r$. A reassembly rebuilds the node when the recursive result is a
genuine tree, and otherwise repairs the double-black child against its sibling. If $x = k$ and
$l$ is empty, the result is $r$ when $c$ is red and $r$ with one black added at its root when
$c$ is black; otherwise, if $r$ is empty, the same with $l$ in place of $r$. If $x = k$ and both
subtrees are nonempty, let $s$ be the leftmost key of $r$; the result is the right reassembly of
color $c$, $l$, key $s$ and the deletion of $s$ from $r$. Thus a node with two children is
deleted by promoting its successor, the minimum key of its right subtree. -/
def del {α : Type u} [LinearOrder α] (x : α) : Tree α → BBTree α
  | .empty => .regular .empty
  | .node color left key right =>
      if x < key then balLeft color (del x left) key right
      else if key < x then balRight color left key (del x right)
      else match left, right with
        | .empty, _ =>
            match color with
            | .red => .regular right
            | .black => incrBlack right
        | _, .empty =>
            match color with
            | .red => .regular left
            | .black => incrBlack left
        | _, _ =>
            match minKey right with
            | some s => balRight color left s (del s right)
            | none => .regular left

/-- **Red-black tree deletion by the double-black method.** For a key $x$ of a linearly ordered
type and a red-black tree $t$, deleting $x$ from $t$ runs the double-black deletion of $x$ from
$t$, which returns a tree whose root may be double black, and then absorbs a remaining double
black at the root and recolors the root black.

When $t$ is ordered, has no red node with a red child and has the same number of black nodes on
every root-to-leaf path, the result is a valid red-black tree; when $t$ is only ordered, the
inorder traversal of the result is that of $t$ with $x$ erased. -/
public def deleteBal {α : Type u} [LinearOrder α] (x : α) (tree : Tree α) :
    Tree α :=
  blacken (del x tree)

@[simp] public theorem inorderBB_regular {α : Type u} {tree : Tree α} :
    inorderBB (.regular tree) = inorder tree :=
  rfl

@[simp] public theorem inorderBB_emptyBB {α : Type u} :
    inorderBB (.emptyBB : BBTree α) = [] :=
  rfl

@[simp] public theorem inorderBB_nodeBB {α : Type u} {left right : Tree α}
    {key : α} :
    inorderBB (.nodeBB left key right) = inorder left ++ key :: inorder right :=
  rfl

@[simp] public theorem bhBB_regular {α : Type u} {tree : Tree α} :
    bhBB (.regular tree) = blackHeight tree :=
  rfl

@[simp] public theorem bhBB_emptyBB {α : Type u} :
    bhBB (.emptyBB : BBTree α) = 2 :=
  rfl

@[simp] public theorem bhBB_nodeBB {α : Type u} {left right : Tree α}
    {key : α} :
    bhBB (.nodeBB left key right) = blackHeight left + 2 :=
  rfl

@[simp] public theorem balancedBB_regular {α : Type u} {tree : Tree α} :
    BalancedBB (.regular tree) = Balanced tree :=
  rfl

@[simp] public theorem balancedBB_emptyBB {α : Type u} :
    BalancedBB (.emptyBB : BBTree α) = True :=
  rfl

@[simp] public theorem balancedBB_nodeBB {α : Type u} {left right : Tree α}
    {key : α} :
    BalancedBB (.nodeBB left key right) =
      (Balanced left ∧ Balanced right ∧ blackHeight left = blackHeight right) :=
  rfl

@[simp] public theorem redOkBB_regular {α : Type u} {tree : Tree α} :
    RedOkBB (.regular tree) = RedOk tree :=
  rfl

@[simp] public theorem redOkBB_emptyBB {α : Type u} :
    RedOkBB (.emptyBB : BBTree α) = True :=
  rfl

@[simp] public theorem redOkBB_nodeBB {α : Type u} {left right : Tree α}
    {key : α} :
    RedOkBB (.nodeBB left key right) = (RedOk left ∧ RedOk right) :=
  rfl

@[simp] public theorem colorBB_emptyBB {α : Type u} :
    colorBB (.emptyBB : BBTree α) = .doubleBlack :=
  rfl

@[simp] public theorem colorBB_nodeBB {α : Type u} {left right : Tree α}
    {key : α} :
    colorBB (.nodeBB left key right) = .doubleBlack :=
  rfl

@[simp] public theorem colorBB_regular_empty {α : Type u} :
    colorBB (.regular (.empty : Tree α)) = .black :=
  rfl

@[simp] public theorem colorBB_regular_red {α : Type u}
    {left right : Tree α} {key : α} :
    colorBB (.regular (.node .red left key right)) = .red :=
  rfl

@[simp] public theorem colorBB_regular_black {α : Type u}
    {left right : Tree α} {key : α} :
    colorBB (.regular (.node .black left key right)) = .black :=
  rfl

@[simp] public theorem rootBlack_empty {α : Type u} :
    rootBlack (.empty : Tree α) = .empty :=
  rfl

@[simp] public theorem rootBlack_node {α : Type u} {color : Color}
    {left right : Tree α} {key : α} :
    rootBlack (.node color left key right) = .node .black left key right :=
  rfl

@[simp] public theorem blacken_regular {α : Type u} {tree : Tree α} :
    blacken (.regular tree) = rootBlack tree :=
  rfl

@[simp] public theorem blacken_emptyBB {α : Type u} :
    blacken (.emptyBB : BBTree α) = .empty :=
  rfl

@[simp] public theorem blacken_nodeBB {α : Type u} {left right : Tree α}
    {key : α} :
    blacken (.nodeBB left key right) = .node .black left key right :=
  rfl

@[simp] public theorem incrBlack_empty {α : Type u} :
    incrBlack (.empty : Tree α) = .emptyBB :=
  rfl

@[simp] public theorem incrBlack_node_red {α : Type u}
    {left right : Tree α} {key : α} :
    incrBlack (.node .red left key right) =
      .regular (.node .black left key right) :=
  rfl

@[simp] public theorem incrBlack_node_black {α : Type u}
    {left right : Tree α} {key : α} :
    incrBlack (.node .black left key right) = .nodeBB left key right :=
  rfl

private theorem blackHeight_pos {α : Type u} (tree : Tree α) :
    1 ≤ blackHeight tree := by
  induction tree with
  | empty => simp [blackHeight]
  | node color left _ _ ihLeft _ =>
      cases color <;> simp [blackHeight, ihLeft]

public theorem colorBB_regular_ne_red {α : Type u} {tree : Tree α} :
    colorBB (.regular tree) ≠ .red ↔ colorOf tree = .black := by
  cases tree with
  | empty => simp [colorBB, colorOf]
  | node color _ _ _ => cases color <;> simp [colorBB, colorOf]

public theorem colorBB_regular_eq_red {α : Type u} {tree : Tree α} :
    colorBB (.regular tree) = .red ↔ colorOf tree = .red := by
  cases tree with
  | empty => simp [colorBB, colorOf]
  | node color _ _ _ => cases color <;> simp [colorBB, colorOf]

public theorem inorder_rootBlack {α : Type u} {tree : Tree α} :
    inorder (rootBlack tree) = inorder tree := by
  cases tree <;> simp [rootBlack]

public theorem inorder_blacken {α : Type u} {tree : BBTree α} :
    inorder (blacken tree) = inorderBB tree := by
  cases tree <;> simp [blacken, inorder_rootBlack]

public theorem balanced_rootBlack {α : Type u} {tree : Tree α}
    (h : Balanced tree) : Balanced (rootBlack tree) := by
  cases tree <;> exact h

public theorem balanced_blacken {α : Type u} {tree : BBTree α}
    (h : BalancedBB tree) : Balanced (blacken tree) := by
  cases tree with
  | regular tree => exact balanced_rootBlack h
  | emptyBB => trivial
  | nodeBB _ _ _ => exact h

public theorem redOk_rootBlack {α : Type u} {tree : Tree α} (h : RedOk tree) :
    RedOk (rootBlack tree) := by
  cases tree with
  | empty => exact h
  | node color _ _ _ =>
      cases color with
      | red => exact ⟨h.1, h.2.1⟩
      | black => exact h

public theorem redOk_blacken {α : Type u} {tree : BBTree α}
    (h : RedOkBB tree) : RedOk (blacken tree) := by
  cases tree with
  | regular tree => exact redOk_rootBlack h
  | emptyBB => trivial
  | nodeBB _ _ _ => exact h

public theorem colorOf_blacken {α : Type u} {tree : BBTree α} :
    colorOf (blacken tree) = .black := by
  cases tree with
  | regular tree => cases tree <;> rfl
  | emptyBB => rfl
  | nodeBB _ _ _ => rfl

public theorem inorderBB_incrBlack {α : Type u} {tree : Tree α} :
    inorderBB (incrBlack tree) = inorder tree := by
  cases tree with
  | empty => rfl
  | node color _ _ _ => cases color <;> simp [incrBlack]

public theorem bhBB_incrBlack {α : Type u} {tree : Tree α} :
    bhBB (incrBlack tree) = blackHeight tree + 1 := by
  cases tree with
  | empty => rfl
  | node color _ _ _ => cases color <;> rfl

public theorem balancedBB_incrBlack {α : Type u} {tree : Tree α}
    (h : Balanced tree) : BalancedBB (incrBlack tree) := by
  cases tree with
  | empty => trivial
  | node color _ _ _ => cases color <;> exact h

public theorem redOkBB_incrBlack {α : Type u} {tree : Tree α}
    (h : RedOk tree) : RedOkBB (incrBlack tree) := by
  cases tree with
  | empty => trivial
  | node color _ _ _ =>
      cases color with
      | red => exact ⟨h.1, h.2.1⟩
      | black => exact h

public theorem colorBB_incrBlack_ne_red {α : Type u} {tree : Tree α} :
    colorBB (incrBlack tree) ≠ .red := by
  cases tree with
  | empty => simp [incrBlack, colorBB]
  | node color _ _ _ => cases color <;> simp [incrBlack, colorBB, colorOf]

private theorem inorder_fixLeft {α : Type u} (color : Color) (left : Tree α)
    (key : α) (right : Tree α) :
    inorderBB (fixLeft color left key right) =
      inorder left ++ key :: inorder right := by
  cases color <;> cases right with
  | empty => simp [fixLeft]
  | node cr rl rk rr =>
      cases cr with
      | black =>
          cases rl <;> cases rr <;> (try cases ‹Color›) <;> (try cases ‹Color›) <;>
            simp [fixLeft, List.append_assoc]
      | red =>
          cases rl with
          | empty => simp [fixLeft]
          | node cl rll rlk rlr =>
              cases cl <;> cases rll <;> cases rlr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp [fixLeft, List.append_assoc]

private theorem inorder_fixRight {α : Type u} (color : Color) (left : Tree α)
    (key : α) (right : Tree α) :
    inorderBB (fixRight color left key right) =
      inorder left ++ key :: inorder right := by
  cases color <;> cases left with
  | empty => simp [fixRight]
  | node cl ll lk lr =>
      cases cl with
      | black =>
          cases ll <;> cases lr <;> (try cases ‹Color›) <;> (try cases ‹Color›) <;>
            simp [fixRight, List.append_assoc]
      | red =>
          cases lr with
          | empty => simp [fixRight]
          | node cl2 ml mk mr =>
              cases cl2 <;> cases ml <;> cases mr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp [fixRight, List.append_assoc]

private theorem bhBB_fixLeft {α : Type u} {color : Color} {left right : Tree α}
    {key : α} (hBh : blackHeight left + 1 = blackHeight right)
    (hRedR : RedOk right) (hCol : color = .red → colorOf right = .black) :
    bhBB (fixLeft color left key right) =
      blackHeight (.node color left key right) + 1 := by
  have hpos : 1 ≤ blackHeight left := blackHeight_pos left
  cases color with
  | red =>
      have hr : colorOf right = .black := hCol rfl
      cases right with
      | empty => simp [blackHeight] at hBh; omega
      | node cr rl rk rr =>
          cases cr with
          | red => simp [colorOf] at hr
          | black =>
              cases rl <;> cases rr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp [fixLeft, blackHeight]
  | black =>
      cases right with
      | empty => simp [blackHeight] at hBh; omega
      | node cr rl rk rr =>
          cases cr with
          | black =>
              cases rl <;> cases rr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp [fixLeft, blackHeight]
          | red =>
              cases rl with
              | empty => simp [blackHeight] at hBh; omega
              | node cl rll rlk rlr =>
                  cases cl <;> cases rll <;> cases rlr <;> (try cases ‹Color›) <;>
                    (try cases ‹Color›) <;>
                    simp_all [fixLeft, blackHeight, RedOk, colorOf]

private theorem bhBB_fixRight {α : Type u} {color : Color} {left right : Tree α}
    {key : α} (hRedL : RedOk left)
    (hCol : color = .red → colorOf left = .black) :
    bhBB (fixRight color left key right) =
      blackHeight (.node color left key right) := by
  cases color with
  | red =>
      have hl : colorOf left = .black := hCol rfl
      cases left with
      | empty => simp [fixRight, blackHeight]
      | node cl ll lk lr =>
          cases cl with
          | red => simp [colorOf] at hl
          | black =>
              cases ll <;> cases lr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp [fixRight, blackHeight]
  | black =>
      cases left with
      | empty => simp [fixRight, blackHeight]
      | node cl ll lk lr =>
          cases cl with
          | black =>
              cases ll <;> cases lr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp [fixRight, blackHeight]
          | red =>
              cases lr with
              | empty => simp [fixRight, blackHeight]
              | node cl2 ml mk mr =>
                  cases cl2 <;> cases ml <;> cases mr <;> (try cases ‹Color›) <;>
                    (try cases ‹Color›) <;>
                    simp_all [fixRight, blackHeight, RedOk, colorOf]

private theorem balanced_fixLeft {α : Type u} {color : Color}
    {left right : Tree α} {key : α} (hBalL : Balanced left)
    (hBalR : Balanced right) (hBh : blackHeight left + 1 = blackHeight right)
    (hRedR : RedOk right) : BalancedBB (fixLeft color left key right) := by
  have hpos : 1 ≤ blackHeight left := blackHeight_pos left
  cases color <;> cases right with
  | empty => simp_all [fixLeft, Balanced, blackHeight]
  | node cr rl rk rr =>
      cases cr with
      | black =>
          cases rl <;> cases rr <;> (try cases ‹Color›) <;> (try cases ‹Color›) <;>
            simp_all [fixLeft, Balanced, blackHeight] <;> omega
      | red =>
          cases rl with
          | empty => simp_all [fixLeft, Balanced, blackHeight]
          | node cl rll rlk rlr =>
              cases cl <;> cases rll <;> cases rlr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;>
                simp_all [fixLeft, Balanced, blackHeight, RedOk, colorOf] <;> omega

private theorem balanced_fixRight {α : Type u} {color : Color}
    {left right : Tree α} {key : α} (hBalL : Balanced left)
    (hBalR : Balanced right) (hBh : blackHeight right + 1 = blackHeight left)
    (hRedL : RedOk left) : BalancedBB (fixRight color left key right) := by
  have hpos : 1 ≤ blackHeight right := blackHeight_pos right
  cases color <;> cases left with
  | empty => simp_all [fixRight, Balanced, blackHeight]
  | node cl ll lk lr =>
      cases cl with
      | black =>
          cases ll <;> cases lr <;> (try cases ‹Color›) <;> (try cases ‹Color›) <;>
            simp_all [fixRight, Balanced, blackHeight] <;> omega
      | red =>
          cases lr with
          | empty => simp_all [fixRight, Balanced, blackHeight]
          | node cl2 ml mk mr =>
              cases cl2 <;> cases ml <;> cases mr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;>
                simp_all [fixRight, Balanced, blackHeight, RedOk, colorOf] <;> omega

private theorem redOk_fixLeft {α : Type u} {color : Color} {left right : Tree α}
    {key : α} (hRedL : RedOk left) (hRedR : RedOk right)
    (hColL : colorOf left = .black)
    (hCol : color = .red → colorOf right = .black) :
    RedOkBB (fixLeft color left key right) := by
  cases color with
  | red =>
      have hr : colorOf right = .black := hCol rfl
      cases right with
      | empty => simp_all [fixLeft, RedOk, colorOf]
      | node cr rl rk rr =>
          cases cr with
          | red => simp [colorOf] at hr
          | black =>
              cases rl <;> cases rr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp_all [fixLeft, RedOk, colorOf]
  | black =>
      cases right with
      | empty => simp_all [fixLeft, RedOk, colorOf]
      | node cr rl rk rr =>
          cases cr with
          | black =>
              cases rl <;> cases rr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp_all [fixLeft, RedOk, colorOf]
          | red =>
              cases rl with
              | empty => simp_all [fixLeft, RedOk, colorOf]
              | node cl rll rlk rlr =>
                  cases cl <;> cases rll <;> cases rlr <;> (try cases ‹Color›) <;>
                    (try cases ‹Color›) <;> simp_all [fixLeft, RedOk, colorOf]

private theorem redOk_fixRight {α : Type u} {color : Color} {left right : Tree α}
    {key : α} (hRedL : RedOk left) (hRedR : RedOk right)
    (hColR : colorOf right = .black)
    (hCol : color = .red → colorOf left = .black) :
    RedOkBB (fixRight color left key right) := by
  cases color with
  | red =>
      have hl : colorOf left = .black := hCol rfl
      cases left with
      | empty => simp_all [fixRight, RedOk, colorOf]
      | node cl ll lk lr =>
          cases cl with
          | red => simp [colorOf] at hl
          | black =>
              cases ll <;> cases lr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp_all [fixRight, RedOk, colorOf]
  | black =>
      cases left with
      | empty => simp_all [fixRight, RedOk, colorOf]
      | node cl ll lk lr =>
          cases cl with
          | black =>
              cases ll <;> cases lr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp_all [fixRight, RedOk, colorOf]
          | red =>
              cases lr with
              | empty => simp_all [fixRight, RedOk, colorOf]
              | node cl2 ml mk mr =>
                  cases cl2 <;> cases ml <;> cases mr <;> (try cases ‹Color›) <;>
                    (try cases ‹Color›) <;> simp_all [fixRight, RedOk, colorOf]

private theorem colorBB_fixLeft_ne_red {α : Type u} {color : Color}
    {left right : Tree α} {key : α} (hc : color = .black) :
    colorBB (fixLeft color left key right) ≠ .red := by
  rw [hc]
  cases right with
  | empty => simp [fixLeft, colorBB, colorOf]
  | node cr rl rk rr =>
      cases cr with
      | black =>
          cases rl <;> cases rr <;> (try cases ‹Color›) <;> (try cases ‹Color›) <;>
            simp [fixLeft, colorBB, colorOf]
      | red =>
          cases rl with
          | empty => simp [fixLeft, colorBB, colorOf]
          | node cl rll rlk rlr =>
              cases cl <;> cases rll <;> cases rlr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp [fixLeft, colorBB, colorOf]

private theorem colorBB_fixRight_ne_red {α : Type u} {color : Color}
    {left right : Tree α} {key : α} (hc : color = .black) :
    colorBB (fixRight color left key right) ≠ .red := by
  rw [hc]
  cases left with
  | empty => simp [fixRight, colorBB, colorOf]
  | node cl ll lk lr =>
      cases cl with
      | black =>
          cases ll <;> cases lr <;> (try cases ‹Color›) <;> (try cases ‹Color›) <;>
            simp [fixRight, colorBB, colorOf]
      | red =>
          cases lr with
          | empty => simp [fixRight, colorBB, colorOf]
          | node cl2 ml mk mr =>
              cases cl2 <;> cases ml <;> cases mr <;> (try cases ‹Color›) <;>
                (try cases ‹Color›) <;> simp [fixRight, colorBB, colorOf]

private theorem inorder_balLeft {α : Type u} {color : Color} {left : BBTree α}
    {key : α} {right : Tree α} :
    inorderBB (balLeft color left key right) =
      inorderBB left ++ key :: inorder right := by
  cases left <;> simp [balLeft, inorder_fixLeft]

private theorem bhBB_balLeft {α : Type u} {color : Color} {left : BBTree α}
    {key : α} {right : Tree α} (hBh : bhBB left = blackHeight right)
    (hRedR : RedOk right)
    (hCol : color = .red → colorOf right = .black) :
    (color = .red → bhBB (balLeft color left key right) = bhBB left) ∧
      (color = .black → bhBB (balLeft color left key right) = bhBB left + 1) := by
  constructor <;> intro hc <;> cases left with
  | regular tree => rw [hc]; simp [balLeft, blackHeight]
  | emptyBB =>
      have hBh' : blackHeight (.empty : Tree α) + 1 = blackHeight right := by
        have h1 : blackHeight (.empty : Tree α) = 1 := rfl
        have h2 : bhBB (.emptyBB : BBTree α) = 2 := rfl
        omega
      have hfix := bhBB_fixLeft hBh' hRedR hCol (key := key)
      show bhBB (fixLeft color .empty key right) = _
      rw [hfix, hc]; simp [blackHeight]
  | nodeBB l k r =>
      have hBh' : blackHeight (.node .black l k r) + 1 = blackHeight right := by
        have h1 : blackHeight (.node .black l k r) = blackHeight l + 1 := rfl
        have h2 : bhBB (.nodeBB l k r) = blackHeight l + 2 := rfl
        omega
      have hfix := bhBB_fixLeft hBh' hRedR hCol (key := key)
      show bhBB (fixLeft color (.node .black l k r) key right) = _
      rw [hfix, hc]; simp [blackHeight]

private theorem balanced_balLeft {α : Type u} {color : Color} {left : BBTree α}
    {key : α} {right : Tree α} (hBalL : BalancedBB left)
    (hBalR : Balanced right) (hBh : bhBB left = blackHeight right)
    (hRedR : RedOk right) : BalancedBB (balLeft color left key right) := by
  cases left with
  | regular tree =>
      show Balanced (.node color tree key right)
      exact ⟨hBalL, hBalR, hBh⟩
  | emptyBB =>
      have hBh' : blackHeight (.empty : Tree α) + 1 = blackHeight right := by
        have h1 : blackHeight (.empty : Tree α) = 1 := rfl
        have h2 : bhBB (.emptyBB : BBTree α) = 2 := rfl
        omega
      exact balanced_fixLeft trivial hBalR hBh' hRedR
  | nodeBB l k r =>
      have hBh' : blackHeight (.node .black l k r) + 1 = blackHeight right := by
        have h1 : blackHeight (.node .black l k r) = blackHeight l + 1 := rfl
        have h2 : bhBB (.nodeBB l k r) = blackHeight l + 2 := rfl
        omega
      exact balanced_fixLeft hBalL hBalR hBh' hRedR

private theorem redOk_balLeft {α : Type u} {color : Color} {left : BBTree α}
    {key : α} {right : Tree α} (hRedL : RedOkBB left) (hRedR : RedOk right)
    (hCol : color = .red → colorBB left ≠ .red ∧ colorOf right = .black) :
    RedOkBB (balLeft color left key right) := by
  cases left with
  | regular tree =>
      cases color with
      | black =>
          show RedOk (.node .black tree key right)
          exact ⟨hRedL, hRedR⟩
      | red =>
          show RedOk (.node .red tree key right)
          exact ⟨hRedL, hRedR, colorBB_regular_ne_red.mp (hCol rfl).1,
            (hCol rfl).2⟩
  | emptyBB =>
      exact redOk_fixLeft trivial hRedR rfl (fun h => (hCol h).2)
  | nodeBB l k r =>
      exact redOk_fixLeft hRedL hRedR rfl (fun h => (hCol h).2)

private theorem colorBB_balLeft_ne_red {α : Type u} {color : Color}
    {left : BBTree α} {key : α} {right : Tree α} (hc : color = .black) :
    colorBB (balLeft color left key right) ≠ .red := by
  cases left with
  | regular tree => rw [hc]; simp [balLeft, colorBB, colorOf]
  | emptyBB => exact colorBB_fixLeft_ne_red hc
  | nodeBB _ _ _ => exact colorBB_fixLeft_ne_red hc

private theorem inorder_balRight {α : Type u} {color : Color} {left : Tree α}
    {key : α} {right : BBTree α} :
    inorderBB (balRight color left key right) =
      inorder left ++ key :: inorderBB right := by
  cases right <;> simp [balRight, inorder_fixRight]

private theorem bhBB_balRight {α : Type u} {color : Color} {left : Tree α}
    {key : α} {right : BBTree α} (hBh : blackHeight left = bhBB right)
    (hRedL : RedOk left)
    (hCol : color = .red → colorOf left = .black) :
    (color = .red → bhBB (balRight color left key right) = bhBB right) ∧
      (color = .black → bhBB (balRight color left key right) = bhBB right + 1) := by
  constructor <;> intro hc <;> cases right with
  | regular tree =>
      have e3 : bhBB (.regular tree) = blackHeight tree := rfl
      rw [hc]; simp [balRight, blackHeight]; omega
  | emptyBB =>
      have hfix := bhBB_fixRight hRedL hCol (key := key) (right := .empty)
      have e3 : bhBB (.emptyBB : BBTree α) = 2 := rfl
      show bhBB (fixRight color left key .empty) = _
      rw [hfix, hc]; simp [blackHeight]; omega
  | nodeBB l k r =>
      have hfix := bhBB_fixRight hRedL hCol (key := key)
        (right := .node .black l k r)
      have e3 : bhBB (.nodeBB l k r) = blackHeight l + 2 := rfl
      have e4 : blackHeight (.node .black l k r) = blackHeight l + 1 := rfl
      show bhBB (fixRight color left key (.node .black l k r)) = _
      rw [hfix, hc]; simp [blackHeight]; omega

private theorem balanced_balRight {α : Type u} {color : Color} {left : Tree α}
    {key : α} {right : BBTree α} (hBalL : Balanced left)
    (hBalR : BalancedBB right) (hBh : blackHeight left = bhBB right)
    (hRedL : RedOk left) : BalancedBB (balRight color left key right) := by
  cases right with
  | regular tree =>
      show Balanced (.node color left key tree)
      exact ⟨hBalL, hBalR, hBh⟩
  | emptyBB =>
      have hBh' : blackHeight (.empty : Tree α) + 1 = blackHeight left := by
        have h1 : blackHeight (.empty : Tree α) = 1 := rfl
        have h2 : bhBB (.emptyBB : BBTree α) = 2 := rfl
        omega
      exact balanced_fixRight hBalL trivial hBh' hRedL
  | nodeBB l k r =>
      have hBh' : blackHeight (.node .black l k r) + 1 = blackHeight left := by
        have h1 : blackHeight (.node .black l k r) = blackHeight l + 1 := rfl
        have h2 : bhBB (.nodeBB l k r) = blackHeight l + 2 := rfl
        omega
      exact balanced_fixRight hBalL hBalR hBh' hRedL

private theorem redOk_balRight {α : Type u} {color : Color} {left : Tree α}
    {key : α} {right : BBTree α} (hRedL : RedOk left) (hRedR : RedOkBB right)
    (hCol : color = .red → colorOf left = .black ∧ colorBB right ≠ .red) :
    RedOkBB (balRight color left key right) := by
  cases right with
  | regular tree =>
      cases color with
      | black =>
          show RedOk (.node .black left key tree)
          exact ⟨hRedL, hRedR⟩
      | red =>
          show RedOk (.node .red left key tree)
          exact ⟨hRedL, hRedR, (hCol rfl).1,
            colorBB_regular_ne_red.mp (hCol rfl).2⟩
  | emptyBB =>
      exact redOk_fixRight hRedL trivial rfl (fun h => (hCol h).1)
  | nodeBB l k r =>
      exact redOk_fixRight hRedL hRedR rfl (fun h => (hCol h).1)

private theorem colorBB_balRight_ne_red {α : Type u} {color : Color}
    {left : Tree α} {key : α} {right : BBTree α} (hc : color = .black) :
    colorBB (balRight color left key right) ≠ .red := by
  cases right with
  | regular tree => rw [hc]; simp [balRight, colorBB, colorOf]
  | emptyBB => exact colorBB_fixRight_ne_red hc
  | nodeBB _ _ _ => exact colorBB_fixRight_ne_red hc

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

private theorem minKey_eq_none {α : Type u} {tree : Tree α} :
    minKey tree = none ↔ tree = .empty := by
  cases tree with
  | empty => simp [minKey]
  | node _ l _ _ => cases hl : minKey l <;> simp [minKey, hl]

private theorem inorder_eq_cons_of_minKey {α : Type u} {tree : Tree α} {s : α}
    (h : minKey tree = some s) : ∃ rest, inorder tree = s :: rest := by
  induction tree with
  | empty => simp [minKey] at h
  | node _ l k r ihL _ =>
      cases hl : minKey l with
      | some s' =>
          have hs : s' = s := by simpa [minKey, hl] using h
          subst hs
          obtain ⟨rest, hrest⟩ := ihL hl
          exact ⟨rest ++ k :: inorder r, by rw [inorder_node, hrest]; rfl⟩
      | none =>
          have hlE : l = .empty := minKey_eq_none.mp hl
          subst hlE
          have hs : k = s := by simpa [minKey] using h
          exact ⟨inorder r, by rw [inorder_node, hs]; simp⟩

private theorem del_spec {α : Type u} [LinearOrder α] (tree : Tree α) :
    Ordered tree → Balanced tree → RedOk tree → ∀ (x : α),
    inorderBB (del x tree) = (inorder tree).erase x ∧
      BalancedBB (del x tree) ∧ bhBB (del x tree) = blackHeight tree ∧
      RedOkBB (del x tree) ∧
      (colorOf tree = .black → colorBB (del x tree) ≠ .red) := by
  induction tree with
  | empty =>
      intro _ _ _ x
      refine ⟨by simp [del], trivial, rfl, trivial, fun _ => ?_⟩
      simp [del, colorBB, colorOf]
  | node color left key right ihL ihR =>
      intro hOrd hBal hRed x
      rcases hOrd with ⟨hOrdL, hOrdR, hAllL, hAllR⟩
      rcases hBal with ⟨hBalL, hBalR, hBhEq⟩
      have hRedL : RedOk left := by
        cases color with
        | red => exact hRed.1
        | black => exact hRed.1
      have hRedR : RedOk right := by
        cases color with
        | red => exact hRed.2.1
        | black => exact hRed.2
      have hColL : color = .red → colorOf left = .black := by
        intro hc
        subst hc
        exact hRed.2.2.1
      have hColR : color = .red → colorOf right = .black := by
        intro hc
        subst hc
        exact hRed.2.2.2
      by_cases hlt : x < key
      · obtain ⟨ihIn, ihBal, ihBh, ihRed, ihCol⟩ := ihL hOrdL hBalL hRedL x
        have hdelEq : del x (.node color left key right) =
            balLeft color (del x left) key right := by
          simp [del, hlt]
        have hnot : x ∉ key :: inorder right := by
          intro hx
          rw [List.mem_cons] at hx
          rcases hx with hx | hx
          · exact ne_of_lt hlt hx
          · rw [mem_inorder] at hx
            exact lt_asymm hlt ((all_iff_forall_mem.mp hAllR) x hx)
        have hb := bhBB_balLeft (ihBh.trans hBhEq) hRedR hColR
          (key := key) (left := del x left)
        rw [hdelEq]
        refine ⟨?_, balanced_balLeft ihBal hBalR (ihBh.trans hBhEq) hRedR, ?_,
          redOk_balLeft ihRed hRedR (fun hc => ⟨ihCol (hColL hc), hColR hc⟩),
          fun hroot => colorBB_balLeft_ne_red hroot⟩
        · rw [inorder_balLeft, ihIn, inorder_node]
          exact (erase_append_of_not_mem_right hnot).symm
        · cases color with
          | red =>
              have e : blackHeight (.node .red left key right) =
                  blackHeight left := rfl
              rw [e, hb.1 rfl, ihBh]
          | black =>
              have e : blackHeight (.node .black left key right) =
                  blackHeight left + 1 := rfl
              rw [e, hb.2 rfl, ihBh]
      · by_cases hgt : key < x
        · obtain ⟨ihIn, ihBal, ihBh, ihRed, ihCol⟩ := ihR hOrdR hBalR hRedR x
          have hdelEq : del x (.node color left key right) =
              balRight color left key (del x right) := by
            simp [del, hlt, hgt]
          have hxL : x ∉ inorder left := by
            rw [mem_inorder]
            intro hx
            exact lt_asymm hgt ((all_iff_forall_mem.mp hAllL) x hx)
          have hb := bhBB_balRight (hBhEq.trans ihBh.symm) hRedL hColL
            (key := key) (right := del x right)
          rw [hdelEq]
          refine ⟨?_, balanced_balRight hBalL ihBal (hBhEq.trans ihBh.symm) hRedL, ?_,
            redOk_balRight hRedL ihRed (fun hc => ⟨hColL hc, ihCol (hColR hc)⟩),
            fun hroot => colorBB_balRight_ne_red hroot⟩
          · rw [inorder_balRight, ihIn, inorder_node,
              erase_append_of_not_mem_left hxL,
              erase_cons_tail_of_ne (ne_of_lt hgt)]
          · cases color with
            | red =>
                have e : blackHeight (.node .red left key right) =
                    blackHeight left := rfl
                rw [e, hb.1 rfl, ihBh, hBhEq]
            | black =>
                have e : blackHeight (.node .black left key right) =
                    blackHeight left + 1 := rfl
                rw [e, hb.2 rfl, ihBh, hBhEq]
        · have hxEq : key = x :=
            (le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)).symm
          subst hxEq
          cases left with
          | empty =>
              cases color with
              | red =>
                  have hdelEq : del key (.node .red .empty key right) =
                      .regular right := by
                    simp [del]
                  rw [hdelEq]
                  refine ⟨?_, hBalR, hBhEq.symm, hRedR, fun hroot => ?_⟩
                  · rw [inorderBB_regular, inorder_node]
                    simp [List.erase_cons_head]
                  · simp [colorOf] at hroot
              | black =>
                  have hdelEq : del key (.node .black .empty key right) =
                      incrBlack right := by
                    simp [del]
                  rw [hdelEq]
                  refine ⟨?_, balancedBB_incrBlack hBalR, ?_,
                    redOkBB_incrBlack hRedR, fun _ => colorBB_incrBlack_ne_red⟩
                  · rw [inorderBB_incrBlack, inorder_node]
                    simp [List.erase_cons_head]
                  · rw [bhBB_incrBlack,
                      show blackHeight (.node .black .empty key right) =
                        blackHeight .empty + 1 from rfl, hBhEq]
          | node cl ll lk lr =>
              have hkL : key ∉ inorder (.node cl ll lk lr) := by
                rw [mem_inorder]
                intro hx
                exact lt_irrefl key ((all_iff_forall_mem.mp hAllL) key hx)
              cases right with
              | empty =>
                  cases color with
                  | red =>
                      have hdelEq : del key (.node .red (.node cl ll lk lr) key .empty) =
                          .regular (.node cl ll lk lr) := by
                        simp [del]
                      have hnode : inorder (.node .red (.node cl ll lk lr) key .empty) =
                          inorder (.node cl ll lk lr) ++ key ::
                            inorder (.empty : Tree α) :=
                        inorder_node _ _ _
                      rw [hdelEq]
                      refine ⟨?_, hBalL, rfl, hRedL, fun hroot => ?_⟩
                      · rw [inorderBB_regular, hnode, inorder_empty,
                          erase_append_of_not_mem_left hkL]
                        simp [List.erase_cons_head]
                      · simp [colorOf] at hroot
                  | black =>
                      have hdelEq : del key (.node .black (.node cl ll lk lr) key .empty) =
                          incrBlack (.node cl ll lk lr) := by
                        simp [del]
                      have hnode : inorder (.node .black (.node cl ll lk lr) key .empty) =
                          inorder (.node cl ll lk lr) ++ key ::
                            inorder (.empty : Tree α) :=
                        inorder_node _ _ _
                      rw [hdelEq]
                      refine ⟨?_, balancedBB_incrBlack hBalL, ?_,
                        redOkBB_incrBlack hRedL, fun _ => colorBB_incrBlack_ne_red⟩
                      · rw [inorderBB_incrBlack, hnode, inorder_empty,
                          erase_append_of_not_mem_left hkL]
                        simp [List.erase_cons_head]
                      · have e : blackHeight
                            (.node .black (.node cl ll lk lr) key .empty) =
                            blackHeight (.node cl ll lk lr) + 1 := rfl
                        rw [bhBB_incrBlack, e]
              | node cr rl rk rr =>
                  obtain ⟨s, hs⟩ : ∃ s, minKey (.node cr rl rk rr : Tree α) = some s := by
                    cases hmk : minKey (.node cr rl rk rr : Tree α) with
                    | none =>
                        have hcontra := minKey_eq_none.mp hmk
                        simp at hcontra
                    | some s => exact ⟨s, rfl⟩
                  have hdelEq : del key
                      (.node color (.node cl ll lk lr) key (.node cr rl rk rr)) =
                      balRight color (.node cl ll lk lr) s
                        (del s (.node cr rl rk rr)) := by
                    simp [del, hs]
                  obtain ⟨ihIn, ihBal, ihBh, ihRed, ihCol⟩ :=
                    ihR hOrdR hBalR hRedR s
                  obtain ⟨rest, hrest⟩ := inorder_eq_cons_of_minKey hs
                  have hnode : inorder
                      (.node color (.node cl ll lk lr) key (.node cr rl rk rr)) =
                      inorder (.node cl ll lk lr) ++ key ::
                        inorder (.node cr rl rk rr) :=
                    inorder_node _ _ _
                  have hb := bhBB_balRight (hBhEq.trans ihBh.symm) hRedL hColL
                    (key := s) (right := del s (.node cr rl rk rr))
                  rw [hdelEq]
                  refine ⟨?_,
                    balanced_balRight hBalL ihBal (hBhEq.trans ihBh.symm) hRedL, ?_,
                    redOk_balRight hRedL ihRed
                      (fun hc => ⟨hColL hc, ihCol (hColR hc)⟩),
                    fun hroot => colorBB_balRight_ne_red hroot⟩
                  · rw [inorder_balRight, ihIn, hnode,
                      erase_append_of_not_mem_left hkL, List.erase_cons_head,
                      hrest, List.erase_cons_head]
                  · cases color with
                    | red =>
                        have e : blackHeight
                            (.node .red (.node cl ll lk lr) key (.node cr rl rk rr)) =
                            blackHeight (.node cl ll lk lr) := rfl
                        rw [e, hb.1 rfl, ihBh, hBhEq]
                    | black =>
                        have e : blackHeight
                            (.node .black (.node cl ll lk lr) key (.node cr rl rk rr)) =
                            blackHeight (.node cl ll lk lr) + 1 := rfl
                        rw [e, hb.2 rfl, ihBh, hBhEq]

private theorem inorderBB_del {α : Type u} [LinearOrder α] (tree : Tree α) :
    Ordered tree → ∀ (x : α), inorderBB (del x tree) = (inorder tree).erase x := by
  induction tree with
  | empty => intro _ x; simp [del]
  | node color left key right ihL ihR =>
      intro hOrd x
      rcases hOrd with ⟨hOrdL, hOrdR, hAllL, hAllR⟩
      by_cases hlt : x < key
      · have hdelEq : del x (.node color left key right) =
            balLeft color (del x left) key right := by
          simp [del, hlt]
        have hnot : x ∉ key :: inorder right := by
          intro hx
          rw [List.mem_cons] at hx
          rcases hx with hx | hx
          · exact ne_of_lt hlt hx
          · rw [mem_inorder] at hx
            exact lt_asymm hlt ((all_iff_forall_mem.mp hAllR) x hx)
        rw [hdelEq, inorder_balLeft, ihL hOrdL x, inorder_node]
        exact (erase_append_of_not_mem_right hnot).symm
      · by_cases hgt : key < x
        · have hdelEq : del x (.node color left key right) =
              balRight color left key (del x right) := by
            simp [del, hlt, hgt]
          have hxL : x ∉ inorder left := by
            rw [mem_inorder]
            intro hx
            exact lt_asymm hgt ((all_iff_forall_mem.mp hAllL) x hx)
          rw [hdelEq, inorder_balRight, ihR hOrdR x, inorder_node,
            erase_append_of_not_mem_left hxL,
            erase_cons_tail_of_ne (ne_of_lt hgt)]
        · have hxEq : key = x :=
            (le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)).symm
          subst hxEq
          cases left with
          | empty =>
              cases color with
              | red =>
                  have hdelEq : del key (.node .red .empty key right) =
                      .regular right := by
                    simp [del]
                  rw [hdelEq, inorderBB_regular, inorder_node]
                  simp [List.erase_cons_head]
              | black =>
                  have hdelEq : del key (.node .black .empty key right) =
                      incrBlack right := by
                    simp [del]
                  rw [hdelEq, inorderBB_incrBlack, inorder_node]
                  simp [List.erase_cons_head]
          | node cl ll lk lr =>
              have hkL : key ∉ inorder (.node cl ll lk lr) := by
                rw [mem_inorder]
                intro hx
                exact lt_irrefl key ((all_iff_forall_mem.mp hAllL) key hx)
              cases right with
              | empty =>
                  cases color with
                  | red =>
                      have hdelEq : del key (.node .red (.node cl ll lk lr) key .empty) =
                          .regular (.node cl ll lk lr) := by
                        simp [del]
                      have hnode : inorder (.node .red (.node cl ll lk lr) key .empty) =
                          inorder (.node cl ll lk lr) ++ key ::
                            inorder (.empty : Tree α) :=
                        inorder_node _ _ _
                      rw [hdelEq, inorderBB_regular, hnode, inorder_empty,
                        erase_append_of_not_mem_left hkL]
                      simp [List.erase_cons_head]
                  | black =>
                      have hdelEq : del key (.node .black (.node cl ll lk lr) key .empty) =
                          incrBlack (.node cl ll lk lr) := by
                        simp [del]
                      have hnode : inorder (.node .black (.node cl ll lk lr) key .empty) =
                          inorder (.node cl ll lk lr) ++ key ::
                            inorder (.empty : Tree α) :=
                        inorder_node _ _ _
                      rw [hdelEq, inorderBB_incrBlack, hnode, inorder_empty,
                        erase_append_of_not_mem_left hkL]
                      simp [List.erase_cons_head]
              | node cr rl rk rr =>
                  obtain ⟨s, hs⟩ : ∃ s, minKey (.node cr rl rk rr : Tree α) = some s := by
                    cases hmk : minKey (.node cr rl rk rr : Tree α) with
                    | none =>
                        have hcontra := minKey_eq_none.mp hmk
                        simp at hcontra
                    | some s => exact ⟨s, rfl⟩
                  have hdelEq : del key
                      (.node color (.node cl ll lk lr) key (.node cr rl rk rr)) =
                      balRight color (.node cl ll lk lr) s
                        (del s (.node cr rl rk rr)) := by
                    simp [del, hs]
                  obtain ⟨rest, hrest⟩ := inorder_eq_cons_of_minKey hs
                  have hnode : inorder
                      (.node color (.node cl ll lk lr) key (.node cr rl rk rr)) =
                      inorder (.node cl ll lk lr) ++ key ::
                        inorder (.node cr rl rk rr) :=
                    inorder_node _ _ _
                  rw [hdelEq, inorder_balRight, ihR hOrdR s, hnode,
                    erase_append_of_not_mem_left hkL, List.erase_cons_head,
                    hrest, List.erase_cons_head]

private theorem ordered_of_pairwise_inorder_bal {α : Type u} [LinearOrder α]
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

/-- **Double-black deletion erases the key from the inorder traversal.** For a key $x$ of a
linearly ordered type and an ordered red-black tree $t$, the inorder traversal of the tree
obtained by deleting $x$ from $t$ by the double-black method is the inorder traversal of $t$
with the first occurrence of $x$ removed (unchanged if $x$ does not occur). -/
public theorem inorder_deleteBal {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Ordered tree) :
    inorder (deleteBal x tree) = (inorder tree).erase x := by
  change inorder (blacken (del x tree)) = (inorder tree).erase x
  rw [inorder_blacken, inorderBB_del tree hTree x]

/-- **Keys after double-black deletion.** For keys $x$ and $y$ of a linearly ordered type and an
ordered red-black tree $t$, $y$ is a key of the tree obtained by deleting $x$ from $t$ by the
double-black method if and only if $y$ is a key of $t$ and $y \ne x$. -/
public theorem mem_deleteBal {α : Type u} [LinearOrder α] {x y : α}
    {tree : Tree α} (hTree : Ordered tree) :
    y ∈ deleteBal x tree ↔ y ∈ tree ∧ y ≠ x := by
  rw [← mem_inorder, ← mem_inorder, inorder_deleteBal hTree]
  constructor
  · intro hy
    refine ⟨List.mem_of_mem_erase hy, ?_⟩
    rintro rfl
    exact (inorder_nodup hTree).not_mem_erase hy
  · rintro ⟨hy, hxy⟩
    exact (List.mem_erase_of_ne hxy).mpr hy

/-- **The deleted key is absent after double-black deletion.** Let $\alpha$ be a linearly
ordered type and $t$ a red-black tree with keys in $\alpha$ that is ordered, that is, at every
node all keys of the left subtree are strictly smaller and all keys of the right subtree are
strictly larger than the node's key. Then for every $x \in \alpha$, the key $x$ does not occur in
the tree obtained by deleting $x$ from $t$ by the double-black method. -/
public theorem not_mem_deleteBal_self {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Ordered tree) : x ∉ deleteBal x tree :=
  fun hx => ((mem_deleteBal hTree).mp hx).2 rfl

/-- **Double-black deletion preserves the search-tree order.** Let $\alpha$ be a linearly
ordered type and $t$ a red-black tree with keys in $\alpha$ that is ordered, that is, at every
node all keys of the left subtree are strictly smaller and all keys of the right subtree are
strictly larger than the node's key. Then for every $x \in \alpha$, the tree obtained by deleting
$x$ from $t$ by the double-black method is again ordered. -/
public theorem ordered_deleteBal {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Ordered tree) : Ordered (deleteBal x tree) := by
  apply ordered_of_pairwise_inorder_bal
  rw [inorder_deleteBal hTree]
  exact (ordered_inorder hTree).sublist List.erase_sublist

/-- **Double-black deletion yields a valid tree from the structural invariants.** Let $\alpha$
be a linearly ordered type and $t$ a red-black tree with keys in $\alpha$ that is ordered,
satisfies the red invariant (no red node has a red child), and is black-height balanced (all
root-to-leaf paths contain the same number of black nodes). Then for every $x \in \alpha$, the
tree obtained by deleting $x$ from $t$ by the double-black method is a valid red-black tree.

The root of $t$ need not be black, since the deletion recolors the root of its result black. -/
public theorem valid_deleteBal_of_invariants {α : Type u} [LinearOrder α]
    {x : α} {tree : Tree α} (hOrdered : Ordered tree) (hRedOk : RedOk tree)
    (hBalanced : Balanced tree) : Valid (deleteBal x tree) := by
  obtain ⟨-, hBalBB, -, hRedBB, -⟩ :=
    del_spec tree hOrdered hBalanced hRedOk x
  exact ⟨ordered_deleteBal hOrdered, redOk_blacken hRedBB,
    balanced_blacken hBalBB, colorOf_blacken⟩

/-- **Double-black deletion preserves validity.** Let $\alpha$ be a linearly ordered type and
$t$ a valid red-black tree with keys in $\alpha$: it is ordered, satisfies the red invariant, is
black-height balanced, and has a black root. Then for every $x \in \alpha$, the tree obtained by
deleting $x$ from $t$ by the double-black method is again a valid red-black tree.

The proof uses only that $t$ is ordered, satisfies the red invariant and is balanced. -/
public theorem valid_deleteBal {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Valid tree) : Valid (deleteBal x tree) :=
  valid_deleteBal_of_invariants hTree.1 hTree.2.1 hTree.2.2.1

/-- **Double-black deletion from a valid tree keeps the red invariant.** Let $\alpha$ be a
linearly ordered type and $t$ a valid red-black tree with keys in $\alpha$: it is ordered,
satisfies the red invariant, is black-height balanced, and has a black root. Then for every
$x \in \alpha$, the tree obtained by deleting $x$ from $t$ by the double-black method satisfies
the red invariant: no red node has a red child. -/
public theorem redOk_deleteBal {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Valid tree) : RedOk (deleteBal x tree) :=
  (valid_deleteBal hTree).2.1

/-- **Double-black deletion keeps a valid tree balanced.** Let $\alpha$ be a linearly ordered
type, $x \in \alpha$, and $T$ a valid red-black tree over $\alpha$. Then the tree obtained from
$T$ by double-black deletion of $x$ is balanced. -/
public theorem balanced_deleteBal {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Valid tree) : Balanced (deleteBal x tree) :=
  (valid_deleteBal hTree).2.2.1

/-- **Double-black deletion leaves a black root.** For every key $x$ of a linearly ordered type
and every red-black tree $t$, valid or not, the root of the tree obtained by deleting $x$ from $t$
by the double-black method is black, where the empty tree counts as black. -/
public theorem colorOf_deleteBal {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} : colorOf (deleteBal x tree) = .black :=
  colorOf_blacken

/-- **Black height after double-black deletion.** Let $\alpha$ be a linearly ordered type,
$x \in \alpha$, $T$ a valid red-black tree over $\alpha$, and $T'$ the tree obtained from $T$ by
double-black deletion of $x$. Then the black height of $T'$ either equals the black height of $T$
or is one less than it.

The black height drops by one when a double black left by the deletion is absorbed at the root. -/
public theorem blackHeight_deleteBal {α : Type u} [LinearOrder α] {x : α}
    {tree : Tree α} (hTree : Valid tree) :
    blackHeight (deleteBal x tree) = blackHeight tree ∨
      blackHeight (deleteBal x tree) + 1 = blackHeight tree := by
  obtain ⟨hOrd, hRed, hBal, hcol⟩ := hTree
  obtain ⟨-, -, hBh, -, hColDel⟩ := del_spec tree hOrd hBal hRed x
  have hnr := hColDel hcol
  cases hdel : del x tree with
  | regular t =>
      rw [hdel] at hBh hnr
      have hct : colorOf t = .black := colorBB_regular_ne_red.mp hnr
      have hrb : blackHeight (rootBlack t) = blackHeight t := by
        cases t with
        | empty => rfl
        | node c _ _ _ =>
            have hc : c = .black := hct
            subst hc
            rfl
      refine Or.inl ?_
      change blackHeight (blacken (del x tree)) = blackHeight tree
      rw [hdel]
      change blackHeight (rootBlack t) = blackHeight tree
      rw [hrb]
      exact hBh
  | emptyBB =>
      rw [hdel] at hBh
      refine Or.inr ?_
      change blackHeight (blacken (del x tree)) + 1 = blackHeight tree
      rw [hdel]
      change blackHeight (.empty : Tree α) + 1 = blackHeight tree
      have e1 : blackHeight (.empty : Tree α) = 1 := rfl
      have e2 : bhBB (.emptyBB : BBTree α) = 2 := rfl
      omega
  | nodeBB l k r =>
      rw [hdel] at hBh
      refine Or.inr ?_
      change blackHeight (blacken (del x tree)) + 1 = blackHeight tree
      rw [hdel]
      change blackHeight (.node .black l k r) + 1 = blackHeight tree
      have e1 : blackHeight (.node .black l k r) = blackHeight l + 1 := rfl
      have e2 : bhBB (.nodeBB l k r) = blackHeight l + 2 := rfl
      omega

end DeleteBalanced
end RedBlackTree
end Cslib.Algorithms.Lean
