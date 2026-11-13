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

/-- **Binary trees with cached heights.** For a type $\alpha$, a tree with cached heights over
$\alpha$ (the underlying type of AVL trees) is either empty, or a node made of a natural
number $h$ (its cached height), a left subtree, a key in $\alpha$ and a right subtree.

The type does not require $h$ to equal the actual height of the node. -/
public inductive Tree (α : Type u) where
  | empty : Tree α
  | node (height : Nat) (left : Tree α) (key : α) (right : Tree α) : Tree α
deriving DecidableEq, Repr

variable {α : Type u}

/-- **Cached height of an AVL tree.** The cached height of the empty tree is $0$, and the cached
height of a node is the height value stored at that node, so it is read off the root in
constant time. -/
public def height : Tree α → Nat
  | .empty => 0
  | .node cached _ _ _ => cached

/-- **AVL node with computed height.** Write $h(T)$ for the cached height at the root of a tree
$T$, with $h$ of the empty tree equal to $0$. Given trees $L$ and $R$ and a key $k$, this is the
node with left subtree $L$, key $k$ and right subtree $R$ whose cached height is
$\max(h(L), h(R)) + 1$. -/
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

/-- **Correct cached heights.** The empty tree has correct cached heights. A node storing the
height $c$, with left subtree $\ell$ and right subtree $r$, has correct cached heights when
$\ell$ and $r$ have correct cached heights and $c = \max(h(\ell), h(r)) + 1$, where $h$ denotes
the height cached at the root of a tree (and $0$ for the empty tree). -/
public def CacheCorrect : Tree α → Prop
  | .empty => True
  | .node cached left _ right =>
      CacheCorrect left ∧ CacheCorrect right ∧
        cached = max (height left) (height right) + 1

/-- **AVL balance invariant.** The empty tree is balanced. A node with left subtree $\ell$ and
right subtree $r$ is balanced when $\ell$ and $r$ are balanced and $h(\ell) \le h(r) + 1$ and
$h(r) \le h(\ell) + 1$, where $h$ denotes the height cached at the root of a tree (and $0$ for the
empty tree). Equivalently, at every node the balance factor $h(\ell) - h(r)$ lies in
$\{-1, 0, 1\}$. -/
public def Balanced : Tree α → Prop
  | .empty => True
  | .node _ left _ right =>
      Balanced left ∧ Balanced right ∧ height left ≤ height right + 1 ∧
        height right ≤ height left + 1

/-- **Erasing the cached heights of an AVL tree.** Let $\alpha$ be a type. Erasing the cached
heights sends a tree with cached heights over $\alpha$ to a binary tree over $\alpha$: the empty
tree goes to the empty binary tree, and a node with height $h$, left subtree $L$, key $k$ and
right subtree $R$ goes to the binary-tree node with key $k$ whose left and right subtrees are
the erasures of $L$ and $R$. -/
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

/-- **Membership in an AVL tree.** A key $x$ belongs to a tree $T$ when $x$ belongs to the binary
tree obtained from $T$ by erasing the cached heights. Equivalently, no key belongs to the empty
tree, and $x$ belongs to a node with left subtree $L$, key $k$ and right subtree $R$ exactly when
$x$ belongs to $L$, $x = k$, or $x$ belongs to $R$. -/
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

/-- **Every key of an AVL tree satisfies a predicate.** For a predicate $p$ on keys and a tree $t$
with cached heights, $\mathrm{All}(p, t)$ holds when $p$ holds at the key of every node of $t$. It
is defined as the corresponding predicate on the plain binary tree obtained from $t$ by erasing
its cached heights. -/
public def All (p : α → Prop) (tree : Tree α) : Prop :=
  BinarySearchTree.All p (toBinaryTree tree)

/-- **Ordered AVL trees.** Let $\alpha$ be a type with a relation $<$. A tree with cached
heights over $\alpha$ is ordered when the binary tree obtained by erasing its cached heights
is an ordered binary search tree: the empty tree is ordered, and a node with key $k$ is
ordered when its left and right subtrees are ordered, every key of the left subtree is less
than $k$, and every key of the right subtree is greater than $k$. -/
public def Ordered [LT α] (tree : Tree α) : Prop :=
  BinarySearchTree.Ordered (toBinaryTree tree)

/-- **Inorder traversal of an AVL tree onto a suffix.** Given a tree $t$ and a list $s$, this is
the list of keys of $t$ in inorder (left subtree, root key, right subtree, recursively)
followed by $s$. It is computed in linear time by the binary search tree traversal of $t$ with
its cached heights erased. -/
public def inorderAux (tree : Tree α) (suffix : List α) : List α :=
  BinarySearchTree.inorderAux (toBinaryTree tree) suffix

/-- **Inorder traversal of an AVL tree.** The inorder traversal of a tree $t$ lists its keys with
the left subtree first, then the root key, then the right subtree, recursively. It is the
binary search tree inorder traversal of $t$ with its cached heights erased, computed in linear
time. -/
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

/-- **AVL membership is membership in the underlying binary tree.** A key $x$ lies in a tree $T$ if
and only if $x$ lies in the binary tree obtained from $T$ by erasing the cached heights.

This holds by definition. -/
public theorem mem_toBinaryTree {x : α} {tree : Tree α} :
    x ∈ tree ↔ x ∈ toBinaryTree tree :=
  Iff.rfl

/-- **The all-keys predicate is unchanged by erasing height caches.** For a predicate $p$ on keys
and a tree $t$ with cached heights, $\mathrm{All}(p, t)$ holds if and only if $p$ holds at every
key of the plain binary tree obtained from $t$ by erasing its cached heights. This holds by
definition. -/
public theorem all_toBinaryTree {p : α → Prop} {tree : Tree α} :
    All p tree ↔ BinarySearchTree.All p (toBinaryTree tree) :=
  Iff.rfl

/-- **Order of an AVL tree via its underlying binary tree.** Let $\alpha$ be a type with a
relation $<$. A tree $t$ with cached heights over $\alpha$ is ordered if and only if the
binary tree obtained from $t$ by erasing the cached heights is an ordered binary search
tree. -/
public theorem ordered_toBinaryTree [LT α] {tree : Tree α} :
    Ordered tree ↔ BinarySearchTree.Ordered (toBinaryTree tree) :=
  Iff.rfl

/-- **AVL inorder traversal agrees with the erased binary search tree.** For every AVL tree
$t$, the inorder traversal of $t$ equals the binary search tree inorder traversal of the binary
tree obtained from $t$ by erasing its cached heights; this holds by definition. -/
public theorem inorder_toBinaryTree (tree : Tree α) :
    inorder tree = BinarySearchTree.inorder (toBinaryTree tree) :=
  rfl

/-- **Membership search in an AVL tree.** For a linearly ordered type $\alpha$ and a key $x$,
the search for $x$ returns false on the empty tree; at a node with key $k$ it searches the left
subtree if $x < k$, searches the right subtree if $k < x$, and returns true otherwise. The cached
heights are ignored. -/
public def contains [LinearOrder α] (x : α) : Tree α → Bool
  | .empty => false
  | .node _ left key right =>
      if x < key then contains x left
      else if key < x then contains x right
      else true

/-- **AVL rebalancing.** For trees $l$, $r$ with cached heights and a key $x$, write $h(T)$ for
the cached height at the root of a tree $T$ (zero for the empty tree) and $N(A, y, B)$ for the
node with left subtree $A$, key $y$, right subtree $B$ and cached height $\max(h(A), h(B)) + 1$.
The node $\mathrm{balance}(l, x, r)$ is defined by cases. If $h(l) > h(r) + 1$ and $l$ has left
subtree $A$, key $y$ and right subtree $B$, it is the single right rotation $N(A, y, N(B, x, r))$
when $h(B) \le h(A)$, and otherwise, when $B$ has left subtree $B_1$, key $z$ and right subtree
$B_2$, the left-right double rotation $N(N(A, y, B_1), z, N(B_2, x, r))$. Symmetrically, if
$h(l) \le h(r) + 1$, $h(r) > h(l) + 1$ and $r$ has left subtree $A$, key $y$ and right subtree $B$,
it is the single left rotation $N(N(l, x, A), y, B)$ when $h(A) \le h(B)$, and otherwise, when
$A$ has left subtree $A_1$, key $z$ and right subtree $A_2$, the right-left double rotation
$N(N(l, x, A_1), z, N(A_2, y, B))$. In every other case it is $N(l, x, r)$.

For balanced children with correct cached heights whose heights differ by at most two, the result
is balanced again. -/
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

/-- **Insertion into an AVL tree.** Let the keys be linearly ordered, and write
$\mathrm{balance}(L, k, R)$ for the AVL rebalancing of the node with left subtree $L$, key $k$ and
right subtree $R$. Inserting $x$ into the empty tree gives the node with key $x$, two empty
children and cached height $1$. Inserting $x$ into a node with left subtree $L$, key $k$ and right
subtree $R$ gives $\mathrm{balance}(L', k, R)$, where $L'$ is the result of inserting $x$ into $L$,
when $x < k$; it gives $\mathrm{balance}(L, k, R')$, where $R'$ is the result of inserting $x$
into $R$, when $k < x$; and otherwise it returns the node unchanged. -/
public def insert [LinearOrder α] (x : α) : Tree α → Tree α
  | .empty => mkNode .empty x .empty
  | tree@(.node _ left key right) =>
      if x < key then balance (insert x left) key right
      else if key < x then balance left key (insert x right)
      else tree

/-- **Building an AVL tree from a list.** For a linearly ordered type $\alpha$, the tree built
from the empty list is the empty tree, and the tree built from a list with head $x$ and tail
$xs$ is obtained by AVL insertion of $x$ into the tree built from $xs$. Thus the list is
inserted from right to left, starting from the empty tree. -/
public def fromList [LinearOrder α] : List α → Tree α
  | [] => .empty
  | x :: xs => insert x (fromList xs)

/-- **The all-keys predicate in terms of membership (AVL trees).** For a predicate $p$ on keys and
a tree $t$ with cached heights, $\mathrm{All}(p, t)$ holds if and only if $p(x)$ holds for every
$x \in t$, where $x \in t$ means that $x$ is the key of some node of $t$. -/
public theorem all_iff_forall_mem {p : α → Prop} {tree : Tree α} :
    All p tree ↔ ∀ x, x ∈ tree → p x :=
  BinarySearchTree.all_iff_forall_mem

/-- **Membership in the inorder traversal of an AVL tree.** A key $x$ occurs in the inorder
traversal of a tree $T$ if and only if $x$ lies in $T$. -/
public theorem mem_inorder {x : α} {tree : Tree α} :
    x ∈ inorder tree ↔ x ∈ tree :=
  BinarySearchTree.mem_inorder

/-- **The inorder traversal of an ordered AVL tree is strictly increasing.** Let $\alpha$ be a
linearly ordered type. If a tree $t$ with cached heights over $\alpha$ is ordered, then in
the inorder traversal of $t$ every key is less than every key that comes after it. -/
public theorem ordered_inorder [LinearOrder α] {tree : Tree α}
    (hTree : Ordered tree) : List.Pairwise (· < ·) (inorder tree) :=
  BinarySearchTree.ordered_inorder hTree

/-- **The inorder traversal of an ordered AVL tree has no duplicates.** For a linearly ordered
type $\alpha$, if an AVL tree is ordered, then its inorder traversal contains no key twice. -/
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

/-- **The AVL node constructor preserves cached heights.** If two AVL trees $\ell$ and $r$ have
correct cached heights, then for every key $k$ the node built from $\ell$, $k$ and $r$ by the
smart constructor, which stores the height $\max(h(\ell), h(r)) + 1$ where $h$ denotes the height
cached at the root (and $0$ for the empty tree), also has correct cached heights. -/
public theorem cacheCorrect_mkNode {key : α} {left right : Tree α}
    (hLeft : CacheCorrect left) (hRight : CacheCorrect right) :
    CacheCorrect (mkNode left key right) :=
  ⟨hLeft, hRight, rfl⟩

/-- **The AVL node constructor preserves balance.** Let $\ell$ and $r$ be AVL trees that satisfy
the AVL balance invariant, and write $h(\ell)$ and $h(r)$ for the heights cached at their roots
(with height $0$ for the empty tree). If $h(\ell) \le h(r) + 1$ and $h(r) \le h(\ell) + 1$, then
for every key $k$ the node built from $\ell$, $k$ and $r$ by the smart constructor, which stores
the height $\max(h(\ell), h(r)) + 1$, satisfies the AVL balance invariant. -/
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

/-- **Rebalancing when the heights of the children differ by at most one.** Let $l$ and $r$ be
trees with cached heights, let $x$ be a key, and write $h(T)$ for the cached height at the root
of a tree $T$ (zero for the empty tree). If $h(l) \le h(r) + 1$ and $h(r) \le h(l) + 1$, then
$\mathrm{balance}(l, x, r)$ is the node with left subtree $l$, key $x$, right subtree $r$ and
cached height $\max(h(l), h(r)) + 1$; no rotation is performed. -/
public theorem balance_eq_mkNode_of_le {key : α} {left right : Tree α}
    (hLeft : height left ≤ height right + 1) (hRight : height right ≤ height left + 1) :
    balance left key right = mkNode left key right := by
  unfold balance
  simp only [show ¬(height right + 1 < height left) by omega,
    show ¬(height left + 1 < height right) by omega, ite_false]

/-- **Single right rotation in AVL rebalancing.** Write $h(T)$ for the cached height at the root
of a tree $T$ (zero for the empty tree), $\langle c; A, y, B \rangle$ for the node with cached
height $c$, left subtree $A$, key $y$ and right subtree $B$, and $N(A, y, B)$ for the node
$\langle \max(h(A), h(B)) + 1; A, y, B \rangle$. Let $A$, $B$, $R$ be trees with cached heights,
let $x$, $y$ be keys and let $c$ be a natural number. If $h(R) + 1 < c$ and $h(B) \le h(A)$, then
$\mathrm{balance}(\langle c; A, y, B \rangle, x, R) = N(A, y, N(B, x, R))$. -/
public theorem balance_left_single {key leftKey : α} {cached : Nat}
    {leftLeft leftRight right : Tree α}
    (hTall : height right + 1 < cached) (hSingle : height leftRight ≤ height leftLeft) :
    balance (.node cached leftLeft leftKey leftRight) key right =
      mkNode leftLeft leftKey (mkNode leftRight key right) := by
  unfold balance
  simp only [height_node, hTall, hSingle, ite_true]

/-- **Left-right double rotation in AVL rebalancing.** Write $h(T)$ for the cached height at the
root of a tree $T$ (zero for the empty tree), $\langle c; A, y, B \rangle$ for the node with
cached height $c$, left subtree $A$, key $y$ and right subtree $B$, and $N(A, y, B)$ for the node
$\langle \max(h(A), h(B)) + 1; A, y, B \rangle$. Let $A$, $B$, $C$, $R$ be trees with cached
heights, let $x$, $y$, $z$ be keys and let $c$, $c'$ be natural numbers. If $h(R) + 1 < c$ and
$h(A) < c'$, then $\mathrm{balance}(\langle c; A, y, \langle c'; B, z, C \rangle \rangle, x, R) =
N(N(A, y, B), z, N(C, x, R))$. -/
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

/-- **Single left rotation in AVL rebalancing.** Write $h(T)$ for the cached height at the root of
a tree $T$ (zero for the empty tree), $\langle c; A, y, B \rangle$ for the node with cached height
$c$, left subtree $A$, key $y$ and right subtree $B$, and $N(A, y, B)$ for the node
$\langle \max(h(A), h(B)) + 1; A, y, B \rangle$. Let $L$, $A$, $B$ be trees with cached heights,
let $x$, $y$ be keys and let $c$ be a natural number. If $h(L) + 1 < c$ and $h(A) \le h(B)$, then
$\mathrm{balance}(L, x, \langle c; A, y, B \rangle) = N(N(L, x, A), y, B)$. -/
public theorem balance_right_single {key rightKey : α} {cached : Nat}
    {left rightLeft rightRight : Tree α}
    (hTall : height left + 1 < cached)
    (hSingle : height rightLeft ≤ height rightRight) :
    balance left key (.node cached rightLeft rightKey rightRight) =
      mkNode (mkNode left key rightLeft) rightKey rightRight := by
  unfold balance
  simp only [height_node, show ¬(cached + 1 < height left) by omega, ite_false,
    hTall, ite_true, hSingle]

/-- **Right-left double rotation in AVL rebalancing.** Write $h(T)$ for the cached height at the
root of a tree $T$ (zero for the empty tree), $\langle c; A, y, B \rangle$ for the node with
cached height $c$, left subtree $A$, key $y$ and right subtree $B$, and $N(A, y, B)$ for the node
$\langle \max(h(A), h(B)) + 1; A, y, B \rangle$. Let $L$, $A$, $B$, $C$ be trees with cached
heights, let $x$, $y$, $z$ be keys and let $c$, $c'$ be natural numbers. If $h(L) + 1 < c$ and
$h(C) < c'$, then $\mathrm{balance}(L, x, \langle c; \langle c'; A, z, B \rangle, y, C \rangle) =
N(N(L, x, A), z, N(B, y, C))$. -/
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

/-- **AVL rebalancing preserves cached heights.** If two AVL trees $\ell$ and $r$ have correct
cached heights, then for every key $k$ the tree produced by the rebalancing function from
$\ell$, $k$ and $r$ also has correct cached heights. -/
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

/-- **Upper bound on height after AVL rebalancing.** Let $l$ and $r$ be trees whose cached
heights are correct at every node, and write $h$ for the cached height. Then for every key $k$,
the rebalanced node $b$ built from $l$, $k$ and $r$ satisfies $h(b) \le \max(h(l), h(r)) + 1$. -/
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

/-- **Rebalancing does not drop below the taller child.** Write $h(T)$ for the cached height at the
root of a tree $T$, with $h$ of the empty tree equal to $0$, and write $\mathrm{balance}(L, k, R)$
for the AVL rebalancing of the node with left subtree $L$, key $k$ and right subtree $R$. If $L$
and $R$ are trees whose cached heights are correct at every node, then for every key $k$ we have
$\max(h(L), h(R)) \le h(\mathrm{balance}(L, k, R))$. -/
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

/-- **AVL rebalancing yields a balanced tree.** Let $l$ and $r$ be trees whose cached heights are
correct at every node and which are balanced (at every node the cached heights of the two
subtrees differ by at most one), let $x$ be a key, and write $h(T)$ for the cached height at the
root of a tree $T$ (zero for the empty tree). If $h(l) \le h(r) + 2$ and $h(r) \le h(l) + 2$,
then $\mathrm{balance}(l, x, r)$ is balanced.

One insertion step maintains this precondition. -/
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

/-- **AVL rebalancing preserves the inorder traversal.** For all trees $l$ and $r$ and every
key $k$, the inorder traversal of the rebalanced node built from $l$, $k$ and $r$ is the
inorder traversal of $l$, followed by $k$, followed by the inorder traversal of $r$. -/
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

/-- **Membership after AVL rebalancing.** Write $\mathrm{balance}(L, k, R)$ for the AVL rebalancing
of the node with left subtree $L$, key $k$ and right subtree $R$. For trees $L$ and $R$ and keys
$k$ and $x$, the key $x$ lies in $\mathrm{balance}(L, k, R)$ if and only if $x$ lies in $L$,
$x = k$, or $x$ lies in $R$. -/
public theorem mem_balance {x key : α} {left right : Tree α} :
    x ∈ balance left key right ↔ x ∈ left ∨ x = key ∨ x ∈ right := by
  rw [← mem_inorder, inorder_balance]
  simp [mem_inorder]

/-- **Rebalancing an AVL node preserves the search-tree order.** Let $\alpha$ be a linearly
ordered type, let $k \in \alpha$, and let $L$ and $R$ be ordered trees with cached heights
over $\alpha$ such that every key of $L$ is less than $k$ and every key of $R$ is greater
than $k$. Then the tree that rebalancing produces from left subtree $L$, key $k$ and right
subtree $R$ is ordered. -/
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

/-- **AVL insertion preserves cached heights.** Let $\alpha$ be a linearly ordered type. If an
AVL tree $t$ over $\alpha$ has correct cached heights, then for every $x \in \alpha$ the tree
obtained by inserting $x$ into $t$ also has correct cached heights. -/
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

/-- **Upper bound on height after AVL insertion.** For a linearly ordered type $\alpha$, if a tree
$t$ has correct cached heights at every node, then for every key $x$ the cached height of the
tree obtained by inserting $x$ into $t$ is at most the cached height of $t$ plus one. -/
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

/-- **Insertion does not lower the height.** Write $h(T)$ for the cached height at the root of a
tree $T$, with $h$ of the empty tree equal to $0$. Let the keys be linearly ordered, and let $T$ be
a tree whose cached heights are correct at every node and which satisfies the AVL balance
invariant at every node. Then for every key $x$, if $T'$ is the tree obtained by inserting $x$
into $T$, we have $h(T) \le h(T')$. -/
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

/-- **AVL insertion preserves balance.** Let $\alpha$ be a linearly ordered type, let $t$ be an
AVL tree over $\alpha$ and let $x \in \alpha$. If $t$ has correct cached heights and satisfies
the AVL balance invariant, then the tree obtained by inserting $x$ into $t$ also satisfies the
AVL balance invariant. -/
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

/-- **Membership after insertion into an AVL tree.** Let the keys be linearly ordered. A key $y$
lies in the tree obtained by inserting $x$ into a tree $T$ if and only if $y = x$ or $y$ lies
in $T$. -/
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

/-- **AVL insertion preserves the search-tree order.** Let $\alpha$ be a linearly ordered type.
For every key $x \in \alpha$ and every ordered tree $t$ with cached heights over $\alpha$, the
tree obtained by inserting $x$ into $t$ is ordered. -/
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

/-- **Correctness of AVL search.** Let $\alpha$ be a linearly ordered type and let $t$ be an
ordered AVL tree over $\alpha$. Then for every $x \in \alpha$, searching for $x$ in $t$ by
following comparisons from the root returns true if and only if $x$ is a key of $t$. -/
public theorem contains_eq_true_iff [LinearOrder α] {x : α} {tree : Tree α}
    (hTree : Ordered tree) : contains x tree = true ↔ x ∈ tree := by
  rw [contains_eq_bstContains]
  exact BinarySearchTree.contains_eq_true_iff hTree

/-- **AVL trees built from a list have correct cached heights.** For every list $L$ over a
linearly ordered type, the AVL tree built from $L$ by successive insertion has correct cached
heights. -/
public theorem cacheCorrect_fromList [LinearOrder α] {xs : List α} :
    CacheCorrect (fromList xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact cacheCorrect_insert ih

/-- **AVL trees built from a list are balanced.** For every list $L$ over a linearly ordered
type, the AVL tree built from $L$ by successive insertion satisfies the AVL balance invariant. -/
public theorem balanced_fromList [LinearOrder α] {xs : List α} :
    Balanced (fromList xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact balanced_insert cacheCorrect_fromList ih

/-- **AVL trees built from a list are ordered.** Let $\alpha$ be a linearly ordered type. For
every list $xs$ of elements of $\alpha$, the tree obtained from the empty tree by inserting
the elements of $xs$ one at a time, from the last element to the first, is ordered. -/
public theorem ordered_fromList [LinearOrder α] {xs : List α} :
    Ordered (fromList xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ordered_insert ih

/-- **Membership in an AVL tree built from a list.** Let the keys be linearly ordered. A key lies
in the tree obtained by inserting the entries of a list one at a time, from last to first, into
the empty tree exactly when it is in the list. -/
public theorem mem_fromList [LinearOrder α] {x : α} {xs : List α} :
    x ∈ fromList xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [fromList]
  | cons y ys ih => simp [fromList, mem_insert, ih]

end AvlTree
end Cslib.Algorithms.Lean
