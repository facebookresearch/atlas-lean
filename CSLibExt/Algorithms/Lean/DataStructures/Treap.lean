/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic

set_option autoImplicit false

universe u v

@[expose] public section

/-!
# Treaps

This module defines deterministic treap operations. Each node stores an explicit
priority; no correctness theorem depends on a random source. Insertion and
deletion are implemented from key splitting and priority-guided merging.

The implementation and proofs were authored for this module. The representation
style follows `BinarySearchTree` from D123980084; no public treap implementation
was copied.
-/

namespace Cslib.Algorithms.Lean
namespace Treap

/-- **Treap trees.** For a type $\kappa$ of keys and a type $\nu$ of values, a treap tree is
either empty or a node made of a left subtree, a key in $\kappa$, a value in $\nu$, a
natural-number priority and a right subtree. Trees are finite, and no ordering of keys or
priorities is imposed; the treap invariants are stated separately. -/
public inductive Tree (κ : Type u) (ν : Type v) where
  | empty
  | node (left : Tree κ ν) (key : κ) (value : ν) (priority : Nat)
      (right : Tree κ ν)
  deriving DecidableEq, Repr

namespace Tree

/-- **Treap predicate holding at every node.** Let $p$ be a predicate on a key, a value and a
natural-number priority. A tree satisfies $p$ at every node when $p(k, v, n)$ holds for the key
$k$, value $v$ and priority $n$ of each of its nodes. By recursion, this holds for the empty
tree, and holds for a node exactly when it holds for the left subtree, $p$ holds at the node's
key, value and priority, and it holds for the right subtree. -/
public def AllNodes {κ : Type u} {ν : Type v} (p : κ → ν → Nat → Prop) :
    Tree κ ν → Prop
  | .empty => True
  | .node left key value priority right =>
      AllNodes p left ∧ p key value priority ∧ AllNodes p right

/-- **Entry membership in a treap tree.** A key $k$, value $v$ and priority $p$ form an entry
of a treap tree when some node stores exactly $k$, $v$ and $p$: the empty tree has no
entries, and $(k, v, p)$ is an entry of a node with left subtree $L$, root key $r$, root value
$w$, root priority $q$ and right subtree $R$ exactly when it is an entry of $L$, or $k = r$,
$v = w$ and $p = q$, or it is an entry of $R$. -/
public def MemNode {κ : Type u} {ν : Type v} (key : κ) (value : ν)
    (priority : Nat) : Tree κ ν → Prop
  | .empty => False
  | .node left rootKey rootValue rootPriority right =>
      MemNode key value priority left ∨
        (key = rootKey ∧ value = rootValue ∧ priority = rootPriority) ∨
        MemNode key value priority right

/-- **Key membership in a treap tree.** A key $k$ is a key of a treap tree when it is stored
at some node: no key belongs to the empty tree, and $k$ belongs to a node with left subtree
$L$, root key $r$ and right subtree $R$ exactly when $k$ belongs to $L$, or $k = r$, or $k$
belongs to $R$.

Membership is structural and does not assume the search-tree or heap invariants. -/
public def MemKey {κ : Type u} {ν : Type v} (key : κ) : Tree κ ν → Prop
  | .empty => False
  | .node left rootKey _ _ right =>
      MemKey key left ∨ key = rootKey ∨ MemKey key right

/-- Key membership notation for trees. -/
public instance {κ : Type u} {ν : Type v} : Membership κ (Tree κ ν) :=
  ⟨fun tree key => MemKey key tree⟩

/-- **Treap inorder traversal onto a suffix.** For a tree $t$ and a list $s$ of key-value pairs,
the traversal of $t$ onto $s$ is defined by recursion: for the empty tree it is $s$, and for a
node with left subtree $l$, key $k$, value $v$ and right subtree $r$ it is the traversal of $l$
onto the list obtained by putting $(k, v)$ in front of the traversal of $r$ onto $s$. The result
is the key-value pairs of $t$ in inorder, priorities dropped, followed by $s$.

No ancestor recopies a completed traversal, so the traversal takes linear time. -/
public def contentsAux {κ : Type u} {ν : Type v} :
    Tree κ ν → List (κ × ν) → List (κ × ν)
  | .empty, suffix => suffix
  | .node left key value _ right, suffix =>
      contentsAux left ((key, value) :: contentsAux right suffix)

private theorem contentsAux_append {κ : Type u} {ν : Type v} (tree : Tree κ ν)
    (xs ys : List (κ × ν)) :
    contentsAux tree (xs ++ ys) = contentsAux tree xs ++ ys := by
  induction tree generalizing xs with
  | empty => rfl
  | node left key value priority right ihLeft ihRight =>
      simp only [contentsAux]
      rw [ihRight]
      change contentsAux left (((key, value) :: contentsAux right xs) ++ ys) =
        contentsAux left ((key, value) :: contentsAux right xs) ++ ys
      exact ihLeft _

/-- **Treap inorder contents.** The contents of a tree $t$ is the list of its key-value pairs in
inorder (left subtree, then node, then right subtree), with priorities dropped. It is defined as
the inorder traversal of $t$ onto the empty list, which takes linear time. -/
public def contents {κ : Type u} {ν : Type v} (tree : Tree κ ν) : List (κ × ν) :=
  contentsAux tree []

/-- **Treap inorder contents of a node.** For trees $l$ and $r$, a key $k$, a value $v$ and a
natural-number priority $n$, the inorder list of key-value pairs of the node with left subtree
$l$, key $k$, value $v$, priority $n$ and right subtree $r$ is the inorder list of $l$, followed
by $(k, v)$, followed by the inorder list of $r$. -/
public theorem contents_node {κ : Type u} {ν : Type v}
    (left : Tree κ ν) (key : κ) (value : ν) (priority : Nat) (right : Tree κ ν) :
    contents (.node left key value priority right) =
      contents left ++ (key, value) :: contents right := by
  show contentsAux left ((key, value) :: contentsAux right []) =
    contentsAux left [] ++ (key, value) :: contentsAux right []
  rw [← List.singleton_append, contentsAux_append]
  conv_lhs => rw [← List.nil_append [(key, value)], contentsAux_append]
  rw [List.append_assoc]

/-- **Size of a treap tree.** The size of a tree is its number of nodes, computed recursively:
the empty tree has size $0$, and a node with left subtree $L$ and right subtree $R$ has size
equal to the size of $L$ plus one plus the size of $R$. -/
public def size {κ : Type u} {ν : Type v} : Tree κ ν → Nat
  | .empty => 0
  | .node left _ _ _ right => size left + 1 + size right

/-- **Ordered treap tree.** For a key type equipped with a relation $<$, a treap tree is
ordered when it is empty, or when it is a node with key $k$ whose left and right subtrees are
both ordered, every key $x$ in the left subtree satisfies $x < k$, and every key $y$ in the
right subtree satisfies $k < y$. -/
public def Ordered {κ : Type u} {ν : Type v} [LT κ] : Tree κ ν → Prop
  | .empty => True
  | .node left key _ _ right =>
      Ordered left ∧ Ordered right ∧
        AllNodes (fun childKey _ _ => childKey < key) left ∧
        AllNodes (fun childKey _ _ => key < childKey) right

/-- **Heap order of treap priorities.** A tree is heap-ordered when the priority of every
node is at most the priority of every node below it. Recursively, the empty tree is
heap-ordered, and a node with priority $p$ is heap-ordered when its left and right subtrees
are heap-ordered and every node in them has priority at least $p$. -/
public def HeapOrdered {κ : Type u} {ν : Type v} : Tree κ ν → Prop
  | .empty => True
  | .node left _ _ priority right =>
      HeapOrdered left ∧ HeapOrdered right ∧
        AllNodes (fun _ _ childPriority => priority ≤ childPriority) left ∧
        AllNodes (fun _ _ childPriority => priority ≤ childPriority) right

/-- **Valid treap.** A binary tree whose nodes each carry a key, a value and a natural-number
priority, with keys compared by a relation $<$ (any `LT` instance; no order axioms are
assumed), is a valid treap when it satisfies both of the following at every node: every key in
the left subtree is less than the node's key and the node's key is less than every key in the
right subtree (search-tree order with respect to $<$), and the node's priority is at most the
priority of every node in its left and right subtrees (min-heap order on priorities). -/
public def Valid {κ : Type u} {ν : Type v} [LT κ] (tree : Tree κ ν) : Prop :=
  Ordered tree ∧ HeapOrdered tree

/-- **Treap lookup.** Looking up a key $k$ in a tree with keys in a linearly ordered type follows
the binary search tree comparisons. The empty tree gives no value. At a node with key $r$ and
value $v$, the lookup continues in the left subtree if $k < r$, continues in the right subtree
if $r < k$, and otherwise returns $v$. -/
public def lookup {κ : Type u} {ν : Type v} [LinearOrder κ] (key : κ) :
    Tree κ ν → Option ν
  | .empty => none
  | .node left rootKey value _ right =>
      if key < rootKey then lookup key left
      else if rootKey < key then lookup key right
      else some value

/-- **Lookup with cost.** The costed lookup of a key $k$ in a tree with keys in a linearly
ordered type returns a possibly absent value together with a natural number counting the
visited nodes. On the empty tree it returns no value and cost $0$. At a node with key $r$ and
value $v$, if $k < r$ it returns the result of the costed lookup of $k$ in the left subtree
with cost increased by $1$; if $r < k$ it does the same with the right subtree; otherwise it
returns $v$ with cost $1$. -/
public def lookupWithCost {κ : Type u} {ν : Type v} [LinearOrder κ] (key : κ) :
    Tree κ ν → Option ν × Nat
  | .empty => (none, 0)
  | .node left rootKey value _ right =>
      if key < rootKey then
        let result := lookupWithCost key left
        (result.1, result.2 + 1)
      else if rootKey < key then
        let result := lookupWithCost key right
        (result.1, result.2 + 1)
      else (some value, 1)

/-- **Root priority of a treap tree.** The root priority of a treap tree is an optional
natural number: it is absent for the empty tree, and for a node it is the priority stored at
that node. -/
public def rootPriority {κ : Type u} {ν : Type v} : Tree κ ν → Option Nat
  | .empty => none
  | .node _ _ _ priority _ => some priority

/-- **Treap merge.** The merge of two treap trees is defined recursively. Merging the empty
tree with a tree $T$, or $T$ with the empty tree, gives $T$. If both trees are nodes, with
root priorities $p$ for the first and $q$ for the second, then when $p \le q$ the result keeps
the root of the first tree and its left subtree, and its right subtree is the merge of the
first tree's right subtree with the second tree; otherwise the result keeps the root of the
second tree and its right subtree, and its left subtree is the merge of the first tree with
the second tree's left subtree. -/
public def merge {κ : Type u} {ν : Type v} : Tree κ ν → Tree κ ν → Tree κ ν
  | .empty, right => right
  | left, .empty => left
  | .node leftLeft leftKey leftValue leftPriority leftRight,
      .node rightLeft rightKey rightValue rightPriority rightRight =>
    if leftPriority ≤ rightPriority then
      .node leftLeft leftKey leftValue leftPriority
        (merge leftRight (.node rightLeft rightKey rightValue rightPriority rightRight))
    else
      .node
        (merge (.node leftLeft leftKey leftValue leftPriority leftRight) rightLeft)
        rightKey rightValue rightPriority rightRight
termination_by left right => size left + size right
decreasing_by all_goals (simp_wf; simp [size] <;> omega)

/-- **Result of a treap split.** For key type $\kappa$ and value type $\nu$, a split result
consists of a lower tree, an optional entry given by a value in $\nu$ together with a
natural-number priority, and an upper tree, where both trees are treap trees with keys in
$\kappa$ and values in $\nu$.

The structure imposes no constraint; on an ordered tree, splitting at a pivot fills the lower
tree with the keys below the pivot, the upper tree with the keys above it, and the entry with
the pivot's value and priority when the pivot occurs. -/
public structure SplitResult (κ : Type u) (ν : Type v) where
  /-- The subtree containing keys below the pivot. -/
  less : Tree κ ν
  /-- The pivot's value and priority when it was present. -/
  found : Option (ν × Nat)
  /-- The subtree containing keys above the pivot. -/
  greater : Tree κ ν
  deriving DecidableEq, Repr

/-- **Treap split.** Let the keys come from a linear order, and write $(L, k, v, q, R)$ for the
node with left subtree $L$, key $k$, value $v$, priority $q$ and right subtree $R$. Splitting
a tree at a pivot $p$ returns a split result, defined by recursion on the tree. The empty tree
splits into two empty trees and no entry. For a node $(L, k, v, q, R)$: if $k < p$, split $R$
at $p$ into a lower tree $R_1$, an optional entry $e$ and an upper tree $R_2$, and return the
lower tree $(L, k, v, q, R_1)$, the entry $e$ and the upper tree $R_2$; if $p < k$, split $L$
at $p$ into $L_1$, $e$ and $L_2$, and return the lower tree $L_1$, the entry $e$ and the upper
tree $(L_2, k, v, q, R)$; otherwise $k = p$, and return the lower tree $L$, the entry
$(v, q)$ and the upper tree $R$.

On an ordered tree, the lower tree holds the keys below $p$, the upper tree holds the keys
above $p$, and the entry is the value and priority stored at $p$ when $p$ occurs. -/
public def split {κ : Type u} {ν : Type v} [LinearOrder κ] (pivot : κ) :
    Tree κ ν → SplitResult κ ν
  | .empty => ⟨.empty, none, .empty⟩
  | .node left key value priority right =>
      if key < pivot then
        let result := split pivot right
        ⟨.node left key value priority result.less, result.found, result.greater⟩
      else if pivot < key then
        let result := split pivot left
        ⟨result.less, result.found,
          .node result.greater key value priority right⟩
      else ⟨left, some (value, priority), right⟩

/-- **Treap insertion.** For a key $k$ of a linearly ordered key type, a value $v$, a priority
$p$ and a tree $t$, inserting $k$ with value $v$ and priority $p$ into $t$ splits $t$ at $k$,
drops the entry the split finds at $k$ if any, merges the part below $k$ with the single node
$(k, v, p)$, and then merges the result with the part above $k$; all merges are
priority-guided. -/
public def insert {κ : Type u} {ν : Type v} [LinearOrder κ] (key : κ)
    (value : ν) (priority : Nat) (tree : Tree κ ν) : Tree κ ν :=
  let result := split key tree
  merge (merge result.less (.node .empty key value priority .empty)) result.greater

/-- **Treap deletion.** For a key $k$ of a linearly ordered key type and a tree $t$, deleting
$k$ from $t$ splits $t$ at $k$ and returns the priority-guided merge of the part of the split
below $k$ with the part above $k$; the entry the split finds at $k$, if any, is dropped. -/
public def erase {κ : Type u} {ν : Type v} [LinearOrder κ] (key : κ)
    (tree : Tree κ ν) : Tree κ ν :=
  let result := split key tree
  merge result.less result.greater

@[simp] private theorem allNodes_empty {κ : Type u} {ν : Type v}
    {p : κ → ν → Nat → Prop} : AllNodes p (.empty : Tree κ ν) :=
  trivial

@[simp] private theorem allNodes_node {κ : Type u} {ν : Type v}
    {p : κ → ν → Nat → Prop} {left right : Tree κ ν} {key : κ} {value : ν}
    {priority : Nat} :
    AllNodes p (.node left key value priority right) ↔
      AllNodes p left ∧ p key value priority ∧ AllNodes p right :=
  Iff.rfl

@[simp] private theorem memKey_empty {κ : Type u} {ν : Type v} {key : κ} :
    key ∈ (.empty : Tree κ ν) ↔ False :=
  Iff.rfl

@[simp] private theorem memKey_node {κ : Type u} {ν : Type v} {key rootKey : κ}
    {left right : Tree κ ν} {value : ν} {priority : Nat} :
    key ∈ (Tree.node left rootKey value priority right) ↔
      key ∈ left ∨ key = rootKey ∨ key ∈ right :=
  Iff.rfl

/-- **Treap all-nodes predicate via node membership.** Let $p$ be a predicate on a key, a value
and a natural-number priority, and let $t$ be a tree. Then $p$ holds at every node of $t$ if and
only if $p(k, v, n)$ holds for every key $k$, value $v$ and priority $n$ such that the entry
$(k, v, n)$ occurs as a node of $t$. -/
public theorem allNodes_iff_forall_mem {κ : Type u} {ν : Type v}
    {p : κ → ν → Nat → Prop} {tree : Tree κ ν} :
    AllNodes p tree ↔ ∀ key value priority, MemNode key value priority tree →
      p key value priority := by
  induction tree with
  | empty => simp [AllNodes, MemNode]
  | node left key value priority right ihLeft ihRight =>
    simp only [AllNodes, MemNode, ihLeft, ihRight]
    constructor
    · rintro ⟨hLeft, hRoot, hRight⟩ childKey childValue childPriority
        (h | h | h)
      · exact hLeft _ _ _ h
      · rcases h with ⟨rfl, rfl, rfl⟩
        exact hRoot
      · exact hRight _ _ _ h
    · intro h
      exact ⟨
        fun childKey childValue childPriority hMem => h _ _ _ (Or.inl hMem),
        h key value priority (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
        fun childKey childValue childPriority hMem => h _ _ _ (Or.inr (Or.inr hMem))⟩

/-- **Entry membership implies key membership in a treap.** If a key $k$, value $v$ and
priority $p$ form an entry of a treap tree $t$, that is, some node of $t$ stores exactly $k$,
$v$ and $p$, then $k$ is a key of $t$. -/
public theorem memKey_of_memNode {κ : Type u} {ν : Type v} {key : κ} {value : ν}
    {priority : Nat} {tree : Tree κ ν} (h : MemNode key value priority tree) :
    key ∈ tree := by
  induction tree with
  | empty => exact h.elim
  | node left rootKey rootValue rootPriority right ihLeft ihRight =>
    rcases h with h | ⟨hKey, _, _⟩ | h
    · exact Or.inl (ihLeft h)
    · exact Or.inr (Or.inl hKey)
    · exact Or.inr (Or.inr (ihRight h))

/-- **Inorder contents list the treap's entries.** For every tree $t$, key $k$ and value $v$,
the pair $(k, v)$ occurs in the inorder key-value list of $t$ if and only if $t$ has a node
with key $k$ and value $v$, for some priority. -/
public theorem mem_contents {κ : Type u} {ν : Type v} {key : κ} {value : ν}
    {tree : Tree κ ν} :
    (key, value) ∈ contents tree ↔ ∃ priority, MemNode key value priority tree := by
  induction tree with
  | empty => simp [contents, contentsAux, contents_node, contentsAux, MemNode]
  | node left rootKey rootValue rootPriority right ihLeft ihRight =>
    simp only [contents_node, List.mem_append, List.mem_cons, ihLeft, ihRight]
    constructor
    · rintro (⟨priority, h⟩ | h | ⟨priority, h⟩)
      · exact ⟨priority, Or.inl h⟩
      · simp only [Prod.mk.injEq] at h
        exact ⟨rootPriority, Or.inr (Or.inl ⟨h.1, h.2, rfl⟩)⟩
      · exact ⟨priority, Or.inr (Or.inr h)⟩
    · rintro ⟨priority, h | ⟨hKey, hValue, _⟩ | h⟩
      · exact Or.inl ⟨priority, h⟩
      · exact Or.inr (Or.inl (by simp [hKey, hValue]))
      · exact Or.inr (Or.inr ⟨priority, h⟩)

/-- **Keys occurring in the inorder contents.** For a key $k$ and a tree $t$, some pair
$(k, v)$ occurs in the inorder list of key-value pairs of $t$ if and only if $k$ is the key
of some node of $t$. -/
public theorem key_mem_contents {κ : Type u} {ν : Type v} {key : κ}
    {tree : Tree κ ν} :
    (∃ value, (key, value) ∈ contents tree) ↔ key ∈ tree := by
  induction tree with
  | empty => simp [contents, contentsAux, contents_node, contentsAux]
  | node left rootKey rootValue rootPriority right ihLeft ihRight =>
    simp only [contents_node, List.mem_append, List.mem_cons]
    constructor
    · rintro ⟨value, h | h | h⟩
      · exact Or.inl (ihLeft.mp ⟨value, h⟩)
      · exact Or.inr (Or.inl (Prod.mk.inj h).1)
      · exact Or.inr (Or.inr (ihRight.mp ⟨value, h⟩))
    · rintro (h | rfl | h)
      · rcases ihLeft.mpr h with ⟨value, hValue⟩
        exact ⟨value, Or.inl hValue⟩
      · exact ⟨rootValue, Or.inr (Or.inl rfl)⟩
      · rcases ihRight.mpr h with ⟨value, hValue⟩
        exact ⟨value, Or.inr (Or.inr hValue)⟩

/-- **Treap all-nodes predicate on keys via key membership.** Let $p$ be a predicate on keys and
let $t$ be a tree. Then the key of every node of $t$ satisfies $p$ if and only if $p(k)$ holds
for every key $k$ that occurs in $t$. -/
public theorem allNodes_key_iff {κ : Type u} {ν : Type v} {p : κ → Prop}
    {tree : Tree κ ν} :
    AllNodes (fun key _ _ => p key) tree ↔ ∀ key, key ∈ tree → p key := by
  induction tree with
  | empty => simp [AllNodes]
  | node left key value priority right ihLeft ihRight =>
    simp only [AllNodes, memKey_node, ihLeft, ihRight]
    constructor
    · rintro ⟨hLeft, hKey, hRight⟩ childKey (h | h | h)
      · exact hLeft childKey h
      · simpa [h] using hKey
      · exact hRight childKey h
    · intro h
      exact ⟨fun childKey hMem => h childKey (Or.inl hMem),
        h key (Or.inr (Or.inl rfl)),
        fun childKey hMem => h childKey (Or.inr (Or.inr hMem))⟩

/-- **Inorder key list of a treap.** The inorder key list of a tree $t$ is the list of first
components of the inorder list of key-value pairs of $t$, that is, the keys of $t$ in
inorder. -/
public def keys {κ : Type u} {ν : Type v} (tree : Tree κ ν) : List κ :=
  (contents tree).map Prod.fst

/-- **Inorder keys of a node.** For trees $l$ and $r$, a key $k$, a value $v$ and a priority
$p$, the inorder key list of the node with left subtree $l$, entry $(k, v, p)$ and right
subtree $r$ is the inorder key list of $l$, followed by $k$, followed by the inorder key list
of $r$. -/
public theorem keys_node {κ : Type u} {ν : Type v}
    (left : Tree κ ν) (key : κ) (value : ν) (priority : Nat) (right : Tree κ ν) :
    keys (.node left key value priority right) =
      keys left ++ key :: keys right := by
  simp [keys, contents_node]

/-- **The inorder key list lists exactly the keys of a treap.** For every treap tree $t$ and
key $k$, $k$ occurs in the inorder key list of $t$ if and only if $k$ is a key of $t$. -/
public theorem mem_keys {κ : Type u} {ν : Type v} {key : κ} {tree : Tree κ ν} :
    key ∈ keys tree ↔ key ∈ tree := by
  induction tree with
  | empty => simp [keys, contents, contentsAux, contents_node, contentsAux]
  | node left rootKey value priority right ihLeft ihRight =>
    simp [keys_node, ihLeft, ihRight, or_left_comm]

/-- **Inorder keys of an ordered treap are strictly increasing.** Let the keys come from a
linearly ordered type. If a treap tree $t$ is ordered, then its inorder key list is strictly
increasing: each key in the list is smaller than every key after it. -/
public theorem ordered_keys {κ : Type u} {ν : Type v} [LinearOrder κ]
    {tree : Tree κ ν} (hOrdered : Ordered tree) :
    List.Pairwise (· < ·) (keys tree) := by
  induction tree with
  | empty => simp [keys, contents, contentsAux, contents_node, contentsAux]
  | node left key value priority right ihLeft ihRight =>
    rcases hOrdered with ⟨hLeft, hRight, hKeysLeft, hKeysRight⟩
    rw [keys_node, List.pairwise_append]
    refine ⟨ihLeft hLeft, ?_, ?_⟩
    · rw [List.pairwise_cons]
      exact ⟨fun childKey hMem =>
        (allNodes_key_iff.mp hKeysRight) childKey (mem_keys.mp hMem), ihRight hRight⟩
    · intro leftKey hLeftMem rightKey hRightMem
      rw [List.mem_cons] at hRightMem
      rcases hRightMem with rfl | hRightMem
      · exact (allNodes_key_iff.mp hKeysLeft) leftKey (mem_keys.mp hLeftMem)
      · exact lt_trans
          ((allNodes_key_iff.mp hKeysLeft) leftKey (mem_keys.mp hLeftMem))
          ((allNodes_key_iff.mp hKeysRight) rightKey (mem_keys.mp hRightMem))

/-- **Treap keys are distinct.** For a linearly ordered key type, if a tree is ordered as a
binary search tree (at every node, every key in the left subtree is smaller and every key in
the right subtree is larger than the node's key), then its inorder key list has no
duplicates. -/
public theorem keys_nodup {κ : Type u} {ν : Type v} [LinearOrder κ]
    {tree : Tree κ ν} (hOrdered : Ordered tree) : (keys tree).Nodup :=
  (ordered_keys hOrdered).nodup

/-- **Treap lookup finds exactly the stored entries.** Let $t$ be a tree with keys in a linearly
ordered type that is ordered as a binary search tree (every key in a left subtree is smaller and
every key in a right subtree is larger than the node's key). For every key $k$ and value $v$,
looking up $k$ in $t$ returns $v$ if and only if $t$ has a node with key $k$ and value $v$, for
some priority. -/
public theorem lookup_eq_some_iff {κ : Type u} {ν : Type v} [LinearOrder κ]
    {query : κ} {value : ν} {tree : Tree κ ν} (hOrdered : Ordered tree) :
    lookup query tree = some value ↔ ∃ priority, MemNode query value priority tree := by
  induction tree with
  | empty => simp [lookup, MemNode]
  | node left key rootValue rootPriority right ihLeft ihRight =>
    rcases hOrdered with ⟨hLeft, hRight, hKeysLeft, hKeysRight⟩
    by_cases hQuery : query < key
    · have hNotRight : ¬query ∈ right := by
        intro hMem
        exact (lt_asymm hQuery ((allNodes_key_iff.mp hKeysRight) query hMem)).elim
      have hNotEq : query ≠ key := ne_of_lt hQuery
      have hNoRight : ∀ priority, ¬MemNode query value priority right :=
        fun _ hMem => hNotRight (memKey_of_memNode hMem)
      simp [lookup, hQuery, ihLeft hLeft, MemNode, hNoRight, hNotEq]
    · by_cases hKey : key < query
      · have hNotLeft : ¬query ∈ left := by
          intro hMem
          exact (lt_asymm hKey ((allNodes_key_iff.mp hKeysLeft) query hMem)).elim
        have hNotEq : query ≠ key := ne_of_gt hKey
        have hNoLeft : ∀ priority, ¬MemNode query value priority left :=
          fun _ hMem => hNotLeft (memKey_of_memNode hMem)
        simp [lookup, hQuery, hKey, ihRight hRight, MemNode, hNoLeft, hNotEq]
      · have hEq : query = key := le_antisymm (le_of_not_gt hKey) (le_of_not_gt hQuery)
        subst query
        have hRootNotLeft : ¬key ∈ left := by
          intro hMem
          exact (lt_irrefl key ((allNodes_key_iff.mp hKeysLeft) key hMem)).elim
        have hRootNotRight : ¬key ∈ right := by
          intro hMem
          exact (lt_irrefl key ((allNodes_key_iff.mp hKeysRight) key hMem)).elim
        have hNoLeft : ∀ priority, ¬MemNode key value priority left :=
          fun _ hMem => hRootNotLeft (memKey_of_memNode hMem)
        have hNoRight : ∀ priority, ¬MemNode key value priority right :=
          fun _ hMem => hRootNotRight (memKey_of_memNode hMem)
        simp [lookup, MemNode, hNoLeft, hNoRight, eq_comm]

/-- **Treap lookup agrees with the inorder contents.** Let $t$ be a tree with keys in a linearly
ordered type that is ordered as a binary search tree (every key in a left subtree is smaller and
every key in a right subtree is larger than the node's key). For every key $k$ and value $v$,
looking up $k$ in $t$ returns $v$ if and only if the pair $(k, v)$ occurs in the inorder
key-value list of $t$. -/
public theorem lookup_contents {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {value : ν} {tree : Tree κ ν} (hOrdered : Ordered tree) :
    lookup key tree = some value ↔ (key, value) ∈ contents tree := by
  rw [lookup_eq_some_iff hOrdered, mem_contents]

/-- **Costed lookup returns the ordinary lookup result.** For every tree $t$ with keys in a
linearly ordered type and every key $k$, the value component of the costed lookup of $k$ in $t$
(ignoring the visit count) equals the result of looking up $k$ in $t$. -/
public theorem lookupWithCost_result {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {tree : Tree κ ν} : (lookupWithCost key tree).1 = lookup key tree := by
  induction tree with
  | empty => rfl
  | node left rootKey value priority right ihLeft ihRight =>
    simp only [lookupWithCost, lookup]
    split_ifs <;> simp_all

/-- **Lookup cost is at most the tree size.** For every tree $t$ with keys in a linearly ordered
type and every key $k$, the number of nodes visited by the costed lookup of $k$ in $t$ is at most
the number of nodes of $t$. -/
public theorem lookupWithCost_le_size {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {tree : Tree κ ν} : (lookupWithCost key tree).2 ≤ size tree := by
  induction tree with
  | empty => simp [lookupWithCost, size]
  | node left rootKey value priority right ihLeft ihRight =>
    simp only [lookupWithCost]
    split_ifs <;> simp_all [size] <;> omega

/-- **The root of a heap-ordered tree has minimal priority.** If a nonempty tree whose root
has priority $p$ is heap-ordered, then every node of the tree, the root included, has
priority at least $p$. -/
public theorem heap_root_min {κ : Type u} {ν : Type v} {left right : Tree κ ν}
    {key : κ} {value : ν} {priority : Nat}
    (hHeap : HeapOrdered (.node left key value priority right)) :
    AllNodes (fun _ _ childPriority => priority ≤ childPriority)
      (.node left key value priority right) := by
  rcases hHeap with ⟨_, _, hLeft, hRight⟩
  exact ⟨hLeft, le_rfl, hRight⟩

private theorem allNodes_merge {κ : Type u} {ν : Type v}
    {p : κ → ν → Nat → Prop} (left right : Tree κ ν) :
    AllNodes p (merge left right) ↔ AllNodes p left ∧ AllNodes p right := by
  induction left, right using merge.induct with
  | case1 right => simp [merge, AllNodes]
  | case2 left hLeft => cases left <;> simp_all [merge, AllNodes]
  | case3 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, AllNodes, ih, and_assoc, and_left_comm]
  | case4 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, AllNodes, ih, and_assoc, and_left_comm]

/-- **Keys of a merged treap.** For all trees $l$ and $r$ and every key $k$, $k$ is the key of
some node of the merge of $l$ and $r$ if and only if $k$ is the key of some node of $l$ or of
some node of $r$. -/
public theorem memKey_merge {κ : Type u} {ν : Type v} {key : κ}
    (left right : Tree κ ν) :
    key ∈ merge left right ↔ key ∈ left ∨ key ∈ right := by
  induction left, right using merge.induct with
  | case1 right => simp [merge]
  | case2 left hLeft => cases left <;> simp_all [merge]
  | case3 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, ih, or_assoc, or_left_comm]
  | case4 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, ih, or_assoc, or_left_comm]

/-- **Treap merge concatenates inorder contents.** For trees $l$ and $r$, the inorder list of
key-value pairs of the priority-guided merge of $l$ and $r$ is the inorder list of $l$ followed
by the inorder list of $r$. -/
public theorem contents_merge {κ : Type u} {ν : Type v} (left right : Tree κ ν) :
    contents (merge left right) = contents left ++ contents right := by
  induction left, right using merge.induct with
  | case1 right => simp [merge, contents, contentsAux, contents_node]
  | case2 left hLeft => cases left <;> simp_all [merge, contents, contentsAux, contents_node]
  | case3 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, contents_node, ih, List.append_assoc]
  | case4 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, contents_node, ih, List.append_assoc]

/-- **Separated treap trees.** For keys equipped with a binary relation $<$, two trees $L$
and $R$ are separated when $a < b$ for every key $a$ occurring at a node of $L$ and every
key $b$ occurring at a node of $R$. -/
public def Separated {κ : Type u} {ν : Type v} [LT κ]
    (left right : Tree κ ν) : Prop :=
  ∀ leftKey, leftKey ∈ left → ∀ rightKey, rightKey ∈ right → leftKey < rightKey

/-- **Treap merge preserves search-tree order.** Let the keys come from a linearly ordered
type. If treap trees $L$ and $R$ are both ordered and every key of $L$ is smaller than every
key of $R$, then the merge of $L$ and $R$ is ordered. -/
public theorem ordered_merge {κ : Type u} {ν : Type v} [LinearOrder κ]
    (left right : Tree κ ν) (hLeft : Ordered left) (hRight : Ordered right)
    (hSeparated : Separated left right) : Ordered (merge left right) := by
  induction left, right using merge.induct with
  | case1 right => simpa [merge] using hRight
  | case2 left hNotEmpty => cases left <;> simp_all [merge]
  | case3 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    rcases hLeft with ⟨hLeftLeft, hLeftRight, hKeysLeft, hKeysRight⟩
    have hSeparatedRight :
        Separated leftRight (.node rightLeft rightKey rightValue rightPriority rightRight) :=
      fun key hKey => hSeparated key (Or.inr (Or.inr hKey))
    have hRootBelowRight :
        AllNodes (fun key _ _ => leftKey < key)
          (.node rightLeft rightKey rightValue rightPriority rightRight) :=
      allNodes_iff_forall_mem.mpr (fun key value priority hMem =>
        hSeparated leftKey (Or.inr (Or.inl rfl)) key (memKey_of_memNode hMem))
    simp only [merge, hPriority]
    exact ⟨hLeftLeft, ih hLeftRight hRight hSeparatedRight, hKeysLeft,
      (allNodes_merge leftRight
        (.node rightLeft rightKey rightValue rightPriority rightRight)).mpr
          ⟨hKeysRight, hRootBelowRight⟩⟩
  | case4 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    rcases hRight with ⟨hRightLeft, hRightRight, hKeysLeft, hKeysRight⟩
    have hSeparatedLeft :
        Separated (.node leftLeft leftKey leftValue leftPriority leftRight) rightLeft :=
      fun key hKey rightKey hRightKey => hSeparated key hKey rightKey (Or.inl hRightKey)
    have hLeftBelowRoot :
        AllNodes (fun key _ _ => key < rightKey)
          (.node leftLeft leftKey leftValue leftPriority leftRight) :=
      allNodes_iff_forall_mem.mpr (fun key value priority hMem =>
        hSeparated key (memKey_of_memNode hMem) rightKey (Or.inr (Or.inl rfl)))
    simp only [merge, hPriority]
    exact ⟨ih hLeft hRightLeft hSeparatedLeft, hRightRight,
      (allNodes_merge
        (.node leftLeft leftKey leftValue leftPriority leftRight) rightLeft).mpr
          ⟨hLeftBelowRoot, hKeysLeft⟩, hKeysRight⟩

/-- **Merging preserves heap order.** If two trees $l$ and $r$ are both heap-ordered in their
priorities, then the priority-guided merge of $l$ and $r$ is heap-ordered. -/
public theorem heapOrdered_merge {κ : Type u} {ν : Type v}
    (left right : Tree κ ν) (hLeft : HeapOrdered left)
    (hRight : HeapOrdered right) : HeapOrdered (merge left right) := by
  induction left, right using merge.induct with
  | case1 right => simpa [merge] using hRight
  | case2 left hNotEmpty => cases left <;> simp_all [merge]
  | case3 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    rcases hLeft with ⟨hLeftLeft, hLeftRight, hPriorityLeft, hPriorityRight⟩
    have hRootRight := heap_root_min hRight
    have hPriorityAllRight :
        AllNodes (fun _ _ priority => leftPriority ≤ priority)
          (.node rightLeft rightKey rightValue rightPriority rightRight) :=
      allNodes_iff_forall_mem.mpr (fun key value priority hMem =>
        le_trans hPriority
          (allNodes_iff_forall_mem.mp hRootRight key value priority hMem))
    simp only [merge, hPriority]
    exact ⟨hLeftLeft, ih hLeftRight hRight, hPriorityLeft,
      (allNodes_merge leftRight
        (.node rightLeft rightKey rightValue rightPriority rightRight)).mpr
          ⟨hPriorityRight, hPriorityAllRight⟩⟩
  | case4 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    rcases hRight with ⟨hRightLeft, hRightRight, hPriorityLeft, hPriorityRight⟩
    have hRightLeLeft : rightPriority ≤ leftPriority := Nat.le_of_lt (Nat.lt_of_not_ge hPriority)
    have hRootLeft := heap_root_min hLeft
    have hPriorityAllLeft :
        AllNodes (fun _ _ priority => rightPriority ≤ priority)
          (.node leftLeft leftKey leftValue leftPriority leftRight) :=
      allNodes_iff_forall_mem.mpr (fun key value priority hMem =>
        le_trans hRightLeLeft
          (allNodes_iff_forall_mem.mp hRootLeft key value priority hMem))
    simp only [merge, hPriority]
    exact ⟨ih hLeft hRightLeft, hRightRight,
      (allNodes_merge
        (.node leftLeft leftKey leftValue leftPriority leftRight) rightLeft).mpr
          ⟨hPriorityAllLeft, hPriorityLeft⟩, hPriorityRight⟩

private theorem split_allNodes {κ : Type u} {ν : Type v} [LinearOrder κ]
    {p : κ → ν → Nat → Prop} {pivot : κ} {tree : Tree κ ν}
    (hAll : AllNodes p tree) :
    AllNodes p (split pivot tree).less ∧ AllNodes p (split pivot tree).greater := by
  induction tree with
  | empty => simp [split]
  | node left key value priority right ihLeft ihRight =>
    rcases hAll with ⟨hAllLeft, hRoot, hAllRight⟩
    by_cases hKey : key < pivot
    · have ih := ihRight hAllRight
      simp [split, hKey, hAllLeft, hRoot, ih]
    · by_cases hPivot : pivot < key
      · have ih := ihLeft hAllLeft
        simp [split, hKey, hPivot, hAllRight, hRoot, ih]
      · simp [split, hKey, hPivot, hAllLeft, hAllRight]

/-- **Treap split preserves search-tree order.** Let the keys come from a linearly ordered
type and let $t$ be an ordered treap tree. For every pivot key $k$, the lower tree and the
upper tree produced by splitting $t$ at $k$ are both ordered. -/
public theorem ordered_split {κ : Type u} {ν : Type v} [LinearOrder κ]
    {pivot : κ} {tree : Tree κ ν} (hOrdered : Ordered tree) :
    Ordered (split pivot tree).less ∧ Ordered (split pivot tree).greater := by
  induction tree with
  | empty => simp [split, Ordered]
  | node left key value priority right ihLeft ihRight =>
    rcases hOrdered with ⟨hOrderedLeft, hOrderedRight, hKeysLeft, hKeysRight⟩
    by_cases hKey : key < pivot
    · rcases ihRight hOrderedRight with ⟨hLess, hGreater⟩
      have hInherited := split_allNodes (pivot := pivot) hKeysRight
      simp [split, hKey, Ordered, hOrderedLeft, hLess, hGreater, hKeysLeft,
        hInherited.1]
    · by_cases hPivot : pivot < key
      · rcases ihLeft hOrderedLeft with ⟨hLess, hGreater⟩
        have hInherited := split_allNodes (pivot := pivot) hKeysLeft
        simp [split, hKey, hPivot, Ordered, hOrderedRight, hLess, hGreater,
          hKeysRight, hInherited.2]
      · simp [split, hKey, hPivot, hOrderedLeft, hOrderedRight]

/-- **Treap split preserves heap order.** Let the keys come from a linearly ordered type and let
$t$ be a heap-ordered treap tree. For every pivot key $k$, the lower tree and the upper tree
produced by splitting $t$ at $k$ are both heap-ordered. -/
public theorem heapOrdered_split {κ : Type u} {ν : Type v} [LinearOrder κ]
    {pivot : κ} {tree : Tree κ ν} (hHeap : HeapOrdered tree) :
    HeapOrdered (split pivot tree).less ∧ HeapOrdered (split pivot tree).greater := by
  induction tree with
  | empty => simp [split, HeapOrdered]
  | node left key value priority right ihLeft ihRight =>
    rcases hHeap with ⟨hHeapLeft, hHeapRight, hPriorityLeft, hPriorityRight⟩
    by_cases hKey : key < pivot
    · rcases ihRight hHeapRight with ⟨hLess, hGreater⟩
      have hInherited := split_allNodes (pivot := pivot) hPriorityRight
      simp [split, hKey, HeapOrdered, hHeapLeft, hLess, hGreater, hPriorityLeft,
        hInherited.1]
    · by_cases hPivot : pivot < key
      · rcases ihLeft hHeapLeft with ⟨hLess, hGreater⟩
        have hInherited := split_allNodes (pivot := pivot) hPriorityLeft
        simp [split, hKey, hPivot, HeapOrdered, hHeapRight, hLess, hGreater,
          hPriorityRight, hInherited.2]
      · simp [split, hKey, hPivot, hHeapLeft, hHeapRight]

/-- **Split bounds for an ordered treap.** Let the keys come from a linear order and let $T$ be
an ordered tree. For every pivot $p$, every key of the lower tree obtained by splitting $T$ at
$p$ is strictly less than $p$, and every key of the upper tree is strictly greater than $p$. -/
public theorem split_bounds {κ : Type u} {ν : Type v} [LinearOrder κ]
    {pivot : κ} {tree : Tree κ ν} (hOrdered : Ordered tree) :
    AllNodes (fun key _ _ => key < pivot) (split pivot tree).less ∧
      AllNodes (fun key _ _ => pivot < key) (split pivot tree).greater := by
  induction tree with
  | empty => simp [split]
  | node left key value priority right ihLeft ihRight =>
    rcases hOrdered with ⟨hOrderedLeft, hOrderedRight, hKeysLeft, hKeysRight⟩
    by_cases hKey : key < pivot
    · rcases ihRight hOrderedRight with ⟨hLess, hGreater⟩
      have hLeftBelow : AllNodes (fun childKey _ _ => childKey < pivot) left :=
        allNodes_iff_forall_mem.mpr (fun childKey childValue childPriority hMem =>
          lt_trans (allNodes_iff_forall_mem.mp hKeysLeft _ _ _ hMem) hKey)
      simp [split, hKey, hLeftBelow, hLess, hGreater]
    · by_cases hPivot : pivot < key
      · rcases ihLeft hOrderedLeft with ⟨hLess, hGreater⟩
        have hRightAbove : AllNodes (fun childKey _ _ => pivot < childKey) right :=
          allNodes_iff_forall_mem.mpr (fun childKey childValue childPriority hMem =>
            lt_trans hPivot (allNodes_iff_forall_mem.mp hKeysRight _ _ _ hMem))
        simp [split, hKey, hPivot, hRightAbove, hLess, hGreater]
      · have hEq : key = pivot := le_antisymm (le_of_not_gt hPivot) (le_of_not_gt hKey)
        subst key
        simp [split, hKeysLeft, hKeysRight]

/-- **Splitting a treap preserves validity.** Let the keys come from a linear order. If a tree
is a valid treap, then for every pivot $p$, both the lower tree and the upper tree obtained by
splitting it at $p$ are valid treaps. -/
public theorem valid_split {κ : Type u} {ν : Type v} [LinearOrder κ]
    {pivot : κ} {tree : Tree κ ν} (hValid : Valid tree) :
    Valid (split pivot tree).less ∧ Valid (split pivot tree).greater := by
  rcases hValid with ⟨hOrdered, hHeap⟩
  rcases ordered_split hOrdered with ⟨hOrderedLess, hOrderedGreater⟩
  rcases heapOrdered_split hHeap with ⟨hHeapLess, hHeapGreater⟩
  exact ⟨⟨hOrderedLess, hHeapLess⟩, ⟨hOrderedGreater, hHeapGreater⟩⟩

/-- **Merging separated treaps preserves validity.** Let the keys come from a linear order. If
$L$ and $R$ are valid treaps and every key of $L$ is strictly less than every key of $R$, then
the merge of $L$ and $R$ is a valid treap. -/
public theorem valid_merge {κ : Type u} {ν : Type v} [LinearOrder κ]
    {left right : Tree κ ν} (hLeft : Valid left) (hRight : Valid right)
    (hSeparated : Separated left right) : Valid (merge left right) :=
  ⟨ordered_merge left right hLeft.1 hRight.1 hSeparated,
    heapOrdered_merge left right hLeft.2 hRight.2⟩

/-- **Inserting into a treap preserves validity.** Let the keys come from a linear order. If a
tree is a valid treap, that is, its keys are in strict binary-search-tree order and its
priorities are in min-heap order, then for every key $k$, value $v$ and natural-number
priority $q$, the tree obtained by inserting $k$ with value $v$ and priority $q$ is again a
valid treap. -/
public theorem valid_insert {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {value : ν} {priority : Nat} {tree : Tree κ ν}
    (hValid : Valid tree) : Valid (insert key value priority tree) := by
  let result := split key tree
  have hSplit := valid_split (pivot := key) hValid
  have hBounds := split_bounds (pivot := key) hValid.1
  have hSingleton : Valid (.node .empty key value priority .empty : Tree κ ν) := by
    simp [Valid, Ordered, HeapOrdered, AllNodes]
  have hLessSingleton :
      Separated result.less (.node .empty key value priority .empty) := by
    intro leftKey hLeftKey rightKey hRightKey
    have hRightEq : rightKey = key := by simpa using hRightKey
    subst rightKey
    exact (allNodes_key_iff.mp hBounds.1) leftKey hLeftKey
  have hFirstValid :
      Valid (merge result.less (.node .empty key value priority .empty)) :=
    valid_merge hSplit.1 hSingleton hLessSingleton
  have hFirstGreater :
      Separated (merge result.less (.node .empty key value priority .empty))
        result.greater := by
    intro leftKey hLeftKey rightKey hRightKey
    rcases (memKey_merge result.less
      (.node .empty key value priority .empty)).mp hLeftKey with hLess | hRoot
    · exact lt_trans ((allNodes_key_iff.mp hBounds.1) leftKey hLess)
        ((allNodes_key_iff.mp hBounds.2) rightKey hRightKey)
    · have hLeftEq : leftKey = key := by simpa using hRoot
      subst leftKey
      exact (allNodes_key_iff.mp hBounds.2) rightKey hRightKey
  change Valid (merge (merge result.less (.node .empty key value priority .empty))
    result.greater)
  exact valid_merge hFirstValid hSplit.2 hFirstGreater

/-- **Erasing from a treap preserves validity.** Let the keys come from a linear order. If a
tree is a valid treap, that is, its keys are in strict binary-search-tree order and its
priorities are in min-heap order, then for every key $k$ the tree obtained by erasing $k$ from
it is again a valid treap. -/
public theorem valid_erase {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {tree : Tree κ ν} (hValid : Valid tree) :
    Valid (erase key tree) := by
  let result := split key tree
  have hSplit := valid_split (pivot := key) hValid
  have hBounds := split_bounds (pivot := key) hValid.1
  have hSeparated : Separated result.less result.greater := by
    intro leftKey hLeftKey rightKey hRightKey
    exact lt_trans ((allNodes_key_iff.mp hBounds.1) leftKey hLeftKey)
      ((allNodes_key_iff.mp hBounds.2) rightKey hRightKey)
  change Valid (merge result.less result.greater)
  exact valid_merge hSplit.1 hSplit.2 hSeparated

/-- **Treap inorder contents split at a pivot.** Let the keys come from a linearly ordered type,
let $t$ be a tree and $k$ a pivot key, and let splitting $t$ at $k$ produce a lower tree $L$, an
optional value-priority pair found at $k$, and an upper tree $G$. Then the inorder list of
key-value pairs of $t$ is the inorder list of $L$, followed by $(k, v)$ if the split found a pair
with value $v$ (and by nothing if it found none), followed by the inorder list of $G$. -/
public theorem contents_split {κ : Type u} {ν : Type v} [LinearOrder κ]
    (pivot : κ) (tree : Tree κ ν) :
    contents tree = contents (split pivot tree).less ++
      ((split pivot tree).found.map fun result => (pivot, result.1)).toList ++
      contents (split pivot tree).greater := by
  induction tree with
  | empty => simp [split, contents, contentsAux, contents_node]
  | node left key value priority right ihLeft ihRight =>
    by_cases hKey : key < pivot
    · simp [split, hKey, contents_node, ihRight, List.append_assoc]
    · by_cases hPivot : pivot < key
      · simp [split, hKey, hPivot, contents_node, ihLeft, List.append_assoc]
      · have hEq : key = pivot := le_antisymm (le_of_not_gt hPivot) (le_of_not_gt hKey)
        subst key
        simp only [split, contents, contentsAux, contents_node]
        rw [← List.singleton_append, contentsAux_append]
        conv_lhs => rw [← List.nil_append [(pivot, value)], contentsAux_append]
        rw [List.append_assoc, List.singleton_append]
        simp

/-- **Treap inorder contents after insertion.** Let the keys come from a linearly ordered type,
let $t$ be a tree, $k$ a key, $v$ a value and $n$ a natural-number priority, and let $L$ and $G$
be the lower and upper trees produced by splitting $t$ at $k$. Then the inorder list of key-value
pairs of the tree obtained by inserting $k$ with value $v$ and priority $n$ into $t$ is the
inorder list of $L$, followed by $(k, v)$, followed by the inorder list of $G$. -/
public theorem contents_insert {κ : Type u} {ν : Type v} [LinearOrder κ]
    (key : κ) (value : ν) (priority : Nat) (tree : Tree κ ν) :
    contents (insert key value priority tree) =
      contents (split key tree).less ++ (key, value) :: contents (split key tree).greater := by
  simp only [insert]
  rw [contents_merge, contents_merge, contents_node]
  simp [contents, contentsAux, List.append_assoc]

/-- **Treap inorder contents after erasure.** Let the keys come from a linearly ordered type, let
$t$ be a tree and $k$ a key, and let $L$ and $G$ be the lower and upper trees produced by
splitting $t$ at $k$. Then the inorder list of key-value pairs of the tree obtained by erasing
$k$ from $t$ is the inorder list of $L$ followed by the inorder list of $G$. -/
public theorem contents_erase {κ : Type u} {ν : Type v} [LinearOrder κ]
    (key : κ) (tree : Tree κ ν) :
    contents (erase key tree) =
      contents (split key tree).less ++ contents (split key tree).greater := by
  simp [erase, contents_merge]

/-- **Treap lookup after insertion.** Let $t$ be a valid treap with keys in a linearly ordered
type, that is, $t$ is ordered as a binary search tree by key and as a min-heap by priority. For
every key $k$, value $v$ and priority $p \in \mathbb{N}$, looking up $k$ in the tree obtained by
inserting $k$ with value $v$ and priority $p$ into $t$ returns $v$. -/
public theorem lookup_insert_eq {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {value : ν} {priority : Nat} {tree : Tree κ ν}
    (hValid : Valid tree) : lookup key (insert key value priority tree) = some value := by
  apply (lookup_contents (valid_insert hValid).1).mpr
  rw [contents_insert]
  simp

/-- **Erased keys are not found.** Let $t$ be a valid treap with keys in a linearly ordered type,
that is, $t$ is ordered as a binary search tree by key and as a min-heap by priority. For every
key $k$, looking up $k$ in the tree obtained by erasing $k$ from $t$ returns no value. -/
public theorem lookup_erase_eq_none {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {tree : Tree κ ν} (hValid : Valid tree) :
    lookup key (erase key tree) = none := by
  have hValidErase := valid_erase (key := key) hValid
  have hBounds := split_bounds (pivot := key) hValid.1
  cases hLookup : lookup key (erase key tree) with
  | none => rfl
  | some value =>
    have hMem := (lookup_contents hValidErase.1).mp hLookup
    rw [contents_erase, List.mem_append] at hMem
    rcases hMem with hLess | hGreater
    · have hKeyMem : key ∈ (split key tree).less :=
        key_mem_contents.mp ⟨value, hLess⟩
      exact (lt_irrefl key ((allNodes_key_iff.mp hBounds.1) key hKeyMem)).elim
    · have hKeyMem : key ∈ (split key tree).greater :=
        key_mem_contents.mp ⟨value, hGreater⟩
      exact (lt_irrefl key ((allNodes_key_iff.mp hBounds.2) key hKeyMem)).elim

end Tree
end Treap
end Cslib.Algorithms.Lean
