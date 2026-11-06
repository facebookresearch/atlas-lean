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

/-- **Membership in a binary tree.** A key $x$ belongs to a binary tree $T$ when it is the key
of some node of $T$: no key belongs to the empty tree, and $x$ belongs to a node with key $k$,
left subtree $L$ and right subtree $R$ exactly when $x$ belongs to $L$, $x = k$, or $x$
belongs to $R$.

This membership does not use the search-tree ordering. -/
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

/-- **Inorder traversal of a binary tree with an accumulator.** For a binary tree $t$ and a list
$s$, the accumulated traversal of the empty tree onto $s$ is $s$, and the accumulated traversal of
a node with key $k$, left subtree $L$ and right subtree $R$ onto $s$ is the accumulated traversal
of $L$ onto the list consisting of $k$ followed by the accumulated traversal of $R$ onto $s$.

Unfolding the recursion, the result is the inorder traversal of $t$ followed by $s$. -/
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

/-- **Inorder traversal of a binary tree.** The inorder traversal of a binary tree $t$ is the
accumulated inorder traversal of $t$ onto the empty list. Equivalently, the empty tree gives the
empty list, and a node with key $k$, left subtree $L$ and right subtree $R$ gives the inorder
traversal of $L$, then $k$, then the inorder traversal of $R$. -/
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

/-- **A predicate holding at every key of a binary tree.** For a predicate $p$ on a type $\alpha$,
the empty binary tree satisfies "every key satisfies $p$", and a node with key $k$, left subtree
$L$ and right subtree $R$ satisfies it exactly when $L$ satisfies it, $p(k)$ holds and $R$
satisfies it. -/
public def All {α : Type u} (p : α → Prop) : BinaryTree α → Prop
  | .nil => True
  | .node key left right => All p left ∧ p key ∧ All p right

/-- **Ordered binary trees.** Let $\alpha$ be a type with a relation $<$. The empty tree is
ordered, and a binary tree with root key $k$, left subtree $L$ and right subtree $R$ is ordered
when $L$ and $R$ are ordered, every key of $L$ is less than $k$, and $k$ is less than every key
of $R$. -/
public def Ordered {α : Type u} [LT α] : BinaryTree α → Prop
  | .nil => True
  | .node key left right =>
      Ordered left ∧ Ordered right ∧ All (· < key) left ∧ All (key < ·) right

/--
**Search in a binary search tree.** For a linearly ordered type $\alpha$, a key $x \in \alpha$ and
a binary tree $t$ with keys in $\alpha$, the search for $x$ in $t$ returns a Boolean: false if $t$
is empty, and if $t$ is a node with key $k$, left subtree $L$ and right subtree $R$, the search
for $x$ in $L$ when $x < k$, the search for $x$ in $R$ when $k < x$, and true otherwise.

Unlike the index of a key in a binary tree, which encodes the root-to-node path as a positive
binary number, this search returns only whether the key was found.
-/
public def contains {α : Type u} [LinearOrder α] (x : α) : BinaryTree α → Bool
  | .nil => false
  | .node key left right =>
      if x < key then contains x left
      else if key < x then contains x right
      else true

/-- **Insertion into a binary search tree.** For a linearly ordered type $\alpha$, a key
$x \in \alpha$ and a binary tree $t$ with keys in $\alpha$, inserting $x$ into the empty tree gives
the single node with key $x$ and empty subtrees; inserting $x$ into a node with key $k$, left
subtree $L$ and right subtree $R$ inserts $x$ into $L$ when $x < k$, inserts $x$ into $R$ when
$k < x$, and returns the node unchanged when $x = k$. -/
public def insert {α : Type u} [LinearOrder α] (x : α) : BinaryTree α → BinaryTree α
  | .nil => .node x .nil .nil
  | tree@(.node key left right) =>
      if x < key then .node key (insert x left) right
      else if key < x then .node key left (insert x right)
      else tree

/-- **Rank of a key in a binary tree.** For a linearly ordered type $\alpha$, a key
$x \in \alpha$ and a binary tree $t$ with keys in $\alpha$, the rank of $x$ in $t$ is the number
of positions of the inorder traversal of $t$ whose entry is strictly less than $x$. -/
public def rank {α : Type u} [LinearOrder α] (x : α) (tree : BinaryTree α) : Nat :=
  ((inorder tree).filter (· < x)).length

/-- **Inorder selection in a binary tree.** For a binary tree $t$ and a natural number $i$,
selecting index $i$ in $t$ returns the entry at zero-based position $i$ of the inorder traversal
of $t$ when $i$ is less than the length of that traversal, and returns nothing otherwise. -/
public def select {α : Type u} (tree : BinaryTree α) (index : Nat) : Option α :=
  (inorder tree)[index]?

/-- **Binary search tree built from a list.** For a linearly ordered type $\alpha$, the binary tree
built from a list $[x_1, \ldots, x_n]$ of elements of $\alpha$ is obtained from the empty tree by
inserting $x_n$, then $x_{n-1}$, and so on down to $x_1$, using binary search tree insertion; the
empty list gives the empty tree. -/
public def fromList {α : Type u} [LinearOrder α] : List α → BinaryTree α
  | [] => .nil
  | x :: xs => insert x (fromList xs)

/-- **A predicate holds at all keys of a binary tree iff it holds at all its members.** For a
type $\alpha$, a predicate $p$ on $\alpha$ and a binary tree $t$ with keys in $\alpha$, every key
of $t$ satisfies $p$ in the recursive sense (the empty tree qualifies, and a node qualifies when
its left subtree qualifies, its key satisfies $p$ and its right subtree qualifies) if and only if
$p(x)$ holds for every $x$ that is a member of $t$. -/
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

/-- **Membership in the inorder traversal of a binary tree.** For every binary tree $T$ and every
key $x$, $x$ occurs in the inorder traversal of $T$ if and only if $x$ lies in $T$. -/
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

/-- **Membership after insertion into a binary search tree.** Let the keys be linearly ordered.
For all keys $x, y$ and every binary tree $T$, $y$ lies in the tree obtained by inserting $x$
into $T$ if and only if $y = x$ or $y$ lies in $T$. -/
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

/-- **Binary search tree insertion preserves order.** Let $\alpha$ be a linearly ordered type.
For every key $x \in \alpha$ and every ordered binary tree $T$ over $\alpha$, the tree obtained
by inserting $x$ into $T$ is ordered. -/
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

/-- **Search in a binary search tree is correct.** For a linearly ordered type $\alpha$, a key
$x \in \alpha$ and a binary tree $t$ with keys in $\alpha$ that is ordered (recursively, every
key in the left subtree of a node is strictly smaller than the node's key and every key in its
right subtree is strictly larger), the comparison search for $x$ in $t$ returns true if and only
if $x$ is a member of $t$. -/
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

/-- **The inorder traversal of an ordered binary tree is strictly increasing.** Let $\alpha$ be
a linearly ordered type. If a binary tree $T$ over $\alpha$ is ordered, then in the inorder
traversal of $T$ every key is less than every key that comes after it. -/
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

/-- **The inorder traversal of a binary search tree has no duplicates.** For a linearly ordered
type $\alpha$ and a binary tree $t$ with keys in $\alpha$ that is ordered (recursively, every key
in the left subtree of a node is strictly smaller than the node's key and every key in its right
subtree is strictly larger), the inorder traversal of $t$ is a list with no repeated entries. -/
public theorem inorder_nodup {α : Type u} [LinearOrder α]
    {tree : BinaryTree α} (hTree : Ordered tree) : (inorder tree).Nodup :=
  (ordered_inorder hTree).nodup

/-- **Binary search trees built from a list are ordered.** Let $\alpha$ be a linearly ordered
type. For every list $xs$ of elements of $\alpha$, the tree obtained from the empty tree by
inserting the elements of $xs$ one at a time, from the last element to the first, is ordered. -/
public theorem ordered_fromList {α : Type u} [LinearOrder α] {xs : List α} :
    Ordered (fromList xs) := by
  induction xs with
  | nil => simp [fromList, Ordered]
  | cons x xs ih => exact ordered_insert ih

/-- **Members of the binary search tree built from a list.** For a linearly ordered type $\alpha$,
a key $x \in \alpha$ and a list $xs$ of elements of $\alpha$, $x$ is a member of the binary tree
built from $xs$ by successive binary search tree insertion if and only if $x$ occurs in $xs$. -/
public theorem mem_fromList {α : Type u} [LinearOrder α] {x : α} {xs : List α} :
    x ∈ fromList xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [fromList]
  | cons y ys ih => simp [fromList, mem_insert, ih]

/-- **The length of the inorder traversal of a binary tree is its number of nodes.** For every
binary tree $T$, the number of nodes of $T$ (each node carries one key, and the empty tree has
none) equals the length of the inorder traversal of $T$. -/
public theorem numNodes_eq_length_inorder {α : Type u} {tree : BinaryTree α} :
    tree.numNodes = (inorder tree).length := by
  induction tree with
  | nil => simp
  | node key left right ihLeft ihRight =>
    simp [ihLeft, ihRight, Nat.add_comm, Nat.add_left_comm]

/-- **Inserting a present key into a binary search tree leaves its size unchanged.** Let the
keys be linearly ordered, and let $T$ be an ordered binary tree. If a key $x$ lies in $T$, then
the tree obtained by inserting $x$ into $T$ has the same number of nodes as $T$. -/
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

/-- **Inserting an absent key into a binary search tree adds one node.** Let the keys be
linearly ordered. For every binary tree $T$ and every key $x$ that does not lie in $T$, the tree
obtained by inserting $x$ into $T$ has one more node than $T$. -/
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

/-- **Rank counts the smaller inorder entries.** For a linearly ordered type $\alpha$, a key
$x \in \alpha$ and a binary tree $t$ with keys in $\alpha$, the rank of $x$ in $t$ equals the
length of the list obtained from the inorder traversal of $t$ by keeping exactly the entries
strictly less than $x$. -/
public theorem rank_eq_count_inorder {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} :
    rank x tree = ((inorder tree).filter (· < x)).length :=
  rfl

/-- **Selection is indexing into the inorder traversal.** For a binary tree $t$ and a natural
number $i$, selecting index $i$ in $t$ gives the same result as looking up zero-based position
$i$ of the inorder traversal of $t$: the entry at that position when $i$ is less than the length
of the traversal, and nothing otherwise. -/
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

/-- **Selecting the rank of a key returns the key.** Let $\alpha$ be a linearly ordered type
and let $t$ be a binary search tree with keys in $\alpha$, that is, at every node each key of the
left subtree is strictly smaller and each key of the right subtree is strictly larger than the
node's key. If $x$ is a key of $t$, then selecting, in $t$, the index equal to the rank of $x$
in $t$ returns $x$. -/
public theorem select_rank {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} (hTree : Ordered tree) (hx : x ∈ tree) :
    select tree (rank x tree) = some x := by
  exact selectList_rank (ordered_inorder hTree) (mem_inorder.mpr hx)

/-- **The rank of a selected key is its index.** Let $\alpha$ be a linearly ordered type and
let $t$ be a binary search tree with keys in $\alpha$, that is, at every node each key of the
left subtree is strictly smaller and each key of the right subtree is strictly larger than the
node's key. If selecting index $i$ in $t$ returns a key $x$, then the rank of $x$ in $t$
equals $i$. -/
public theorem rank_select {α : Type u} [LinearOrder α] {tree : BinaryTree α}
    {index : Nat} {x : α} (hTree : Ordered tree)
    (hSelect : select tree index = some x) : rank x tree = index := by
  exact rankList_select (ordered_inorder hTree) hSelect

end BinarySearchTree
end Cslib.Algorithms.Lean
