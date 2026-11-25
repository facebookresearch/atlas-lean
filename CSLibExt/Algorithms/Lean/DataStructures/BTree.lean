/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.OrderedInsert
public import Mathlib.Data.List.Nodup
public import Mathlib.Order.Defs.LinearOrder

/-!
# B-trees

This module develops B-trees as in CLRS Chapter 18, with set semantics: a tree stores a
finite set of keys, and insertion of an already-present key leaves the tree unchanged.

A raw tree is either a leaf holding a list of keys or an internal node holding a list of
separator keys and a list of children. For minimum degree `t`, the invariant `Valid t mink h`
states that `h` is the height (leaves have height `0` and every leaf occurs at depth `h`, so
the tree is perfectly balanced), every node has at most `2 * t - 1` keys, every non-root node
has at least `t - 1` keys (the root instead satisfies the bound `mink`), and every internal
node with `k` keys has exactly `k + 1` children. The ordering invariant `Ordered` states
that the inorder flattening is strictly increasing; `Ordered.node_keys_pairwise` and
`Ordered.separator_bounds` extract from it the usual facts that the keys at each node are
sorted and that every key in a subtree lies strictly between the separators adjacent to it.

Insertion is a bottom-up, split-returning (overflow-returning) variant: the internal
function `ins` first inserts into a leaf or child, allowing a node to reach `2 * t` keys, and
splits such an overflowing node while returning, yielding either a single tree of the same
height or a pair of trees of the same height together with the median key promoted between
them; `insert` grows a new root exactly when the old root splits. This is not the insertion
algorithm of CLRS (Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*, 3rd
edition, §18.2), which is top-down: it splits every full `2 * t - 1`-key node before
descending into it, so no overflow ever arises. The deviation affects tree shape: for
`t = 2`, inserting `0` into the leaf `[1, 2, 3]` promotes `1` here (the median of the
overflow `[0, 1, 2, 3]`), where CLRS first promotes `2` (splitting `[1, 2, 3]` before
descending). The B-tree invariants and set semantics agree with CLRS Chapter 18; only the
insertion strategy (and hence the resulting shape) differs.
The main lemmas are that `flatten (insert t x tr) = orderedInsert x (flatten tr)` for a valid
ordered tree, that insertion preserves validity and orderedness, and that the search
procedure `contains` agrees with membership.

Deletion is out of scope for this module.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean

/-- **Raw B-trees.** A raw B-tree with keys in a type $\alpha$ is either a leaf, holding a list
of keys, or an internal node, holding a list of separator keys and a list of child raw B-trees.
The type imposes no invariant: that an internal node with $k$ keys has $k + 1$ children, the
bounds on key counts, the balance of the tree and the ordering of the keys are imposed
separately by the structural and ordering invariants of B-trees. -/
public inductive BTree (α : Type u) where
  | leaf (keys : List α) : BTree α
  | node (keys : List α) (children : List (BTree α)) : BTree α

namespace BTree

variable {α : Type u}

/-- **Accumulating flattening of a B-tree.** Given a raw B-tree $T$ and a list $s$, this returns
the inorder traversal of $T$ followed by $s$. For a leaf it is the leaf's key list followed by
$s$. For an internal node with separator keys $k_1, \dots, k_m$ and children $c_0, \dots, c_n$
it is the sequence $c_0, k_1, c_1, k_2, \dots$, in which children and keys alternate starting
with a child until one of the two lists runs out, then the remaining keys or children in
order, and finally $s$; each key contributes itself, and each child contributes its own
accumulating flattening with everything after it as the suffix. In particular every key of
the tree occurs in the result.

The result is built from right to left, so each key is copied only once. -/
public def flattenAux : BTree α → List α → List α
  | .leaf keys, suffix => keys ++ suffix
  | .node keys children, suffix => flattenListAux keys children suffix
where
  flattenListAux : List α → List (BTree α) → List α → List α
    | [], [], suffix => suffix
    | [], child :: children, suffix =>
        flattenAux child (flattenListAux [] children suffix)
    | key :: keys, [], suffix => key :: flattenListAux keys [] suffix
    | key :: keys, child :: children, suffix =>
        flattenAux child (key :: flattenListAux keys children suffix)

/-- **Inorder flattening of a B-tree.** The flattening of a raw B-tree is the list of its keys
defined recursively: for a leaf it is the leaf's key list, and for an internal node with keys
$k_1, k_2, \dots$ and children $c_1, c_2, \dots$ it is the flattening of $c_1$, then $k_1$, then
the flattening of $c_2$, then $k_2$, and so on, alternating while both lists last; whatever
remains of the longer list is then appended in order, each surplus child contributing its
flattening and each surplus key contributing itself. In particular every key of the tree occurs
in the flattening.

The flattening is computed in linear time by an accumulator-passing auxiliary function. -/
public def flatten (tree : BTree α) : List α :=
  flattenAux tree []

private theorem flattenListAux_append_of :
    ∀ (keys : List α) (children : List (BTree α)),
      (∀ child ∈ children, ∀ xs ys : List α,
        flattenAux child (xs ++ ys) = flattenAux child xs ++ ys) →
      ∀ xs ys : List α,
      flattenAux.flattenListAux keys children (xs ++ ys) =
        flattenAux.flattenListAux keys children xs ++ ys := by
  intro keys
  induction keys with
  | nil =>
      intro children hsub xs ys
      induction children with
      | nil => simp [flattenAux.flattenListAux]
      | cons child children ih =>
          have hhead := hsub child (by simp)
          have htail : ∀ c ∈ children, ∀ xs ys : List α,
              flattenAux c (xs ++ ys) = flattenAux c xs ++ ys :=
            fun c hc => hsub c (List.mem_cons_of_mem child hc)
          simp only [flattenAux.flattenListAux]
          rw [ih htail, hhead]
  | cons key keys ih =>
      intro children hsub xs ys
      cases children with
      | nil =>
          simp only [flattenAux.flattenListAux]
          rw [ih [] (fun c hc => by simp at hc), List.cons_append]
      | cons child children =>
          have hhead := hsub child (by simp)
          have htail : ∀ c ∈ children, ∀ xs ys : List α,
              flattenAux c (xs ++ ys) = flattenAux c xs ++ ys :=
            fun c hc => hsub c (List.mem_cons_of_mem child hc)
          simp only [flattenAux.flattenListAux]
          rw [ih children htail, ← List.cons_append]
          exact hhead _ _

private theorem flattenAux_append_aux :
    ∀ (n : Nat) (t : BTree α), sizeOf t ≤ n → ∀ xs ys : List α,
      flattenAux t (xs ++ ys) = flattenAux t xs ++ ys := by
  intro n
  induction n with
  | zero =>
      intro t hle xs ys
      cases t with
      | leaf keys =>
          rw [BTree.leaf.sizeOf_spec] at hle
          omega
      | node keys children =>
          rw [BTree.node.sizeOf_spec] at hle
          omega
  | succ n ih =>
      intro t hle xs ys
      cases t with
      | leaf keys => simp [flattenAux, List.append_assoc]
      | node keys children =>
          have hchild : ∀ child ∈ children, ∀ xs ys : List α,
              flattenAux child (xs ++ ys) = flattenAux child xs ++ ys := by
            intro child hmem xs' ys'
            apply ih child _ xs' ys'
            have hlt := List.sizeOf_lt_of_mem hmem
            rw [BTree.node.sizeOf_spec] at hle
            omega
          simp only [flattenAux]
          exact flattenListAux_append_of keys children hchild xs ys

private theorem flattenAux_append (t : BTree α) (xs ys : List α) :
    flattenAux t (xs ++ ys) = flattenAux t xs ++ ys :=
  flattenAux_append_aux (sizeOf t) t (Nat.le_refl _) xs ys

/-- **The accumulating B-tree flattening is correct.** For every raw B-tree $T$ and every list
$s$, the accumulating flattening of $T$ with suffix $s$ equals the inorder flattening of $T$
followed by $s$. -/
public theorem flattenAux_eq (t : BTree α) (suffix : List α) :
    flattenAux t suffix = flatten t ++ suffix := by
  change flattenAux t suffix = flattenAux t [] ++ suffix
  rw [← flattenAux_append t [] suffix]
  simp

@[simp] public theorem flatten_leaf {keys : List α} :
    flatten (.leaf keys : BTree α) = keys := by
  simp [flatten, flattenAux]

@[simp] public theorem flatten_node_cons {key : α} {keys : List α}
    {child : BTree α} {children : List (BTree α)} :
    flatten (.node (key :: keys) (child :: children)) =
      flatten child ++ key :: flatten (.node keys children) := by
  have h1 : flatten (.node (key :: keys) (child :: children) : BTree α) =
      flattenAux child
        (key :: flattenAux.flattenListAux keys children []) := by
    simp only [flatten, flattenAux, flattenAux.flattenListAux]
  have h2 : flatten (.node keys children : BTree α) =
      flattenAux.flattenListAux keys children [] := by
    simp only [flatten, flattenAux]
  rw [h1, h2, flattenAux_eq]

/-- **Flattening a keyless node, one child at a time.** For a raw B-tree $c$ and a list $C$ of
raw B-trees, the flattening of the node with no keys and child list $c$ followed by $C$ is the
flattening of $c$ followed by the flattening of the node with no keys and child list $C$.

This covers nodes with more children than a well-formed node would have. -/
public theorem flatten_node_nil_cons {child : BTree α}
    {children : List (BTree α)} :
    flatten (.node [] (child :: children) : BTree α) =
      flatten child ++ flatten (.node [] children) := by
  have h1 : flatten (.node [] (child :: children) : BTree α) =
      flattenAux child (flattenAux.flattenListAux [] children []) := by
    simp only [flatten, flattenAux, flattenAux.flattenListAux]
  have h2 : flatten (.node [] children : BTree α) =
      flattenAux.flattenListAux [] children [] := by
    simp only [flatten, flattenAux]
  rw [h1, h2, flattenAux_eq]

/-- **Flattening a childless node, one key at a time.** For a key $k$ and a list of keys $K$, the
flattening of the node with key list $k$ followed by $K$ and no children is $k$ followed by the
flattening of the node with key list $K$ and no children.

This covers nodes with more keys than a well-formed node would have. -/
public theorem flatten_node_cons_nil {key : α} {keys : List α} :
    flatten (.node (key :: keys) [] : BTree α) =
      key :: flatten (.node keys []) := by
  simp only [flatten, flattenAux, flattenAux.flattenListAux]

/-- **Flattening of the empty node.** The flattening of the internal node with no keys and no
children is the empty list. -/
public theorem flatten_node_nil_nil :
    flatten (.node [] [] : BTree α) = [] := by
  simp [flatten, flattenAux, flattenAux.flattenListAux]

public theorem flatten_node_nil {child : BTree α} :
    flatten (.node [] [child] : BTree α) = flatten child := by
  rw [flatten_node_nil_cons, flatten_node_nil_nil, List.append_nil]

public theorem flatten_node_pair {median : α} {left right : BTree α} :
    flatten (.node [median] [left, right] : BTree α) =
      flatten left ++ median :: flatten right := by
  rw [flatten_node_cons, flatten_node_nil]

private theorem mem_flatten_node {x : α} :
    ∀ {keys : List α} {children : List (BTree α)},
      x ∈ flatten (node keys children : BTree α) ↔
        x ∈ keys ∨ ∃ child ∈ children, x ∈ flatten child := by
  intro keys
  induction keys with
  | nil =>
      intro children
      induction children with
      | nil => simp [flatten_node_nil_nil]
      | cons child children ih =>
          rw [flatten_node_nil_cons]
          simp only [List.mem_append, ih, List.mem_cons,
            List.not_mem_nil, false_or]
          constructor
          · rintro (hx | ⟨child', hchild', hx⟩)
            · exact ⟨child, Or.inl rfl, hx⟩
            · exact ⟨child', Or.inr hchild', hx⟩
          · rintro ⟨child', rfl | hchild', hx⟩
            · exact Or.inl hx
            · exact Or.inr ⟨child', hchild', hx⟩
  | cons key keys ih =>
      intro children
      cases children with
      | nil =>
          rw [flatten_node_cons_nil]
          simp only [List.mem_cons]
          rw [ih]
          simp
      | cons child children =>
          rw [flatten_node_cons]
          simp only [List.mem_append, List.mem_cons]
          rw [ih]
          constructor
          · rintro (hx | hx | hx | ⟨child', hchild', hx⟩)
            · exact Or.inr ⟨child, Or.inl rfl, hx⟩
            · exact Or.inl (Or.inl hx)
            · exact Or.inl (Or.inr hx)
            · exact Or.inr ⟨child', Or.inr hchild', hx⟩
          · rintro ((hx | hx) | ⟨child', rfl | hchild', hx⟩)
            · exact Or.inr (Or.inl hx)
            · exact Or.inr (Or.inr (Or.inl hx))
            · exact Or.inl hx
            · exact Or.inr (Or.inr (Or.inr ⟨child', hchild', hx⟩))

/-- **Splitting a node's flattening at a separator.** Let $K_1$ and $K_2$ be lists of keys, $m$ a
key, and $C_1$ and $C_2$ lists of raw B-trees such that $C_1$ has exactly one more element than
$K_1$. Then the flattening of the node whose key list is $K_1$ followed by $m$ followed by $K_2$
and whose child list is $C_1$ followed by $C_2$ equals the flattening of the node with keys $K_1$
and children $C_1$, followed by $m$, followed by the flattening of the node with keys $K_2$ and
children $C_2$. -/
public theorem flatten_node_append_cons {median : α} :
    ∀ {keys₁ : List α} {children₁ : List (BTree α)} {keys₂ : List α}
      {children₂ : List (BTree α)},
      children₁.length = keys₁.length + 1 →
      flatten (node (keys₁ ++ median :: keys₂) (children₁ ++ children₂) :
          BTree α) =
        flatten (node keys₁ children₁ : BTree α) ++
          median :: flatten (node keys₂ children₂ : BTree α) := by
  intro keys₁
  induction keys₁ with
  | nil =>
      intro children₁ keys₂ children₂ hlen
      cases children₁ with
      | nil => simp at hlen
      | cons child children₁ =>
          cases children₁ with
          | nil =>
              simp only [List.nil_append, List.cons_append]
              rw [flatten_node_cons, flatten_node_nil]
          | cons _ _ =>
              simp only [List.length_cons, List.length_nil] at hlen
              omega
  | cons key keys₁ ih =>
      intro children₁ keys₂ children₂ hlen
      cases children₁ with
      | nil => simp at hlen
      | cons child children₁ =>
          have hlen' : children₁.length = keys₁.length + 1 := by
            simpa using hlen
          simp only [List.cons_append]
          rw [flatten_node_cons, flatten_node_cons, ih hlen']
          simp [List.append_assoc]

private theorem pairwise_flatten_of_mem [LT α] {child : BTree α} :
    ∀ {keys : List α} {children : List (BTree α)},
      child ∈ children →
      (flatten (node keys children : BTree α)).Pairwise (· < ·) →
      (flatten child).Pairwise (· < ·) := by
  intro keys
  induction keys with
  | nil =>
      intro children hmem hpair
      induction children with
      | nil => exact absurd hmem (by simp)
      | cons head children ih =>
          rw [List.mem_cons] at hmem
          rw [flatten_node_nil_cons] at hpair
          rw [List.pairwise_append] at hpair
          rcases hmem with rfl | hmem
          · exact hpair.1
          · exact ih hmem hpair.2.1
  | cons key keys ih =>
      intro children hmem hpair
      cases children with
      | nil => exact absurd hmem (by simp)
      | cons head children =>
          rw [List.mem_cons] at hmem
          rw [flatten_node_cons] at hpair
          rw [List.pairwise_append] at hpair
          rcases hmem with rfl | hmem
          · exact hpair.1
          · exact ih hmem (List.pairwise_cons.mp hpair.2.1).2

private theorem keys_sublist_flatten_node :
    ∀ {keys : List α} {children : List (BTree α)},
      keys.Sublist (flatten (node keys children : BTree α)) := by
  intro keys
  induction keys with
  | nil =>
      intro children
      exact List.nil_sublist _
  | cons key keys ih =>
      intro children
      cases children with
      | nil =>
          rw [flatten_node_cons_nil]
          exact (ih).cons_cons key
      | cons child children =>
          rw [flatten_node_cons]
          exact ((ih).cons_cons key).trans
            (List.IsSuffix.sublist ⟨flatten child, rfl⟩)

/-- **Membership in a B-tree.** A key $x$ belongs to a tree $T$ when $x$ occurs in the inorder
flattening of $T$.

Structurally, a key belongs to an internal node exactly when it is one of the node's separator
keys or belongs to one of its children. -/
public def Mem (x : α) (tree : BTree α) : Prop :=
  x ∈ flatten tree

public instance : Membership α (BTree α) :=
  ⟨fun tree x => Mem x tree⟩

@[simp] public theorem mem_leaf {x : α} {keys : List α} :
    x ∈ (leaf keys : BTree α) ↔ x ∈ keys := by
  show x ∈ flatten (leaf keys : BTree α) ↔ x ∈ keys
  rw [flatten_leaf]

public theorem mem_node {x : α} {keys : List α} {children : List (BTree α)} :
    x ∈ (node keys children : BTree α) ↔
      x ∈ keys ∨ ∃ child ∈ children, x ∈ child := by
  show x ∈ flatten (node keys children : BTree α) ↔ _
  exact mem_flatten_node

/-- **Ordered B-tree.** A B-tree over a type with a relation $<$ is ordered when its inorder
flattening is strictly increasing, that is, each key of the flattening is less than every
key that comes after it. This single condition packages sortedness of the keys at each node
and the separator bounds between a node's keys and the keys stored in its subtrees. -/
public def Ordered [LT α] (tree : BTree α) : Prop :=
  (flatten tree).Pairwise (· < ·)

/-- **The separator keys of an ordered node are sorted.** If an internal node with separator list
$K$ is ordered, then $K$ is strictly increasing: every key of $K$ is smaller than every key that
comes after it in $K$. -/
public theorem Ordered.node_keys_pairwise [LT α] {keys : List α}
    {children : List (BTree α)} (h : Ordered (node keys children : BTree α)) :
    keys.Pairwise (· < ·) := by
  have hpair : (flatten (node keys children : BTree α)).Pairwise (· < ·) := h
  exact hpair.sublist keys_sublist_flatten_node

/-- **Separator bounds in an ordered B-tree node.** Let $K_1$ and $K_2$ be lists of keys,
$k$ a key, and $C_1$ and $C_2$ lists of B-trees such that $C_1$ has exactly one more tree
than $K_1$ has keys. If the internal node whose key list is $K_1$ followed by $k$ followed
by $K_2$, and whose child list is $C_1$ followed by $C_2$, is ordered, then every key in the
flattening of the node with keys $K_1$ and children $C_1$ is less than $k$, and $k$ is less
than every key in the flattening of the node with keys $K_2$ and children $C_2$.

Here the last tree of $C_1$ is the subtree immediately left of $k$ and the first tree of
$C_2$ the one immediately right of it; in particular, every key in a child of an ordered
node lies strictly between the separators adjacent to it. -/
public theorem Ordered.separator_bounds [LT α] {keys₁ keys₂ : List α}
    {children₁ children₂ : List (BTree α)} {key : α}
    (hlen : children₁.length = keys₁.length + 1)
    (h : Ordered (node (keys₁ ++ key :: keys₂) (children₁ ++ children₂) : BTree α)) :
    (∀ x ∈ flatten (node keys₁ children₁ : BTree α), x < key) ∧
      (∀ x ∈ flatten (node keys₂ children₂ : BTree α), key < x) := by
  have hpair : (flatten (node (keys₁ ++ key :: keys₂)
      (children₁ ++ children₂) : BTree α)).Pairwise (· < ·) := h
  rw [flatten_node_append_cons hlen, List.pairwise_append] at hpair
  refine ⟨fun x hx => hpair.2.2 x hx key List.mem_cons_self,
    fun x hx => (List.pairwise_cons.mp hpair.2.1).1 x hx⟩

/-- **An ordered B-tree has no duplicate keys.** For a linearly ordered key type, the flattening
of an ordered raw B-tree has no duplicate entries. -/
public theorem Ordered.flatten_nodup [LinearOrder α] {tree : BTree α} (h : Ordered tree) :
    (flatten tree).Nodup :=
  List.Pairwise.nodup h

private theorem orderedInsert_length_le [LinearOrder α] {x : α} {keys : List α} :
    (orderedInsert x keys).length ≤ keys.length + 1 := by
  induction keys with
  | nil => simp [orderedInsert]
  | cons key keys ih =>
      simp only [orderedInsert]
      split_ifs with h1 h2
      · simp
      · simp only [List.length_cons]
        omega
      · simp

private theorem length_le_orderedInsert [LinearOrder α] {x : α} {keys : List α} :
    keys.length ≤ (orderedInsert x keys).length := by
  induction keys with
  | nil => simp [orderedInsert]
  | cons key keys ih =>
      simp only [orderedInsert]
      split_ifs with h1 h2
      · simp
      · simp only [List.length_cons]
        omega
      · simp

private theorem orderedInsert_length_eq_add_one_of_not_mem [LinearOrder α] {x : α} :
    ∀ {keys : List α}, x ∉ keys → (orderedInsert x keys).length = keys.length + 1 := by
  intro keys
  induction keys with
  | nil => intro _; rfl
  | cons key keys ih =>
      intro hmem
      have hne : x ≠ key := fun h => hmem (by simp [h])
      have hmem' : x ∉ keys := fun h => hmem (by simp [h])
      simp only [orderedInsert]
      split_ifs with h1 h2
      · rfl
      · simp only [List.length_cons, ih hmem']
      · exact absurd (le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)) hne

private theorem pairwise_orderedInsert [LinearOrder α] {x : α} :
    ∀ {keys : List α}, keys.Pairwise (· < ·) →
      (orderedInsert x keys).Pairwise (· < ·) := by
  intro keys
  induction keys with
  | nil => intro _; simp [orderedInsert]
  | cons key keys ih =>
      intro hpair
      rw [List.pairwise_cons] at hpair
      obtain ⟨hhead, htail⟩ := hpair
      simp only [orderedInsert]
      split_ifs with h1 h2
      · rw [List.pairwise_cons]
        refine ⟨?_, List.pairwise_cons.mpr ⟨hhead, htail⟩⟩
        intro y hy
        rw [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact h1
        · exact lt_trans h1 (hhead y hy)
      · rw [List.pairwise_cons]
        refine ⟨?_, ih htail⟩
        intro y hy
        rw [mem_orderedInsert] at hy
        rcases hy with rfl | hy
        · exact h2
        · exact hhead y hy
      · exact List.pairwise_cons.mpr ⟨hhead, htail⟩

private theorem orderedInsert_append_of_lt [LinearOrder α] {x key : α} (h : x < key)
    (left right : List α) :
    orderedInsert x (left ++ key :: right) = orderedInsert x left ++ key :: right := by
  induction left with
  | nil => simp [orderedInsert, h]
  | cons y ys ih =>
      show orderedInsert x (y :: (ys ++ key :: right)) = orderedInsert x (y :: ys) ++ key :: right
      simp only [orderedInsert]
      split_ifs with h1 h2
      · rfl
      · exact congrArg (y :: ·) ih
      · rfl

private theorem orderedInsert_append_of_forall_lt [LinearOrder α] {x : α} :
    ∀ {left : List α}, (∀ y ∈ left, y < x) → ∀ (right : List α),
      orderedInsert x (left ++ right) = left ++ orderedInsert x right := by
  intro left
  induction left with
  | nil => intro _ right; rfl
  | cons y ys ih =>
      intro hlt right
      have hy : y < x := hlt y (by simp)
      have hys : ∀ z ∈ ys, z < x := fun z hz => hlt z (by simp [hz])
      show orderedInsert x (y :: (ys ++ right)) = (y :: ys) ++ orderedInsert x right
      simp only [orderedInsert, ite_eq_right (not_lt_of_gt hy), ite_eq_left hy]
      exact congrArg (y :: ·) (ih hys right)

/-- **Structural invariant of a B-tree.** For a minimum degree $t$ and a minimum key count $m$
for the top node, the invariant is defined inductively over the height: a leaf with $k$ keys
satisfies it at height $0$ when $m \le k \le 2t - 1$, and for every natural number $h$, an
internal node with $k$ keys satisfies it at height $h + 1$ when $m \le k \le 2t - 1$, the
node has exactly $k + 1$ children, and every child satisfies the invariant with minimum key
count $t - 1$ at height $h$. Here $2t - 1$ and $t - 1$ are truncated at $0$.

Consequently all leaves of a valid tree sit at the same depth, every node has at most
$2t - 1$ keys, and every node other than the top one has at least $t - 1$ keys. Non-root
trees are used with $m = t - 1$; the root of a B-tree satisfies the root invariant instead. -/
public inductive Valid (t : Nat) : Nat → Nat → BTree α → Prop where
  | leaf {mink : Nat} {keys : List α} (hlo : mink ≤ keys.length)
      (hhi : keys.length ≤ 2 * t - 1) : Valid t mink 0 (.leaf keys)
  | node {mink height : Nat} {keys : List α} {children : List (BTree α)}
      (hlo : mink ≤ keys.length) (hhi : keys.length ≤ 2 * t - 1)
      (hlen : children.length = keys.length + 1)
      (hchildren : ∀ child ∈ children, Valid t (t - 1) height child) :
      Valid t mink (height + 1) (.node keys children)

/-- **Root invariant of a B-tree.** For a minimum degree $t$ and a height $h$, a tree
satisfies the root invariant when either $h = 0$ and the tree is a leaf with at most
$2t - 1$ keys (possibly none, for the empty tree), or $h = h' + 1$ and the tree is an
internal node with between $1$ and $2t - 1$ keys and exactly one more child than keys,
every child satisfying the structural invariant for minimum degree $t$, minimum top-node
key count $t - 1$ and height $h'$. Here $2t - 1$ and $t - 1$ are truncated at $0$. -/
public inductive ValidRoot (t : Nat) : Nat → BTree α → Prop where
  | leaf {keys : List α} (hhi : keys.length ≤ 2 * t - 1) : ValidRoot t 0 (.leaf keys)
  | node {height : Nat} {keys : List α} {children : List (BTree α)}
      (hlo : 1 ≤ keys.length) (hhi : keys.length ≤ 2 * t - 1)
      (hlen : children.length = keys.length + 1)
      (hchildren : ∀ child ∈ children, Valid t (t - 1) height child) :
      ValidRoot t (height + 1) (.node keys children)

/-- **Root-valid B-trees are valid.** If a tree satisfies the root invariant for minimum
degree $t$ at height $h$, then for some natural number $m$ it satisfies the structural
invariant for minimum degree $t$, minimum top-node key count $m$ and height $h$. -/
public theorem ValidRoot.valid {t height : Nat} {tree : BTree α}
    (h : ValidRoot t height tree) : ∃ mink, Valid t mink height tree := by
  cases h with
  | leaf hhi => exact ⟨0, Valid.leaf (Nat.zero_le _) hhi⟩
  | node hlo hhi hlen hchildren => exact ⟨1, Valid.node hlo hhi hlen hchildren⟩

/-- **B-tree search.** For a linearly ordered key type, the search for a key $x$ in a raw B-tree
proceeds as follows. At a leaf, report whether $x$ is in the leaf's key list. At an internal
node with separators $k_1, \dots, k_m$ and children $c_0, c_1, \dots$, scan the separators in
order. On reaching $k_i$, report failure if the node has no child $c_{i-1}$; otherwise search
$c_{i-1}$ if $x < k_i$, report success if $x = k_i$, and move on to the next separator if
$k_i < x$. If every separator is less than $x$, search the child $c_m$, or report failure if
the node has no such child. -/
public def contains [LinearOrder α] (x : α) : BTree α → Bool
  | .leaf keys => decide (x ∈ keys)
  | .node keys children => containsList x keys children
where
  containsList (x : α) : List α → List (BTree α) → Bool
    | [], child :: _ => contains x child
    | [], [] => false
    | key :: keys, child :: children =>
        if x < key then contains x child
        else if key < x then containsList x keys children
        else true
    | _ :: _, [] => false

private theorem containsList_spec [LinearOrder α] {x : α} :
    ∀ {keys : List α} {children : List (BTree α)},
      children.length = keys.length + 1 →
      (∀ child ∈ children, contains x child = true ↔ x ∈ flatten child) →
      (flatten (node keys children : BTree α)).Pairwise (· < ·) →
      (contains.containsList x keys children = true ↔
        x ∈ flatten (node keys children : BTree α)) := by
  intro keys
  induction keys with
  | nil =>
      intro children hlen hchild _
      cases children with
      | nil => simp at hlen
      | cons child children =>
          cases children with
          | cons _ _ =>
              simp only [List.length_cons, List.length_nil] at hlen
              omega
          | nil =>
              have hc := hchild child (by simp)
              simpa [contains.containsList, flatten_node_nil] using hc
  | cons key keys ih =>
      intro children hlen hchild hpair
      cases children with
      | nil => simp at hlen
      | cons child children =>
          have hlen' : children.length = keys.length + 1 := by simpa using hlen
          have htail : ∀ c ∈ children, contains x c = true ↔ x ∈ flatten c :=
            fun c hc => hchild c (List.mem_cons_of_mem child hc)
          have hhead := hchild child (by simp)
          rw [flatten_node_cons] at hpair
          rw [List.pairwise_append] at hpair
          obtain ⟨hpairchild, hpairrest, hcross⟩ := hpair
          rw [List.pairwise_cons] at hpairrest
          obtain ⟨hgt, hpairlist⟩ := hpairrest
          have hlt : ∀ y ∈ flatten child, y < key :=
            fun y hy => hcross y hy key List.mem_cons_self
          have iht := ih hlen' htail hpairlist
          simp only [contains.containsList, flatten_node_cons, List.mem_append,
            List.mem_cons]
          by_cases h1 : x < key
          · rw [ite_eq_left h1]
            constructor
            · intro hx
              exact Or.inl (hhead.mp hx)
            · rintro (hx | hx | hx)
              · exact hhead.mpr hx
              · exact absurd hx (ne_of_lt h1)
              · exact absurd (hgt x hx) (not_lt_of_gt h1)
          · by_cases h2 : key < x
            · rw [ite_eq_right h1, ite_eq_left h2, iht]
              constructor
              · intro hx
                exact Or.inr (Or.inr hx)
              · rintro (hx | hx | hx)
                · exact absurd (hlt x hx) (not_lt_of_gt h2)
                · exact absurd hx (ne_of_gt h2)
                · exact hx
            · have hxeq : x = key := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
              rw [ite_eq_right h1, ite_eq_right h2]
              simp [hxeq]

private theorem contains_spec [LinearOrder α] {t : Nat} {x : α} :
    ∀ {height mink : Nat} {tree : BTree α}, Valid t mink height tree → Ordered tree →
      (contains x tree = true ↔ x ∈ tree) := by
  intro height
  induction height with
  | zero =>
      intro mink tree hvalid _
      cases tree with
      | node _ _ => cases hvalid
      | leaf keys => simp [contains]
  | succ height ih =>
      intro mink tree hvalid hordered
      cases tree with
      | leaf _ => cases hvalid
      | node keys children =>
          cases hvalid with
          | node _ hhi hlen hchildren =>
              have hpair : (flatten (node keys children : BTree α)).Pairwise
                  (· < ·) := hordered
              have hchild : ∀ child ∈ children,
                  contains x child = true ↔ x ∈ flatten child := by
                intro child hmem
                exact ih (hchildren child hmem)
                  (pairwise_flatten_of_mem hmem hpair)
              have hspec := containsList_spec hlen hchild hpair
              have hcont : contains x (node keys children : BTree α) =
                  contains.containsList x keys children := by
                simp only [contains]
              show contains x (node keys children : BTree α) = true ↔
                x ∈ flatten (node keys children : BTree α)
              rw [hcont]
              exact hspec

/-- **Result of inserting into a B-tree subtree.** An insertion result over a key type $\alpha$
is either a single tree over $\alpha$, or a triple $(\ell, m, r)$ of two trees $\ell$ and $r$
over $\alpha$ and a key $m$ of $\alpha$. In insertion, the first form is a subtree that did not
split, and the second form is an overflowing node split into two trees of the same height, with
the median key $m$ promoted between them; the type itself does not record heights. -/
public def InsResult (α : Type u) := BTree α ⊕ (BTree α × α × BTree α)

/-- **Flattening of a B-tree insertion result.** The flattening of an insertion result that is a
single tree is the flattening of that tree; for a result that splits into a left tree $\ell$, a
promoted median key $m$ and a right tree $r$, it is the flattening of $\ell$, followed by $m$,
followed by the flattening of $r$. -/
public def grownFlatten : InsResult α → List α
  | .inl tree => flatten tree
  | .inr (left, median, right) => flatten left ++ median :: flatten right

/-- **Insertion into a B-tree leaf.** Over a linearly ordered key type, let $t$ be a natural
number, $x$ a key, $K$ the key list of a leaf, and $K'$ the result of ordered insertion of $x$
into $K$. If $K'$ has at most $2t - 1$ keys, the insertion result is the single leaf with keys
$K'$. Otherwise the leaf is split: the result consists of the leaf holding the first $t - 1$ keys
of $K'$, the next key of $K'$ promoted as the median, and the leaf holding the remaining keys.
Here subtraction of natural numbers is truncated at $0$. -/
public def insLeaf [LinearOrder α] (t : Nat) (x : α) (keys : List α) : InsResult α :=
  if (orderedInsert x keys).length ≤ 2 * t - 1 then .inl (.leaf (orderedInsert x keys))
  else match (orderedInsert x keys).drop (t - 1) with
    | [] => .inl (.leaf (orderedInsert x keys))
    | median :: rest => .inr (.leaf ((orderedInsert x keys).take (t - 1)), median, .leaf rest)

/-- **Splitting a B-tree node.** Let $t$ be a minimum degree, $s = t - 1$ (so $s = 0$ when
$t = 0$), $k_1, \dots, k_m$ a list of keys and $c_1, \dots, c_n$ a list of B-trees. If
$m > s$, splitting returns the pair of internal nodes formed by the keys $k_1, \dots, k_s$
with the first $t$ children (all of them if $n < t$) and by the keys $k_{s+2}, \dots, k_m$
with the children after the first $t$, together with the key $k_{s+1}$ promoted between
them. If $m \le s$, it returns the single internal node with keys $k_1, \dots, k_m$ and
children $c_1, \dots, c_n$ unchanged.

On an overfull node with $2t$ keys and $t \ge 1$, the promoted key $k_t$ is the median key. -/
public def splitNode (t : Nat) (keys : List α) (children : List (BTree α)) : InsResult α :=
  match keys.drop (t - 1) with
  | [] => .inl (.node keys children)
  | median :: rightKeys =>
      .inr (.node (keys.take (t - 1)) (children.take t), median,
        .node rightKeys (children.drop t))

/-- **Rebuilding an internal node after insertion.** For minimum degree $t$, a separator list $K$
and a child list $C$, the result is the internal node with separators $K$ and children $C$, kept
as a single tree when $K$ has at most $2t - 1$ keys, and otherwise split by node splitting into
two nodes and a promoted median key. -/
public def mkNode (t : Nat) (keys : List α) (children : List (BTree α)) : InsResult α :=
  if keys.length ≤ 2 * t - 1 then .inl (.node keys children) else splitNode t keys children

/-- **Split-returning insertion into a B-tree subtree.** For minimum degree $t$ and a key $x$,
insertion of $x$ into a tree returns an insertion result and is defined by recursion. At a leaf
with key list $K$, it is leaf insertion of $x$ into $K$. At an internal node, the separator list
and the child list are scanned together from the left. If $x$ is smaller than the current
separator, or no separator is left but a child is, $x$ is inserted into the current child. If $x$
is larger than the current separator, the scan moves on to the next separator and child. If $x$
equals the current separator, or no child is left, the remaining lists are kept unchanged. When
the child that received $x$ returns a single tree, that tree replaces the child; when it returns
two trees $\ell$, $r$ with a median $m$, the child is replaced by $\ell$ and $r$ with $m$ inserted
as a separator between them. The rebuilt separator and child lists are then turned into a node by
the internal-node rebuilding step: kept as one node if there are at most $2t - 1$ separators, and
split otherwise. -/
public def ins [LinearOrder α] (t : Nat) (x : α) : BTree α → InsResult α
  | .leaf keys => insLeaf t x keys
  | .node keys children =>
      let (keys', children') := insList t x keys children
      mkNode t keys' children'
where
  insList (t : Nat) (x : α) : List α → List (BTree α) → List α × List (BTree α)
    | [], child :: children =>
        match ins t x child with
        | .inl child' => ([], child' :: children)
        | .inr (left, median, right) => ([median], left :: right :: children)
    | [], [] => ([], [])
    | key :: keys, child :: children =>
        if x < key then
          match ins t x child with
          | .inl child' => (key :: keys, child' :: children)
          | .inr (left, median, right) =>
              (median :: key :: keys, left :: right :: children)
        else if key < x then
          let (keys', children') := insList t x keys children
          (key :: keys', child :: children')
        else (key :: keys, child :: children)
    | key :: keys, [] => (key :: keys, [])

/-- The specification of `ins` on a tree satisfying `Valid` and `Ordered`: a non-split
result is valid with the same bounds, both halves of a split result are non-root valid,
and the flattening of the result is `orderedInsert x` applied to the flattening of the input. -/
private def InsSpec [LinearOrder α] (t mink height : Nat) (x : α) (tree : BTree α) : Prop :=
  (∀ tree', ins t x tree = Sum.inl tree' → Valid t mink height tree') ∧
  (∀ left median right, ins t x tree = Sum.inr (left, median, right) →
    Valid t (t - 1) height left ∧ Valid t (t - 1) height right) ∧
  grownFlatten (ins t x tree) = orderedInsert x (flatten tree)

private theorem insList_spec [LinearOrder α] {t height : Nat} {x : α} :
    ∀ {keys : List α} {children : List (BTree α)},
      children.length = keys.length + 1 →
      (∀ child ∈ children, Valid t (t - 1) height child) →
      (∀ child ∈ children, InsSpec t (t - 1) height x child) →
      (flatten (node keys children : BTree α)).Pairwise (· < ·) →
      ∀ p, p = ins.insList t x keys children →
        p.2.length = p.1.length + 1 ∧ keys.length ≤ p.1.length ∧
          p.1.length ≤ keys.length + 1 ∧
          (∀ child ∈ p.2, Valid t (t - 1) height child) ∧
          flatten (node p.1 p.2 : BTree α) =
            orderedInsert x (flatten (node keys children : BTree α)) := by
  intro keys
  induction keys with
  | nil =>
      intro children hlen _ hspecs _ p hp
      cases children with
      | nil => simp at hlen
      | cons child children =>
          cases children with
          | cons _ _ =>
              simp only [List.length_cons, List.length_nil] at hlen
              omega
          | nil =>
              obtain ⟨hinl, hinr, hflat⟩ := hspecs child (by simp)
              cases hins : ins t x child with
              | inl child' =>
                  have e : ins.insList t x [] [child] = ([], [child']) := by
                    simp [ins.insList, hins]
                  rw [e] at hp
                  subst hp
                  refine ⟨rfl, Nat.zero_le _, Nat.zero_le _, ?_, ?_⟩
                  · intro c hc
                    change c ∈ [child'] at hc
                    rw [List.mem_singleton] at hc
                    rw [hc]
                    exact hinl child' hins
                  · show flatten (node [] [child'] : BTree α) =
                      orderedInsert x (flatten (node [] [child] : BTree α))
                    simp only [flatten_node_nil]
                    rw [hins] at hflat
                    exact hflat
              | inr split =>
                  rcases split with ⟨left, median, right⟩
                  have e : ins.insList t x [] [child] = ([median], [left, right]) := by
                    simp [ins.insList, hins]
                  rw [e] at hp
                  subst hp
                  have hboth := hinr left median right hins
                  refine ⟨rfl, Nat.zero_le _, Nat.le_refl _, ?_, ?_⟩
                  · intro c hc
                    change c ∈ [left, right] at hc
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
                    rcases hc with rfl | rfl
                    · exact hboth.1
                    · exact hboth.2
                  · show flatten (node [median] [left, right] : BTree α) =
                      orderedInsert x (flatten (node [] [child] : BTree α))
                    rw [flatten_node_pair, flatten_node_nil]
                    rw [hins] at hflat
                    exact hflat
  | cons key keys ih =>
      intro children hlen hvalid hspecs hpair p hp
      cases children with
      | nil => simp at hlen
      | cons child children =>
          have hlen' : children.length = keys.length + 1 := by simpa using hlen
          rw [flatten_node_cons] at hpair
          obtain ⟨hpchild, hprest, hcross⟩ := List.pairwise_append.mp hpair
          obtain ⟨hgt, hprest⟩ := List.pairwise_cons.mp hprest
          have hlt : ∀ y ∈ flatten child, y < key :=
            fun y hy => hcross y hy key List.mem_cons_self
          obtain ⟨hinl, hinr, hflat⟩ := hspecs child (by simp)
          have hvalidtail : ∀ c ∈ children, Valid t (t - 1) height c :=
            fun c hc => hvalid c (List.mem_cons_of_mem child hc)
          have hspectail : ∀ c ∈ children, InsSpec t (t - 1) height x c :=
            fun c hc => hspecs c (List.mem_cons_of_mem child hc)
          by_cases h1 : x < key
          · cases hins : ins t x child with
            | inl child' =>
                have e : ins.insList t x (key :: keys) (child :: children) =
                    (key :: keys, child' :: children) := by
                  simp [ins.insList, h1, hins]
                rw [e] at hp
                subst hp
                have hf : flatten child' = orderedInsert x (flatten child) := by
                  rw [hins] at hflat
                  exact hflat
                refine ⟨?_, Nat.le_refl _, Nat.le_succ _, ?_, ?_⟩
                · show (child' :: children).length = (key :: keys).length + 1
                  simp only [List.length_cons]
                  omega
                · intro c hc
                  change c ∈ child' :: children at hc
                  rw [List.mem_cons] at hc
                  rcases hc with rfl | hc
                  · exact hinl _ hins
                  · exact hvalidtail c hc
                · show flatten (node (key :: keys) (child' :: children) : BTree α) =
                    orderedInsert x (flatten (node (key :: keys) (child :: children) : BTree α))
                  simp only [flatten_node_cons]
                  rw [orderedInsert_append_of_lt h1, hf]
            | inr split =>
                rcases split with ⟨left, median, right⟩
                have e : ins.insList t x (key :: keys) (child :: children) =
                    (median :: key :: keys, left :: right :: children) := by
                  simp [ins.insList, h1, hins]
                rw [e] at hp
                subst hp
                have hboth := hinr left median right hins
                have hf : flatten left ++ median :: flatten right =
                    orderedInsert x (flatten child) := by
                  rw [hins] at hflat
                  exact hflat
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · show (left :: right :: children).length =
                    (median :: key :: keys).length + 1
                  simp only [List.length_cons]
                  omega
                · show (key :: keys).length ≤ (median :: key :: keys).length
                  simp only [List.length_cons]
                  omega
                · show (median :: key :: keys).length ≤ (key :: keys).length + 1
                  simp only [List.length_cons]
                  omega
                · intro c hc
                  change c ∈ left :: right :: children at hc
                  rw [List.mem_cons] at hc
                  rcases hc with rfl | hc
                  · exact hboth.1
                  · rw [List.mem_cons] at hc
                    rcases hc with rfl | hc
                    · exact hboth.2
                    · exact hvalidtail c hc
                · show flatten (node (median :: key :: keys)
                      (left :: right :: children) : BTree α) =
                    orderedInsert x
                      (flatten (node (key :: keys) (child :: children) : BTree α))
                  simp only [flatten_node_cons]
                  rw [orderedInsert_append_of_lt h1, ← hf]
                  simp [List.append_assoc]
          · by_cases h2 : key < x
            · cases hq : ins.insList t x keys children with
              | mk keys' children' =>
                  have hpairnode : (flatten (node keys children : BTree α)).Pairwise
                      (· < ·) := hprest
                  have htail := ih hlen' hvalidtail hspectail hpairnode
                    (keys', children') hq.symm
                  have ihlen : children'.length = keys'.length + 1 := htail.1
                  have ihge : keys.length ≤ keys'.length := htail.2.1
                  have ihle : keys'.length ≤ keys.length + 1 := htail.2.2.1
                  have ihvalid : ∀ c ∈ children', Valid t (t - 1) height c :=
                    htail.2.2.2.1
                  have ihflat : flatten (node keys' children' : BTree α) =
                      orderedInsert x (flatten (node keys children : BTree α)) :=
                    htail.2.2.2.2
                  have e : ins.insList t x (key :: keys) (child :: children) =
                      (key :: keys', child :: children') := by
                    simp [ins.insList, h1, h2, hq]
                  rw [e] at hp
                  subst hp
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · show (child :: children').length = (key :: keys').length + 1
                    simp only [List.length_cons]
                    omega
                  · show (key :: keys).length ≤ (key :: keys').length
                    simp only [List.length_cons]
                    omega
                  · show (key :: keys').length ≤ (key :: keys).length + 1
                    simp only [List.length_cons]
                    omega
                  · intro c hc
                    change c ∈ child :: children' at hc
                    rw [List.mem_cons] at hc
                    rcases hc with rfl | hc
                    · exact hvalid _ (by simp)
                    · exact ihvalid c hc
                  · show flatten (node (key :: keys') (child :: children') : BTree α) =
                      orderedInsert x
                        (flatten (node (key :: keys) (child :: children) : BTree α))
                    simp only [flatten_node_cons]
                    have hforall : ∀ y ∈ flatten child, y < x :=
                      fun y hy => lt_trans (hlt y hy) h2
                    have hcons : orderedInsert x
                        (key :: flatten (node keys children : BTree α)) =
                        key :: orderedInsert x (flatten (node keys children : BTree α)) := by
                      simp [orderedInsert, h1, h2]
                    rw [ihflat, orderedInsert_append_of_forall_lt hforall, hcons]
            · have hxeq : x = key := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
              have e : ins.insList t x (key :: keys) (child :: children) =
                  (key :: keys, child :: children) := by
                simp [ins.insList, h1, h2]
              rw [e] at hp
              subst hp
              refine ⟨?_, Nat.le_refl _, Nat.le_succ _, ?_, ?_⟩
              · show (child :: children).length = (key :: keys).length + 1
                exact hlen
              · intro c hc
                change c ∈ child :: children at hc
                exact hvalid c hc
              · show flatten (node (key :: keys) (child :: children) : BTree α) =
                  orderedInsert x (flatten (node (key :: keys) (child :: children) : BTree α))
                simp only [flatten_node_cons]
                have hmem : x ∈ flatten child ++
                    key :: flatten (node keys children : BTree α) := by
                  rw [hxeq]
                  exact List.mem_append_right _ List.mem_cons_self
                exact (orderedInsert_eq_of_mem hpair hmem).symm

private theorem ins_spec [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α} :
    ∀ {height mink : Nat} {tree : BTree α}, Valid t mink height tree → Ordered tree →
      InsSpec t mink height x tree := by
  intro height
  induction height with
  | zero =>
      intro mink tree hvalid _
      cases tree with
      | node _ _ => cases hvalid
      | leaf keys =>
          cases hvalid with
          | leaf hlo hhi =>
              by_cases hle : (orderedInsert x keys).length ≤ 2 * t - 1
              · have e : ins t x (leaf keys : BTree α) =
                    Sum.inl (leaf (orderedInsert x keys)) := by
                  simp [ins, insLeaf, hle]; rfl
                refine ⟨?_, ?_, ?_⟩
                · intro tree' heq
                  rw [e] at heq
                  have h : (leaf (orderedInsert x keys) : BTree α) = tree' := Sum.inl.inj heq
                  subst h
                  have hge := length_le_orderedInsert (x := x) (keys := keys)
                  exact Valid.leaf (by omega) hle
                · intro left median right heq
                  rw [e] at heq
                  cases heq
                · rw [e]
                  simp [grownFlatten]
              · have hlen2t : (orderedInsert x keys).length = 2 * t := by
                  have hle1 := orderedInsert_length_le (x := x) (keys := keys)
                  omega
                cases hdrop : (orderedInsert x keys).drop (t - 1) with
                | nil =>
                    exfalso
                    have h := congrArg List.length hdrop
                    rw [List.length_drop] at h
                    simp only [List.length_nil] at h
                    omega
                | cons median rest =>
                    have e : ins t x (leaf keys : BTree α) =
                        Sum.inr (leaf ((orderedInsert x keys).take (t - 1)), median,
                          leaf rest) := by
                      simp [ins, insLeaf, hle, hdrop]; rfl
                    have htake : ((orderedInsert x keys).take (t - 1)).length = t - 1 := by
                      rw [List.length_take]
                      omega
                    have hrest : rest.length = t := by
                      have h := congrArg List.length hdrop
                      rw [List.length_drop] at h
                      simp only [List.length_cons] at h
                      omega
                    refine ⟨?_, ?_, ?_⟩
                    · intro tree' heq
                      rw [e] at heq
                      cases heq
                    · intro left med right heq
                      rw [e] at heq
                      have h := Sum.inr.inj heq
                      simp only [Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl, rfl⟩ := h
                      exact ⟨Valid.leaf (by omega) (by omega),
                        Valid.leaf (by omega) (by omega)⟩
                    · rw [e]
                      have hdecomp : (orderedInsert x keys).take (t - 1) ++ median :: rest =
                          orderedInsert x keys := by
                        conv_rhs => rw [← List.take_append_drop (t - 1) (orderedInsert x keys)]
                        rw [hdrop]
                      simp only [grownFlatten, flatten_leaf]
                      exact hdecomp
  | succ height ih =>
      intro mink tree hvalid hordered
      cases tree with
      | leaf _ => cases hvalid
      | node keys children =>
          cases hvalid with
          | node hlo hhi hlen hchildren =>
              have hpair : (flatten (node keys children : BTree α)).Pairwise
                  (· < ·) := hordered
              have hspecs : ∀ child ∈ children, InsSpec t (t - 1) height x child :=
                fun child hmem => ih (hchildren child hmem)
                  (pairwise_flatten_of_mem hmem hpair)
              cases hq : ins.insList t x keys children with
              | mk keys' children' =>
                  have hlist := insList_spec hlen hchildren hspecs hordered
                    (keys', children') hq.symm
                  have ihlen : children'.length = keys'.length + 1 := hlist.1
                  have ihge : keys.length ≤ keys'.length := hlist.2.1
                  have ihle : keys'.length ≤ keys.length + 1 := hlist.2.2.1
                  have ihvalid : ∀ c ∈ children', Valid t (t - 1) height c :=
                    hlist.2.2.2.1
                  have ihflat : flatten (node keys' children' : BTree α) =
                      orderedInsert x (flatten (node keys children : BTree α)) :=
                    hlist.2.2.2.2
                  have hins_eq : ins t x (node keys children : BTree α) =
                      mkNode t keys' children' := by
                    simp [ins, hq]
                  by_cases hsplit : keys'.length ≤ 2 * t - 1
                  · have e : ins t x (node keys children : BTree α) =
                        Sum.inl (node keys' children') := by
                      rw [hins_eq]
                      simp [mkNode, hsplit]; rfl
                    refine ⟨?_, ?_, ?_⟩
                    · intro tree' heq
                      rw [e] at heq
                      have h : (node keys' children' : BTree α) = tree' :=
                        Sum.inl.inj heq
                      subst h
                      exact Valid.node (by omega) hsplit ihlen ihvalid
                    · intro left median right heq
                      rw [e] at heq
                      cases heq
                    · rw [e]
                      simp only [grownFlatten]
                      exact ihflat
                  · have hlen2t : keys'.length = 2 * t := by omega
                    have hclen : children'.length = 2 * t + 1 := by omega
                    cases hdrop : keys'.drop (t - 1) with
                    | nil =>
                        exfalso
                        have h := congrArg List.length hdrop
                        rw [List.length_drop] at h
                        simp only [List.length_nil] at h
                        omega
                    | cons median rightKeys =>
                        have e : ins t x (node keys children : BTree α) =
                            Sum.inr (node (keys'.take (t - 1)) (children'.take t), median,
                              node rightKeys (children'.drop t)) := by
                          rw [hins_eq]
                          simp [mkNode, splitNode, hsplit, hdrop]; rfl
                        have htakeK : (keys'.take (t - 1)).length = t - 1 := by
                          rw [List.length_take]
                          omega
                        have htakeC : (children'.take t).length = t := by
                          rw [List.length_take]
                          omega
                        have hrightK : rightKeys.length = t := by
                          have h := congrArg List.length hdrop
                          rw [List.length_drop] at h
                          simp only [List.length_cons] at h
                          omega
                        have hdropC : (children'.drop t).length = t + 1 := by
                          rw [List.length_drop]
                          omega
                        have hleft : Valid t (t - 1) (height + 1)
                            (node (keys'.take (t - 1)) (children'.take t) : BTree α) :=
                          Valid.node (by omega) (by omega) (by omega)
                            (fun c hc => ihvalid c (List.take_subset t children' hc))
                        have hright : Valid t (t - 1) (height + 1)
                            (node rightKeys (children'.drop t) : BTree α) :=
                          Valid.node (by omega) (by omega) (by omega)
                            (fun c hc => ihvalid c (List.drop_subset t children' hc))
                        have hks : keys' =
                            keys'.take (t - 1) ++ median :: rightKeys := by
                          conv_lhs => rw [← List.take_append_drop (t - 1) keys']
                          rw [hdrop]
                        have happ := flatten_node_append_cons (median := median)
                          (keys₁ := keys'.take (t - 1))
                          (children₁ := children'.take t)
                          (keys₂ := rightKeys) (children₂ := children'.drop t)
                          (by omega)
                        rw [← hks, List.take_append_drop t children'] at happ
                        refine ⟨?_, ?_, ?_⟩
                        · intro tree' heq
                          rw [e] at heq
                          cases heq
                        · intro left med right heq
                          rw [e] at heq
                          have h := Sum.inr.inj heq
                          simp only [Prod.mk.injEq] at h
                          obtain ⟨rfl, rfl, rfl⟩ := h
                          exact ⟨hleft, hright⟩
                        · rw [e]
                          simp only [grownFlatten]
                          rw [← happ]
                          exact ihflat

/-- **B-tree insertion.** For minimum degree $t$, the tree obtained by inserting a key $x$ into a
tree $T$ is computed from the split-returning insertion of $x$ into $T$: if that returns a single
tree, this tree is the result; if it returns two trees $\ell$ and $r$ with a promoted median key
$m$, the result is a new root node with the single separator $m$ and the two children $\ell$ and
$r$.

When $T$ is a B-tree of minimum degree $t$, inserting a key already present in $T$ returns a tree
with the same flattening. -/
public def insert [LinearOrder α] (t : Nat) (x : α) (tree : BTree α) : BTree α :=
  match ins t x tree with
  | .inl tree' => tree'
  | .inr (left, median, right) => .node [median] [left, right]

/-- **The empty B-tree.** The empty B-tree is the leaf with no keys. -/
public def empty : BTree α :=
  .leaf []

/-- **B-trees of a given minimum degree.** A tree $T$ is a B-tree of minimum degree $t$ when
$t \ge 2$ (the CLRS Chapter 18 minimum-degree requirement), $T$ is ordered, and $T$ is
root-valid at some height. This is the invariant preserved by insertion and by building a tree
from a list. -/
public def IsBTree [LT α] (t : Nat) (tree : BTree α) : Prop :=
  2 ≤ t ∧ Ordered tree ∧ ∃ height, ValidRoot t height tree

/-- **The minimum degree of a B-tree is at least two.** If a tree is a B-tree of minimum
degree $t$, then $t \ge 2$. -/
public theorem IsBTree.two_le [LT α] {t : Nat} {tree : BTree α}
    (h : IsBTree t tree) : 2 ≤ t :=
  h.1

/-- **B-trees are ordered.** If a tree is a B-tree of minimum degree $t$, then it is ordered:
each key of its inorder flattening is less than every key that comes after it. -/
public theorem IsBTree.ordered [LT α] {t : Nat} {tree : BTree α}
    (h : IsBTree t tree) : Ordered tree :=
  h.2.1

/-- **B-trees satisfy the root invariant.** If $T$ is a B-tree of minimum degree $t$, then there
is a height $h$ such that $T$ satisfies the root structural invariant of minimum degree $t$ at
height $h$. -/
public theorem IsBTree.exists_validRoot [LT α] {t : Nat} {tree : BTree α}
    (h : IsBTree t tree) : ∃ height, ValidRoot t height tree :=
  h.2.2

/-- **The empty tree is a B-tree.** For every key type equipped with a binary relation $<$ and
every natural number $t \ge 2$, the empty B-tree is a B-tree of minimum degree $t$. -/
public theorem IsBTree.empty [LT α] {t : Nat} (ht : 2 ≤ t) :
    IsBTree t (empty : BTree α) := by
  refine ⟨ht, ?_, 0, ValidRoot.leaf (by simp)⟩
  show (flatten (BTree.empty : BTree α)).Pairwise (· < ·)
  simp [BTree.empty]

/-- **B-tree insertion as sorted list insertion.** Let $\alpha$ be linearly ordered, let
$t \ge 2$, and let $T$ be a B-tree of minimum degree $t$ with keys in $\alpha$. For every key
$x \in \alpha$, the inorder flattening of the tree obtained by inserting $x$ into $T$ with
minimum degree $t$ equals the sorted insertion of $x$ into the inorder flattening of $T$. -/
public theorem flatten_insert [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : IsBTree t tree) :
    flatten (insert t x tree) = orderedInsert x (flatten tree) := by
  obtain ⟨-, hordered, height, hroot⟩ := h
  obtain ⟨mink, hvalid⟩ := hroot.valid
  obtain ⟨-, -, hflat⟩ := ins_spec ht hvalid hordered
  cases hins : ins t x tree with
  | inl tree' =>
      have e : insert t x tree = tree' := by simp [insert, hins]
      rw [e]
      rw [hins] at hflat
      exact hflat
  | inr split =>
      rcases split with ⟨left, median, right⟩
      have e : insert t x tree = node [median] [left, right] := by simp [insert, hins]
      rw [e, flatten_node_pair]
      rw [hins] at hflat
      exact hflat

/-- **Membership after B-tree insertion.** Let $t \ge 2$ and let $T$ be a B-tree of minimum
degree $t$ over a linearly ordered key type. For all keys $x$ and $y$, $y$ belongs to the tree
obtained by inserting $x$ into $T$ if and only if $y = x$ or $y$ belongs to $T$. -/
public theorem mem_insert [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x y : α}
    {tree : BTree α} (h : IsBTree t tree) :
    y ∈ insert t x tree ↔ y = x ∨ y ∈ tree := by
  show y ∈ flatten (insert t x tree) ↔ y = x ∨ y ∈ flatten tree
  rw [flatten_insert ht h, mem_orderedInsert]

/-- **Insertion preserves the B-tree invariant.** Let $t \ge 2$ and let the keys come from a
linearly ordered type. If $T$ is a B-tree of minimum degree $t$, then for every key $x$ the tree
obtained by inserting $x$ into $T$ is again a B-tree of minimum degree $t$: it is ordered and
root-valid at some height. -/
public theorem IsBTree.insert [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : IsBTree t tree) : IsBTree t (BTree.insert t x tree) := by
  obtain ⟨-, hordered, height, hroot⟩ := h
  have hord' : Ordered (BTree.insert t x tree) := by
    have hfi : flatten (BTree.insert t x tree) = orderedInsert x (flatten tree) :=
      flatten_insert ht ⟨ht, hordered, height, hroot⟩
    show (flatten (BTree.insert t x tree)).Pairwise (· < ·)
    rw [hfi]
    exact pairwise_orderedInsert hordered
  refine ⟨ht, hord', ?_⟩
  cases hroot with
  | @leaf keys hhi =>
      obtain ⟨hinl, hinr, -⟩ :=
        ins_spec ht (Valid.leaf (Nat.zero_le _) hhi) hordered
      cases hins : ins t x (leaf keys) with
      | inl tree' =>
          have e : BTree.insert t x (leaf keys : BTree α) = tree' := by simp [BTree.insert, hins]
          rw [e]
          have hvalid' := hinl tree' hins
          cases hvalid' with
          | leaf _ hhi' => exact ⟨0, ValidRoot.leaf hhi'⟩
      | inr split =>
          rcases split with ⟨left, median, right⟩
          have e : BTree.insert t x (leaf keys : BTree α) =
              node [median] [left, right] := by
            simp [BTree.insert, hins]
          rw [e]
          have hboth := hinr left median right hins
          refine ⟨1, ValidRoot.node (Nat.le_refl 1) ?_ rfl ?_⟩
          · simp only [List.length_cons, List.length_nil]
            omega
          · intro c hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact hboth.1
            · exact hboth.2
  | @node height keys children hlo hhi hlen hchildren =>
      obtain ⟨hinl, hinr, -⟩ :=
        ins_spec ht (Valid.node hlo hhi hlen hchildren) hordered
      cases hins : ins t x (node keys children) with
      | inl tree' =>
          have e : BTree.insert t x (node keys children : BTree α) = tree' := by
            simp [BTree.insert, hins]
          rw [e]
          have hvalid' := hinl tree' hins
          cases hvalid' with
          | node hlo' hhi' hlen' hchildren' =>
              exact ⟨_, ValidRoot.node hlo' hhi' hlen' hchildren'⟩
      | inr split =>
          rcases split with ⟨left, median, right⟩
          have e : BTree.insert t x (node keys children : BTree α) =
              node [median] [left, right] := by
            simp [BTree.insert, hins]
          rw [e]
          have hboth := hinr left median right hins
          refine ⟨height + 2, ValidRoot.node (height := height + 1) (Nat.le_refl 1) ?_ rfl ?_⟩
          · simp only [List.length_cons, List.length_nil]
            omega
          · intro c hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact hboth.1
            · exact hboth.2

/-- **Correctness of B-tree search.** Let $\alpha$ be linearly ordered and let $T$ be a B-tree
of minimum degree $t$ with keys in $\alpha$. For every key $x \in \alpha$, the search procedure
returns true on $x$ and $T$ if and only if $x$ is a member of $T$, that is, $x$ occurs in the
inorder flattening of $T$. -/
public theorem contains_eq_true_iff [LinearOrder α] {t : Nat} {x : α} {tree : BTree α}
    (h : IsBTree t tree) : contains x tree = true ↔ x ∈ tree := by
  obtain ⟨-, hordered, height, hroot⟩ := h
  obtain ⟨mink, hvalid⟩ := hroot.valid
  exact contains_spec hvalid hordered

/-- **Size of a B-tree after insertion.** Let $\alpha$ be linearly ordered, let $t \ge 2$, let
$T$ be a B-tree of minimum degree $t$ with keys in $\alpha$, and let $x \in \alpha$. Let $T'$ be
the tree obtained by inserting $x$ into $T$ with minimum degree $t$. If $x$ occurs in the
inorder flattening of $T$, then the flattening of $T'$ has the same length as that of $T$;
otherwise it is one longer. -/
public theorem flatten_length_insert [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : IsBTree t tree) :
    (flatten (insert t x tree)).length =
      if x ∈ flatten tree then (flatten tree).length else (flatten tree).length + 1 := by
  rw [flatten_insert ht h]
  obtain ⟨-, hordered, -⟩ := h
  by_cases hx : x ∈ flatten tree
  · rw [ite_eq_left hx]
    have hself : orderedInsert x (flatten tree) = flatten tree :=
      orderedInsert_eq_of_mem hordered hx
    rw [hself]
  · rw [ite_eq_right hx]
    exact orderedInsert_length_eq_add_one_of_not_mem hx

/-- **B-tree built from a list.** For a linearly ordered key type and a natural number $t$, the
tree built from the empty list is the empty tree, and the tree built from a list with head $x$
and tail $L$ is the result of inserting $x$, with minimum degree $t$, into the tree built from
$L$. Thus the elements are inserted from right to left. -/
public def fromList [LinearOrder α] (t : Nat) : List α → BTree α
  | [] => empty
  | x :: xs => insert t x (fromList t xs)

/-- **Building from a list yields a B-tree.** For a linearly ordered key type, every natural
number $t \ge 2$ and every list $L$ of keys, the tree obtained by inserting the elements of $L$
from right to left into the empty tree, each insertion with minimum degree $t$, is a B-tree of
minimum degree $t$. -/
public theorem IsBTree.fromList [LinearOrder α] {t : Nat} (ht : 2 ≤ t) (xs : List α) :
    IsBTree t (fromList t xs) := by
  induction xs with
  | nil => exact IsBTree.empty ht
  | cons x xs ih => exact ih.insert ht

/-- **Membership in a B-tree built from a list.** Let $t \ge 2$ and let $xs$ be a list over a
linearly ordered key type. A key $x$ belongs to the tree of minimum degree $t$ built from $xs$
(by inserting the elements of $xs$ into the empty tree, from right to left) if and only if $x$
is an element of $xs$. -/
public theorem mem_fromList [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {xs : List α} : x ∈ fromList t xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [fromList, empty]
  | cons y ys ih =>
      show x ∈ insert t y (fromList t ys) ↔ x ∈ y :: ys
      rw [mem_insert ht (IsBTree.fromList ht ys), ih, List.mem_cons]

end BTree

end Cslib.Algorithms.Lean
