/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.OrderedInsert
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# 2-3 trees

A 2-3 tree is a balanced search tree in which every internal node has two or
three children and all leaves lie at the same depth. Here the tree type is
indexed by its height: a `Tree α h` has all of its leaves at depth `h`, so
balance is a typing invariant. The recursive `Balanced` predicate and
`height_eq` record the same fact at the level of the recursively computed
height. Keys stored at nodes are strict separators: in `node2 a l r` every key
of `l` is below `a` and every key of `r` is above it, and similarly with two
separators at a `node3`; this is the `Ordered` predicate.

Insertion follows the standard splitting discipline. The auxiliary `ins`
returns an `Overflow`: either a replacement tree of the same height, or a
*split* into two trees of that height separated by a promoted key. A 2-node
absorbs a split child by becoming a 3-node; a 3-node passes a split upward.
At the root, a split becomes a new 2-node and the height grows by one.
Insertion ignores an already-present key.

The machine-checked results are `ins_spec`, which bundles preservation of
`Ordered` and the equation `flatten (insert result) = orderedInsert x (flatten
t)` for the height-indexed insertion, and its root-level consequences in the
`Root` API: `Root.ordered_insert`, `Root.flatten_insert`,
`Root.mem_flatten_insert`, and `Root.contains_eq_true_iff` (search agrees with
membership in the flattening). There is no formal cost model; the index gives
height `O(log n)` only in combination with size bounds that are not stated
here. Deletion is out of scope for this module.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace TwoThreeTree

/-- **Height-indexed 2-3 trees.** For a type $\alpha$ of keys, the 2-3 trees over $\alpha$ indexed
by height are generated as follows. The leaf is a tree of height $0$ and stores no key. For a
natural number $h$, a key $a$ and trees $l$, $r$ of height $h$, the 2-node with separator $a$
and children $l$, $r$ is a tree of height $h + 1$. For a natural number $h$, keys $a$, $b$ and
trees $l$, $m$, $r$ of height $h$, the 3-node with separators $a$, $b$ and children $l$, $m$,
$r$ is a tree of height $h + 1$. Hence all leaves of a tree of height $h$ lie at depth $h$. -/
public inductive Tree (α : Type u) : Nat → Type u where
  | leaf : Tree α 0
  | node2 {h : Nat} (a : α) (l r : Tree α h) : Tree α (h + 1)
  | node3 {h : Nat} (a b : α) (l m r : Tree α h) : Tree α (h + 1)

/-- **Insertion results for 2-3 trees.** For a type $\alpha$ and a natural number $h$, an
insertion result at height $h$ is either a 2-3 tree over $\alpha$ of height $h$, or a split:
two 2-3 trees $l$ and $r$ over $\alpha$ of height $h$ together with a promoted key $k \in \alpha$.

It records the outcome of inserting a key into a tree of height $h$. -/
public inductive Overflow (α : Type u) : Nat → Type u where
  | ok {h : Nat} (t : Tree α h) : Overflow α h
  | split {h : Nat} (l : Tree α h) (k : α) (r : Tree α h) : Overflow α h

variable {α : Type u}

/-- **Height of a 2-3 tree.** The height of a 2-3 tree is computed along its leftmost spine:
a leaf has height $0$, and a 2-node or a 3-node has height one more than the height of its
leftmost child. -/
public def height : {h : Nat} → Tree α h → Nat
  | _, .leaf => 0
  | _, .node2 _ l _ => height l + 1
  | _, .node3 _ _ l _ _ => height l + 1

/-- **Computed height equals the height index.** For every 2-3 tree $t$ with height index $h$,
the height of $t$ computed along its leftmost spine equals $h$. -/
public theorem height_eq {h : Nat} (t : Tree α h) : height t = h := by
  induction t with
  | leaf => rfl
  | node2 _ _ _ ihl _ => exact congrArg Nat.succ ihl
  | node3 _ _ _ _ _ ihl _ _ => exact congrArg Nat.succ ihl

/-- **Balance invariant for 2-3 trees.** A leaf is balanced, and a node is balanced when all of
its subtrees are balanced and have the same computed height, where the computed height of a
tree is the length of its leftmost path from the root down to a leaf. Hence all leaves of a
balanced tree lie at the same depth. -/
public def Balanced : {h : Nat} → Tree α h → Prop
  | _, .leaf => True
  | _, .node2 _ l r => Balanced l ∧ Balanced r ∧ height l = height r
  | _, .node3 _ _ l m r =>
      Balanced l ∧ Balanced m ∧ Balanced r ∧ height l = height m ∧ height m = height r

/-- **Every height-indexed 2-3 tree is balanced.** For every height $h$, every 2-3 tree of
height $h$ satisfies the balance invariant: at every node, the subtrees are balanced and have
equal computed heights. -/
public theorem balanced {h : Nat} (t : Tree α h) : Balanced t := by
  induction t with
  | leaf => trivial
  | node2 _ _ _ ihl ihr => exact ⟨ihl, ihr, by rw [height_eq, height_eq]⟩
  | node3 _ _ _ _ _ ihl ihm ihr =>
    exact ⟨ihl, ihm, ihr, by rw [height_eq, height_eq], by rw [height_eq, height_eq]⟩

/-- **Membership in a 2-3 tree.** A key $x$ is a member of a 2-3 tree when it is one of the
separator keys stored at its nodes: nothing is a member of a leaf; $x$ is a member of a 2-node
with key $a$ and children $l, r$ when it is a member of $l$, equals $a$, or is a member of $r$;
and $x$ is a member of a 3-node with keys $a, b$ and children $l, m, r$ when it is a member of
$l$, equals $a$, is a member of $m$, equals $b$, or is a member of $r$.

Membership is structural and does not use the ordering invariant. -/
public def Mem (x : α) : {h : Nat} → Tree α h → Prop
  | _, .leaf => False
  | _, .node2 a l r => Mem x l ∨ x = a ∨ Mem x r
  | _, .node3 a b l m r => Mem x l ∨ x = a ∨ Mem x m ∨ x = b ∨ Mem x r

public instance {h : Nat} : Membership α (Tree α h) :=
  ⟨fun t x => Mem x t⟩

@[simp] private theorem mem_leaf {x : α} :
    x ∈ (Tree.leaf : Tree α 0) ↔ False :=
  Iff.rfl

@[simp] private theorem mem_node2 {h : Nat} {x a : α} {l r : Tree α h} :
    x ∈ Tree.node2 a l r ↔ x ∈ l ∨ x = a ∨ x ∈ r :=
  Iff.rfl

@[simp] private theorem mem_node3 {h : Nat} {x a b : α} {l m r : Tree α h} :
    x ∈ Tree.node3 a b l m r ↔ x ∈ l ∨ x = a ∨ x ∈ m ∨ x = b ∨ x ∈ r :=
  Iff.rfl

/-- **Predicate on all keys of a 2-3 tree.** For a predicate $p$ on keys and a 2-3 tree $t$,
$\mathrm{All}_p(t)$ states that every separator key stored at a node of $t$ satisfies $p$: it
is true at a leaf, and at a node it requires $p$ of each key of the node and
$\mathrm{All}_p$ of each of its subtrees. -/
public def All (p : α → Prop) : {h : Nat} → Tree α h → Prop
  | _, .leaf => True
  | _, .node2 a l r => All p l ∧ p a ∧ All p r
  | _, .node3 a b l m r => All p l ∧ p a ∧ All p m ∧ p b ∧ All p r

private theorem all_mono {p q : α → Prop} (hmono : ∀ y, p y → q y) :
    ∀ {h : Nat} (t : Tree α h), All p t → All q t := by
  intro h t
  induction t with
  | leaf => exact fun _ => trivial
  | node2 a l r ihl ihr =>
    intro hAll
    obtain ⟨hAl, hpa, hAr⟩ := hAll
    exact ⟨ihl hAl, hmono a hpa, ihr hAr⟩
  | node3 a b l m r ihl ihm ihr =>
    intro hAll
    obtain ⟨hAl, hpa, hAm, hpb, hAr⟩ := hAll
    exact ⟨ihl hAl, hmono a hpa, ihm hAm, hmono b hpb, ihr hAr⟩

/-- **All-keys predicate agrees with membership on 2-3 trees.** For every predicate $p$ on
keys and every 2-3 tree $t$ of height $h$, the recursive predicate requiring $p$ at every key
stored at a node of $t$ holds if and only if $p(x)$ holds for every member $x$ of $t$, where
$x$ is a member of $t$ when it equals one of the keys stored at some node of $t$. -/
public theorem all_iff_forall_mem {p : α → Prop} {h : Nat} {t : Tree α h} :
    All p t ↔ ∀ x, x ∈ t → p x := by
  induction t with
  | leaf => simp [All]
  | node2 a l r ihl ihr =>
    simp only [All, mem_node2, ihl, ihr]
    constructor
    · rintro ⟨hAl, hpa, hAr⟩ x (hx | hx | hx)
      · exact hAl x hx
      · simpa [hx] using hpa
      · exact hAr x hx
    · intro hforall
      exact ⟨fun x hx => hforall x (Or.inl hx), hforall a (Or.inr (Or.inl rfl)),
        fun x hx => hforall x (Or.inr (Or.inr hx))⟩
  | node3 a b l m r ihl ihm ihr =>
    simp only [All, mem_node3, ihl, ihm, ihr]
    constructor
    · rintro ⟨hAl, hpa, hAm, hpb, hAr⟩ x (hx | hx | hx | hx | hx)
      · exact hAl x hx
      · simpa [hx] using hpa
      · exact hAm x hx
      · simpa [hx] using hpb
      · exact hAr x hx
    · intro hforall
      exact ⟨fun x hx => hforall x (Or.inl hx), hforall a (Or.inr (Or.inl rfl)),
        fun x hx => hforall x (Or.inr (Or.inr (Or.inl hx))),
        hforall b (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        fun x hx => hforall x (Or.inr (Or.inr (Or.inr (Or.inr hx))))⟩

/-- **Ordering invariant for 2-3 trees.** Let $\alpha$ be a type with a relation $<$. The leaf is
ordered. A 2-node with separator $a$ and children $l$, $r$ is ordered when $l$ and $r$ are
ordered, $y < a$ for every key $y$ stored in $l$, and $a < y$ for every key $y$ stored in $r$. A
3-node with separators $a$, $b$ and children $l$, $m$, $r$ is ordered when $l$, $m$ and $r$ are
ordered, $a < b$, $y < a$ for every key $y$ stored in $l$, $a < y$ and $y < b$ for every key $y$
stored in $m$, and $b < y$ for every key $y$ stored in $r$. -/
public def Ordered [LT α] : {h : Nat} → Tree α h → Prop
  | _, .leaf => True
  | _, .node2 a l r =>
      Ordered l ∧ Ordered r ∧ All (· < a) l ∧ All (a < ·) r
  | _, .node3 a b l m r =>
      Ordered l ∧ Ordered m ∧ Ordered r ∧ a < b ∧ All (· < a) l ∧
        All (a < ·) m ∧ All (· < b) m ∧ All (b < ·) r

/-- **Accumulated inorder traversal of a 2-3 tree.** For a 2-3 tree $t$ and a list $s$, the
accumulated traversal $F(t, s)$ is defined by recursion on $t$: for a leaf, $F(t, s) = s$; for
a 2-node with key $a$ and children $l, r$, $F(t, s)$ is $F(l, s')$ where $s'$ is $a$ prepended
to $F(r, s)$; for a 3-node with keys $a, b$ and children $l, m, r$, $F(t, s)$ is $F(l, s')$
where $s'$ is $a$ prepended to $F(m, s'')$ and $s''$ is $b$ prepended to $F(r, s)$.

The result is the inorder traversal of $t$ followed by $s$. It is built without recopying the
traversals of left subtrees. -/
public def flattenAux : {h : Nat} → Tree α h → List α → List α
  | _, .leaf, suffix => suffix
  | _, .node2 a l r, suffix => flattenAux l (a :: flattenAux r suffix)
  | _, .node3 a b l m r, suffix =>
      flattenAux l (a :: flattenAux m (b :: flattenAux r suffix))

private theorem flattenAux_append {h : Nat} (t : Tree α h)
    (xs ys : List α) :
    flattenAux t (xs ++ ys) = flattenAux t xs ++ ys := by
  induction t generalizing xs with
  | leaf => rfl
  | node2 a l r ihl ihr =>
      simp only [flattenAux]
      rw [ihr]
      change flattenAux l ((a :: flattenAux r xs) ++ ys) =
        flattenAux l (a :: flattenAux r xs) ++ ys
      exact ihl _
  | node3 a b l m r ihl ihm ihr =>
      simp only [flattenAux]
      rw [ihr]
      change flattenAux l
          (a :: flattenAux m ((b :: flattenAux r xs) ++ ys)) =
        flattenAux l (a :: flattenAux m (b :: flattenAux r xs)) ++ ys
      rw [ihm]
      change flattenAux l ((a :: flattenAux m (b :: flattenAux r xs)) ++ ys) =
        flattenAux l (a :: flattenAux m (b :: flattenAux r xs)) ++ ys
      exact ihl _

/-- **Inorder traversal of a 2-3 tree.** The flattening of a 2-3 tree $t$ is the accumulated
inorder traversal of $t$ onto the empty list. Equivalently, the flattening of a leaf is empty;
that of a 2-node with key $a$ and children $l, r$ is the flattening of $l$, then $a$, then the
flattening of $r$; and that of a 3-node with keys $a, b$ and children $l, m, r$ is the flattening
of $l$, then $a$, then the flattening of $m$, then $b$, then the flattening of $r$. -/
public def flatten {h : Nat} (t : Tree α h) : List α :=
  flattenAux t []

/-- **The accumulated traversal appends the suffix.** For every 2-3 tree $t$ (of any height)
and every list $s$, the accumulated inorder traversal of $t$ onto $s$ equals the flattening of
$t$ followed by $s$. -/
public theorem flattenAux_eq {h : Nat} (t : Tree α h) (suffix : List α) :
    flattenAux t suffix = flatten t ++ suffix := by
  show flattenAux t suffix = flattenAux t [] ++ suffix
  rw [← flattenAux_append t [] suffix]
  simp

@[simp] public theorem flatten_leaf : flatten (Tree.leaf : Tree α 0) = [] :=
  rfl

@[simp] public theorem flatten_node2 {h : Nat} {a : α} {l r : Tree α h} :
    flatten (Tree.node2 a l r) = flatten l ++ a :: flatten r := by
  show flattenAux l (a :: flattenAux r []) =
    flattenAux l [] ++ a :: flattenAux r []
  simpa using flattenAux_append l [] (a :: flattenAux r [])

@[simp] public theorem flatten_node3 {h : Nat} {a b : α} {l m r : Tree α h} :
    flatten (Tree.node3 a b l m r) =
      flatten l ++ a :: (flatten m ++ b :: flatten r) := by
  have hm : flattenAux m (b :: flattenAux r []) =
      flattenAux m [] ++ b :: flattenAux r [] := by
    simpa using flattenAux_append m [] (b :: flattenAux r [])
  show flattenAux l (a :: flattenAux m (b :: flattenAux r [])) =
    flattenAux l [] ++ a :: (flattenAux m [] ++ b :: flattenAux r [])
  rw [hm]
  simpa using flattenAux_append l []
    (a :: (flattenAux m [] ++ b :: flattenAux r []))

/-- **The inorder traversal lists exactly the keys of a 2-3 tree.** For every 2-3 tree $t$ of
height $h$ and every key $x$, $x$ occurs in the inorder traversal of $t$ if and only if $x$ is a
member of $t$, that is, one of the separator keys stored at its nodes. -/
public theorem mem_flatten {x : α} {h : Nat} {t : Tree α h} :
    x ∈ flatten t ↔ x ∈ t := by
  induction t with
  | leaf => simp
  | node2 a l r ihl ihr => simp [ihl, ihr, or_left_comm]
  | node3 a b l m r ihl ihm ihr => simp [ihl, ihm, ihr, or_left_comm]

/-- **All-keys predicate agrees with the flattening on 2-3 trees.** For every predicate $p$
on keys and every 2-3 tree $t$ of height $h$, every key stored at a node of $t$ satisfies $p$
if and only if every element of the inorder flattening of $t$ satisfies $p$. -/
public theorem all_iff_forall_flatten {p : α → Prop} {h : Nat} {t : Tree α h} :
    All p t ↔ ∀ y ∈ flatten t, p y := by
  rw [all_iff_forall_mem]
  constructor
  · intro hforall y hy
    exact hforall y (mem_flatten.mp hy)
  · intro hforall y hy
    exact hforall y (mem_flatten.mpr hy)

/-- **Inorder traversal of an ordered 2-3 tree is strictly increasing.** Let $\alpha$ be a
linearly ordered type. For every natural number $h$ and every ordered 2-3 tree $t$ over $\alpha$
of height $h$, the flattening (inorder traversal) of $t$ is strictly increasing: whenever a key
$x$ occurs before a key $y$ in it, $x < y$. -/
public theorem ordered_flatten_pairwise [LinearOrder α] {h : Nat} {t : Tree α h}
    (hOrd : Ordered t) : List.Pairwise (· < ·) (flatten t) := by
  induction t with
  | leaf => simp
  | node2 a l r ihl ihr =>
    obtain ⟨hOl, hOr, hAl, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    have hBr : ∀ y ∈ flatten r, a < y := all_iff_forall_flatten.mp hAr
    rw [flatten_node2, List.pairwise_append]
    refine ⟨ihl hOl, ?_, ?_⟩
    · rw [List.pairwise_cons]
      exact ⟨hBr, ihr hOr⟩
    · intro y hy z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hBl y hy
      · exact lt_trans (hBl y hy) (hBr z hz)
  | node3 a b l m r ihl ihm ihr =>
    obtain ⟨hOl, hOm, hOr, hab, hAl, hAmgt, hAmlt, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    have hBmgt : ∀ y ∈ flatten m, a < y := all_iff_forall_flatten.mp hAmgt
    have hBmlt : ∀ y ∈ flatten m, y < b := all_iff_forall_flatten.mp hAmlt
    have hBr : ∀ y ∈ flatten r, b < y := all_iff_forall_flatten.mp hAr
    have hpwMid : List.Pairwise (· < ·) (flatten m ++ b :: flatten r) := by
      rw [List.pairwise_append]
      refine ⟨ihm hOm, ?_, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨hBr, ihr hOr⟩
      · intro y hy z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hBmlt y hy
        · exact lt_trans (hBmlt y hy) (hBr z hz)
    have hpwTail : List.Pairwise (· < ·) (a :: (flatten m ++ b :: flatten r)) := by
      rw [List.pairwise_cons]
      refine ⟨?_, hpwMid⟩
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hBmgt y hy
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hab
        · exact lt_trans hab (hBr y hy)
    rw [flatten_node3, List.pairwise_append]
    refine ⟨ihl hOl, hpwTail, ?_⟩
    intro y hy z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hBl y hy
    · exact lt_trans (hBl y hy) ((List.pairwise_cons.mp hpwTail).1 z hz)

/-- **The traversal of an ordered 2-3 tree has no duplicates.** If the keys are linearly ordered
and a 2-3 tree $t$ (of any height) is ordered, then no key occurs twice in the flattening of
$t$. -/
public theorem flatten_nodup [LinearOrder α] {h : Nat} {t : Tree α h}
    (hOrd : Ordered t) : (flatten t).Nodup :=
  (ordered_flatten_pairwise hOrd).nodup

/-- **Search in a 2-3 tree.** For a linearly ordered key type, searching a 2-3 tree for a key
$x$ returns false at a leaf. At a 2-node with key $a$, it searches the left subtree if $x < a$,
otherwise the right subtree if $a < x$, and otherwise returns true. At a 3-node with keys $a$
and $b$, it searches the left subtree if $x < a$; otherwise, if $a < x$, it searches the
middle subtree if $x < b$, otherwise the right subtree if $b < x$, and otherwise returns true;
if neither $x < a$ nor $a < x$, it returns true. -/
public def contains [LinearOrder α] (x : α) : {h : Nat} → Tree α h → Bool
  | _, .leaf => false
  | _, .node2 a l r =>
      if x < a then contains x l
      else if a < x then contains x r
      else true
  | _, .node3 a b l m r =>
      if x < a then contains x l
      else if a < x then
        if x < b then contains x m
        else if b < x then contains x r
        else true
      else true

/-- **Search in an ordered 2-3 tree is correct.** Let the keys be linearly ordered and let $t$ be
a 2-3 tree of height $h$ that satisfies the ordering invariant. Then searching $t$ for a key
$x$ returns true if and only if $x$ occurs in the inorder flattening of $t$. -/
public theorem contains_eq_true_iff [LinearOrder α] {x : α} {h : Nat} {t : Tree α h}
    (hOrd : Ordered t) : contains x t = true ↔ x ∈ flatten t := by
  induction t with
  | leaf => simp [contains]
  | node2 a l r ihl ihr =>
    obtain ⟨hOl, hOr, hAl, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    have hBr : ∀ y ∈ flatten r, a < y := all_iff_forall_flatten.mp hAr
    by_cases hxa : x < a
    · have hNotR : x ∉ flatten r := fun hmem => lt_asymm hxa (hBr x hmem)
      simp [contains, hxa, ihl hOl, hNotR, ne_of_lt hxa]
    · by_cases hax : a < x
      · have hNotL : x ∉ flatten l := fun hmem => lt_asymm hax (hBl x hmem)
        simp [contains, hxa, hax, ihr hOr, hNotL, ne_of_gt hax]
      · obtain rfl : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        simp [contains, hxa]
  | node3 a b l m r ihl ihm ihr =>
    obtain ⟨hOl, hOm, hOr, hab, hAl, hAmgt, hAmlt, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    have hBmgt : ∀ y ∈ flatten m, a < y := all_iff_forall_flatten.mp hAmgt
    have hBmlt : ∀ y ∈ flatten m, y < b := all_iff_forall_flatten.mp hAmlt
    have hBr : ∀ y ∈ flatten r, b < y := all_iff_forall_flatten.mp hAr
    by_cases hxa : x < a
    · have hNotM : x ∉ flatten m := fun hmem => lt_asymm hxa (hBmgt x hmem)
      have hNotR : x ∉ flatten r :=
        fun hmem => lt_asymm (lt_trans hxa hab) (hBr x hmem)
      simp [contains, hxa, ihl hOl, hNotM, hNotR, ne_of_lt hxa,
        ne_of_lt (lt_trans hxa hab)]
    · by_cases hax : a < x
      · by_cases hxb : x < b
        · have hNotL : x ∉ flatten l := fun hmem => lt_asymm hax (hBl x hmem)
          have hNotR : x ∉ flatten r := fun hmem => lt_asymm hxb (hBr x hmem)
          simp [contains, hxa, hax, hxb, ihm hOm, hNotL, hNotR, ne_of_gt hax,
            ne_of_lt hxb]
        · by_cases hbx : b < x
          · have hNotL : x ∉ flatten l := fun hmem => lt_asymm hax (hBl x hmem)
            have hNotM : x ∉ flatten m := fun hmem => lt_asymm hbx (hBmlt x hmem)
            simp [contains, hxa, hax, hxb, hbx, ihr hOr, hNotL, hNotM,
              ne_of_gt hax, ne_of_gt hbx]
          · obtain rfl : x = b := le_antisymm (le_of_not_gt hbx) (le_of_not_gt hxb)
            simp [contains, hxa, hax, hxb]
      · obtain rfl : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        simp [contains, hxa]

private theorem orderedInsert_append_left [LinearOrder α] {x a : α} (hxa : x < a) :
    ∀ (L R : List α), (∀ y ∈ L, y < a) →
      orderedInsert x (L ++ a :: R) = orderedInsert x L ++ a :: R := by
  intro L
  induction L with
  | nil =>
    intro R _
    simp [orderedInsert, hxa]
  | cons b bs ih =>
    intro R hL
    have hbs : ∀ y ∈ bs, y < a := fun y hy => hL y (List.mem_cons_of_mem b hy)
    show orderedInsert x (b :: (bs ++ a :: R)) = orderedInsert x (b :: bs) ++ a :: R
    rcases lt_trichotomy x b with hlt | heq | hgt
    · simp [orderedInsert, hlt]
    · have hnot1 : ¬x < b := by rw [heq]; exact lt_irrefl _
      have hnot2 : ¬b < x := by rw [heq]; exact lt_irrefl _
      simp [orderedInsert, hnot1, hnot2]
    · have hnot : ¬x < b := not_lt_of_ge (le_of_lt hgt)
      simp [orderedInsert, hnot, hgt, ih R hbs]

private theorem orderedInsert_append_right [LinearOrder α] {x a : α} (hax : a < x) :
    ∀ (L R : List α), (∀ y ∈ L, y < x) →
      orderedInsert x (L ++ a :: R) = L ++ a :: orderedInsert x R := by
  intro L
  induction L with
  | nil =>
    intro R _
    have hnot : ¬x < a := not_lt_of_ge (le_of_lt hax)
    simp [orderedInsert, hnot, hax]
  | cons b bs ih =>
    intro R hL
    have hb : b < x := hL b (by simp)
    have hbs : ∀ y ∈ bs, y < x := fun y hy => hL y (List.mem_cons_of_mem b hy)
    have hnot : ¬x < b := not_lt_of_ge (le_of_lt hb)
    show orderedInsert x (b :: (bs ++ a :: R)) = (b :: bs) ++ a :: orderedInsert x R
    simp [orderedInsert, hnot, hb, ih R hbs]

private theorem orderedInsert_append_eq [LinearOrder α] (a : α) :
    ∀ (L R : List α), (∀ y ∈ L, y < a) →
      orderedInsert a (L ++ a :: R) = L ++ a :: R := by
  intro L
  induction L with
  | nil =>
    intro R _
    simp [orderedInsert, lt_irrefl a]
  | cons b bs ih =>
    intro R hL
    have hb : b < a := hL b (by simp)
    have hbs : ∀ y ∈ bs, y < a := fun y hy => hL y (List.mem_cons_of_mem b hy)
    have hnot : ¬a < b := not_lt_of_ge (le_of_lt hb)
    show orderedInsert a (b :: (bs ++ a :: R)) = (b :: bs) ++ a :: R
    simp [orderedInsert, hnot, hb, ih R hbs]

/-- **Insertion into a height-indexed 2-3 tree.** Inserting a key $x$ into a 2-3 tree of
height $h$ yields either a single tree of height $h$ or a split into two trees of height $h$
around a promoted key. Inserting into a leaf gives the split of two leaves around $x$. At a
2-node with key $a$, insertion recurses into the left child if $x < a$ and into the right child
if $a < x$; a returned tree replaces that child, and a returned split around $k$ is absorbed by
turning the node into a 3-node with keys $k, a$ (left) or $a, k$ (right). At a 3-node with keys
$a, b$, insertion recurses into the left child if $x < a$, the middle child if $a < x < b$, and
the right child if $a < x$ and $b < x$; a returned tree replaces that child, and a returned split
makes the node split into two 2-nodes, promoting $a$, the child's promoted key, or $b$
respectively. In the remaining cases $x$ equals a key of the node and the tree is returned
unchanged. -/
public def ins [LinearOrder α] (x : α) : {h : Nat} → Tree α h → Overflow α h
  | _, .leaf => .split .leaf x .leaf
  | _, .node2 a l r =>
      if x < a then
        match ins x l with
        | .ok l' => .ok (.node2 a l' r)
        | .split l₁ k l₂ => .ok (.node3 k a l₁ l₂ r)
      else if a < x then
        match ins x r with
        | .ok r' => .ok (.node2 a l r')
        | .split r₁ k r₂ => .ok (.node3 a k l r₁ r₂)
      else .ok (.node2 a l r)
  | _, .node3 a b l m r =>
      if x < a then
        match ins x l with
        | .ok l' => .ok (.node3 a b l' m r)
        | .split l₁ k l₂ => .split (.node2 k l₁ l₂) a (.node2 b m r)
      else if a < x then
        if x < b then
          match ins x m with
          | .ok m' => .ok (.node3 a b l m' r)
          | .split m₁ k m₂ => .split (.node2 a l m₁) k (.node2 b m₂ r)
        else if b < x then
          match ins x r with
          | .ok r' => .ok (.node3 a b l m r')
          | .split r₁ k r₂ => .split (.node2 a l m) b (.node2 k r₁ r₂)
        else .ok (.node3 a b l m r)
      else .ok (.node3 a b l m r)

/-- **Insertion specification for 2-3 trees.** Let $\alpha$ be linearly ordered, let
$x \in \alpha$, and let $t$ be a 2-3 tree of height $h$. An insertion result of height $h$ meets
the specification for inserting $x$ into $t$ when the following holds. If it is a single tree
$t'$ of height $h$, then $t'$ is ordered and its inorder traversal equals the ordered insertion
of $x$ into the inorder traversal of $t$. If it is a split into trees $l$ and $r$ of height $h$
around a promoted key $k$, then $l$ and $r$ are ordered, every key of $l$ is less than $k$,
every key of $r$ is greater than $k$, and the traversal of $l$ followed by $k$ and then the
traversal of $r$ equals the ordered insertion of $x$ into the inorder traversal of $t$. -/
public def InsSpec [LinearOrder α] (x : α) {h : Nat} (t : Tree α h) :
    Overflow α h → Prop
  | .ok t' => Ordered t' ∧ flatten t' = orderedInsert x (flatten t)
  | .split l k r =>
      Ordered l ∧ Ordered r ∧ All (· < k) l ∧ All (k < ·) r ∧
        flatten l ++ k :: flatten r = orderedInsert x (flatten t)

/-- `All` lifted to an insertion overflow. -/
private def AllOverflow (p : α → Prop) : {h : Nat} → Overflow α h → Prop
  | _, .ok t => All p t
  | _, .split l k r => All p l ∧ p k ∧ All p r

private theorem all_ins [LinearOrder α] {p : α → Prop} {x : α} (hx : p x) :
    ∀ {h : Nat} (t : Tree α h), All p t → AllOverflow p (ins x t) := by
  intro hidx t
  induction t with
  | leaf =>
    intro _
    exact ⟨trivial, hx, trivial⟩
  | node2 a l r ihl ihr =>
    intro hAll
    obtain ⟨hAl, hpa, hAr⟩ := hAll
    by_cases hxa : x < a
    · have ih := ihl hAl
      cases hins : ins x l with
      | ok l' =>
        rw [hins] at ih
        have hEq : ins x (Tree.node2 a l r) = Overflow.ok (Tree.node2 a l' r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        exact ⟨ih, hpa, hAr⟩
      | split l₁ k l₂ =>
        rw [hins] at ih
        obtain ⟨h1, h2, h3⟩ := ih
        have hEq : ins x (Tree.node2 a l r) =
            Overflow.ok (Tree.node3 k a l₁ l₂ r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        exact ⟨h1, h2, h3, hpa, hAr⟩
    · by_cases hax : a < x
      · have ih := ihr hAr
        cases hins : ins x r with
        | ok r' =>
          rw [hins] at ih
          have hEq : ins x (Tree.node2 a l r) = Overflow.ok (Tree.node2 a l r') := by
            simp [ins, hxa, hax, hins]
          rw [hEq]
          exact ⟨hAl, hpa, ih⟩
        | split r₁ k r₂ =>
          rw [hins] at ih
          obtain ⟨h1, h2, h3⟩ := ih
          have hEq : ins x (Tree.node2 a l r) =
              Overflow.ok (Tree.node3 a k l r₁ r₂) := by
            simp [ins, hxa, hax, hins]
          rw [hEq]
          exact ⟨hAl, hpa, h1, h2, h3⟩
      · have hEq : ins x (Tree.node2 a l r) = Overflow.ok (Tree.node2 a l r) := by
          simp [ins, hxa, hax]
        rw [hEq]
        exact ⟨hAl, hpa, hAr⟩
  | node3 a b l m r ihl ihm ihr =>
    intro hAll
    obtain ⟨hAl, hpa, hAm, hpb, hAr⟩ := hAll
    by_cases hxa : x < a
    · have ih := ihl hAl
      cases hins : ins x l with
      | ok l' =>
        rw [hins] at ih
        have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.ok (Tree.node3 a b l' m r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        exact ⟨ih, hpa, hAm, hpb, hAr⟩
      | split l₁ k l₂ =>
        rw [hins] at ih
        obtain ⟨h1, h2, h3⟩ := ih
        have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.split (Tree.node2 k l₁ l₂) a (Tree.node2 b m r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        exact ⟨⟨h1, h2, h3⟩, hpa, ⟨hAm, hpb, hAr⟩⟩
    · by_cases hax : a < x
      · by_cases hxb : x < b
        · have ih := ihm hAm
          cases hins : ins x m with
          | ok m' =>
            rw [hins] at ih
            have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.ok (Tree.node3 a b l m' r) := by
              simp [ins, hxa, hax, hxb, hins]
            rw [hEq]
            exact ⟨hAl, hpa, ih, hpb, hAr⟩
          | split m₁ k m₂ =>
            rw [hins] at ih
            obtain ⟨h1, h2, h3⟩ := ih
            have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.split (Tree.node2 a l m₁) k (Tree.node2 b m₂ r) := by
              simp [ins, hxa, hax, hxb, hins]
            rw [hEq]
            exact ⟨⟨hAl, hpa, h1⟩, h2, ⟨h3, hpb, hAr⟩⟩
        · by_cases hbx : b < x
          · have ih := ihr hAr
            cases hins : ins x r with
            | ok r' =>
              rw [hins] at ih
              have hEq : ins x (Tree.node3 a b l m r) =
                  Overflow.ok (Tree.node3 a b l m r') := by
                simp [ins, hxa, hax, hxb, hbx, hins]
              rw [hEq]
              exact ⟨hAl, hpa, hAm, hpb, ih⟩
            | split r₁ k r₂ =>
              rw [hins] at ih
              obtain ⟨h1, h2, h3⟩ := ih
              have hEq : ins x (Tree.node3 a b l m r) =
                  Overflow.split (Tree.node2 a l m) b (Tree.node2 k r₁ r₂) := by
                simp [ins, hxa, hax, hxb, hbx, hins]
              rw [hEq]
              exact ⟨⟨hAl, hpa, hAm⟩, hpb, ⟨h1, h2, h3⟩⟩
          · have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.ok (Tree.node3 a b l m r) := by
              simp [ins, hxa, hax, hxb, hbx]
            rw [hEq]
            exact ⟨hAl, hpa, hAm, hpb, hAr⟩
      · have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.ok (Tree.node3 a b l m r) := by
          simp [ins, hxa, hax]
        rw [hEq]
        exact ⟨hAl, hpa, hAm, hpb, hAr⟩

/-- **Correctness of 2-3 tree insertion.** Let $\alpha$ be linearly ordered, let $x \in \alpha$,
and let $t$ be an ordered 2-3 tree of height $h$. Then inserting $x$ into $t$ meets the insertion
specification. If the insertion returns a single tree $t'$ of height $h$, then $t'$ is ordered
and its inorder traversal is the ordered insertion of $x$ into the inorder traversal of $t$. If
it returns a split into trees $l$ and $r$ of height $h$ around a promoted key $k$, then $l$ and
$r$ are ordered, every key of $l$ is less than $k$, every key of $r$ is greater than $k$, and
the traversal of $l$ followed by $k$ and then the traversal of $r$ is the ordered insertion of
$x$ into the inorder traversal of $t$.

Balance is automatic from the height index. -/
public theorem ins_spec [LinearOrder α] (x : α) :
    ∀ {h : Nat} (t : Tree α h), Ordered t → InsSpec x t (ins x t) := by
  intro hidx t
  induction t with
  | leaf =>
    intro _
    show InsSpec x Tree.leaf (Overflow.split Tree.leaf x Tree.leaf)
    exact ⟨trivial, trivial, trivial, trivial, by simp [orderedInsert]⟩
  | node2 a l r ihl ihr =>
    intro hOrd
    obtain ⟨hOl, hOr, hAl, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    by_cases hxa : x < a
    · have ih := ihl hOl
      cases hins : ins x l with
      | ok l' =>
        rw [hins] at ih
        obtain ⟨hOl', hf⟩ := ih
        have hAll' : All (· < a) l' := by
          have hAll := all_ins (p := (· < a)) hxa l hAl
          rw [hins] at hAll
          exact hAll
        have hEq : ins x (Tree.node2 a l r) = Overflow.ok (Tree.node2 a l' r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        refine ⟨⟨hOl', hOr, hAll', hAr⟩, ?_⟩
        simp only [flatten_node2]
        rw [hf, orderedInsert_append_left hxa _ _ hBl]
      | split l₁ k l₂ =>
        rw [hins] at ih
        obtain ⟨hO₁, hO₂, hA₁, hA₂, hf⟩ := ih
        have hAllSplit := all_ins (p := (· < a)) hxa l hAl
        rw [hins] at hAllSplit
        obtain ⟨-, hka, hAa₂⟩ := hAllSplit
        have hEq : ins x (Tree.node2 a l r) =
            Overflow.ok (Tree.node3 k a l₁ l₂ r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        refine ⟨⟨hO₁, hO₂, hOr, hka, hA₁, hA₂, hAa₂, hAr⟩, ?_⟩
        simp only [flatten_node3, flatten_node2]
        rw [orderedInsert_append_left hxa _ _ hBl, ← hf]
        simp [List.append_assoc]
    · by_cases hax : a < x
      · have hBlx : ∀ y ∈ flatten l, y < x :=
          fun y hy => lt_trans (hBl y hy) hax
        have ih := ihr hOr
        cases hins : ins x r with
        | ok r' =>
          rw [hins] at ih
          obtain ⟨hOr', hf⟩ := ih
          have hAll' : All (a < ·) r' := by
            have hAll := all_ins (p := (a < ·)) hax r hAr
            rw [hins] at hAll
            exact hAll
          have hEq : ins x (Tree.node2 a l r) =
              Overflow.ok (Tree.node2 a l r') := by
            simp [ins, hxa, hax, hins]
          rw [hEq]
          refine ⟨⟨hOl, hOr', hAl, hAll'⟩, ?_⟩
          simp only [flatten_node2]
          rw [hf, orderedInsert_append_right hax _ _ hBlx]
        | split r₁ k r₂ =>
          rw [hins] at ih
          obtain ⟨hO₁, hO₂, hA₁, hA₂, hf⟩ := ih
          have hAllSplit := all_ins (p := (a < ·)) hax r hAr
          rw [hins] at hAllSplit
          obtain ⟨hAa₁, hak, -⟩ := hAllSplit
          have hEq : ins x (Tree.node2 a l r) =
              Overflow.ok (Tree.node3 a k l r₁ r₂) := by
            simp [ins, hxa, hax, hins]
          rw [hEq]
          refine ⟨⟨hOl, hO₁, hO₂, hak, hAl, hAa₁, hA₁, hA₂⟩, ?_⟩
          simp only [flatten_node3, flatten_node2]
          rw [orderedInsert_append_right hax _ _ hBlx, ← hf]
      · have hEq : ins x (Tree.node2 a l r) = Overflow.ok (Tree.node2 a l r) := by
          simp [ins, hxa, hax]
        rw [hEq]
        obtain rfl : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        refine ⟨⟨hOl, hOr, hAl, hAr⟩, ?_⟩
        simp only [flatten_node2]
        rw [orderedInsert_append_eq _ _ _ hBl]
  | node3 a b l m r ihl ihm ihr =>
    intro hOrd
    obtain ⟨hOl, hOm, hOr, hab, hAl, hAmgt, hAmlt, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    have hBmlt : ∀ y ∈ flatten m, y < b := all_iff_forall_flatten.mp hAmlt
    by_cases hxa : x < a
    · have ih := ihl hOl
      cases hins : ins x l with
      | ok l' =>
        rw [hins] at ih
        obtain ⟨hOl', hf⟩ := ih
        have hAll' : All (· < a) l' := by
          have hAll := all_ins (p := (· < a)) hxa l hAl
          rw [hins] at hAll
          exact hAll
        have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.ok (Tree.node3 a b l' m r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        refine ⟨⟨hOl', hOm, hOr, hab, hAll', hAmgt, hAmlt, hAr⟩, ?_⟩
        simp only [flatten_node3]
        rw [hf, orderedInsert_append_left hxa _ _ hBl]
      | split l₁ k l₂ =>
        rw [hins] at ih
        obtain ⟨hO₁, hO₂, hA₁, hA₂, hf⟩ := ih
        have hAllSplit := all_ins (p := (· < a)) hxa l hAl
        rw [hins] at hAllSplit
        obtain ⟨hAa₁, hka, hAa₂⟩ := hAllSplit
        have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.split (Tree.node2 k l₁ l₂) a (Tree.node2 b m r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        refine ⟨⟨hO₁, hO₂, hA₁, hA₂⟩, ⟨hOm, hOr, hAmlt, hAr⟩, ⟨hAa₁, hka, hAa₂⟩,
          ⟨hAmgt, hab, all_mono (fun y hy => lt_trans hab hy) r hAr⟩, ?_⟩
        simp only [flatten_node2, flatten_node3]
        rw [orderedInsert_append_left hxa _ _ hBl, ← hf]
    · by_cases hax : a < x
      · have hBlx : ∀ y ∈ flatten l, y < x :=
          fun y hy => lt_trans (hBl y hy) hax
        by_cases hxb : x < b
        · have ih := ihm hOm
          cases hins : ins x m with
          | ok m' =>
            rw [hins] at ih
            obtain ⟨hOm', hf⟩ := ih
            have hAllGt : All (a < ·) m' := by
              have hAll := all_ins (p := (a < ·)) hax m hAmgt
              rw [hins] at hAll
              exact hAll
            have hAllLt : All (· < b) m' := by
              have hAll := all_ins (p := (· < b)) hxb m hAmlt
              rw [hins] at hAll
              exact hAll
            have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.ok (Tree.node3 a b l m' r) := by
              simp [ins, hxa, hax, hxb, hins]
            rw [hEq]
            refine ⟨⟨hOl, hOm', hOr, hab, hAl, hAllGt, hAllLt, hAr⟩, ?_⟩
            simp only [flatten_node3]
            rw [hf, orderedInsert_append_right hax _ _ hBlx,
              orderedInsert_append_left hxb _ _ hBmlt]
          | split m₁ k m₂ =>
            rw [hins] at ih
            obtain ⟨hO₁, hO₂, hA₁, hA₂, hf⟩ := ih
            have hAllGt := all_ins (p := (a < ·)) hax m hAmgt
            rw [hins] at hAllGt
            obtain ⟨hAm₁gt, hak, -⟩ := hAllGt
            have hAllLt := all_ins (p := (· < b)) hxb m hAmlt
            rw [hins] at hAllLt
            obtain ⟨-, hkb, hAm₂lt⟩ := hAllLt
            have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.split (Tree.node2 a l m₁) k (Tree.node2 b m₂ r) := by
              simp [ins, hxa, hax, hxb, hins]
            rw [hEq]
            refine ⟨⟨hOl, hO₁, hAl, hAm₁gt⟩, ⟨hO₂, hOr, hAm₂lt, hAr⟩,
              ⟨all_mono (fun y hy => lt_trans hy hak) l hAl, hak, hA₁⟩,
              ⟨hA₂, hkb, all_mono (fun y hy => lt_trans hkb hy) r hAr⟩, ?_⟩
            simp only [flatten_node2, flatten_node3]
            rw [orderedInsert_append_right hax _ _ hBlx,
              orderedInsert_append_left hxb _ _ hBmlt, ← hf]
            simp [List.append_assoc]
        · by_cases hbx : b < x
          · have hBmx : ∀ y ∈ flatten m, y < x :=
              fun y hy => lt_trans (hBmlt y hy) hbx
            have ih := ihr hOr
            cases hins : ins x r with
            | ok r' =>
              rw [hins] at ih
              obtain ⟨hOr', hf⟩ := ih
              have hAll' : All (b < ·) r' := by
                have hAll := all_ins (p := (b < ·)) hbx r hAr
                rw [hins] at hAll
                exact hAll
              have hEq : ins x (Tree.node3 a b l m r) =
                  Overflow.ok (Tree.node3 a b l m r') := by
                simp [ins, hxa, hax, hxb, hbx, hins]
              rw [hEq]
              refine ⟨⟨hOl, hOm, hOr', hab, hAl, hAmgt, hAmlt, hAll'⟩, ?_⟩
              simp only [flatten_node3]
              rw [hf, orderedInsert_append_right hax _ _ hBlx,
                orderedInsert_append_right hbx _ _ hBmx]
            | split r₁ k r₂ =>
              rw [hins] at ih
              obtain ⟨hO₁, hO₂, hA₁, hA₂, hf⟩ := ih
              have hAllSplit := all_ins (p := (b < ·)) hbx r hAr
              rw [hins] at hAllSplit
              obtain ⟨hAr₁, hbk, hAr₂⟩ := hAllSplit
              have hEq : ins x (Tree.node3 a b l m r) =
                  Overflow.split (Tree.node2 a l m) b (Tree.node2 k r₁ r₂) := by
                simp [ins, hxa, hax, hxb, hbx, hins]
              rw [hEq]
              refine ⟨⟨hOl, hOm, hAl, hAmgt⟩, ⟨hO₁, hO₂, hA₁, hA₂⟩,
                ⟨all_mono (fun y hy => lt_trans hy hab) l hAl, hab, hAmlt⟩,
                ⟨hAr₁, hbk, hAr₂⟩, ?_⟩
              simp only [flatten_node2, flatten_node3]
              rw [orderedInsert_append_right hax _ _ hBlx,
                orderedInsert_append_right hbx _ _ hBmx, ← hf]
              simp [List.append_assoc]
          · have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.ok (Tree.node3 a b l m r) := by
              simp [ins, hxa, hax, hxb, hbx]
            rw [hEq]
            obtain rfl : x = b := le_antisymm (le_of_not_gt hbx) (le_of_not_gt hxb)
            refine ⟨⟨hOl, hOm, hOr, hab, hAl, hAmgt, hAmlt, hAr⟩, ?_⟩
            simp only [flatten_node3]
            rw [orderedInsert_append_right hax _ _ hBlx,
              orderedInsert_append_eq _ _ _ hBmlt]
      · have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.ok (Tree.node3 a b l m r) := by
          simp [ins, hxa, hax]
        rw [hEq]
        obtain rfl : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        refine ⟨⟨hOl, hOm, hOr, hab, hAl, hAmgt, hAmlt, hAr⟩, ?_⟩
        simp only [flatten_node3]
        rw [orderedInsert_append_eq _ _ _ hBl]

/-- **2-3 trees of unspecified height.** For a type $\alpha$, a 2-3 tree of unspecified height
over $\alpha$ is a pair $(h, t)$ of a natural number $h$ and a height-indexed 2-3 tree $t$ over
$\alpha$ of height $h$.

It serves as a standalone search tree. -/
public structure Root (α : Type u) where
  /-- The height of the underlying tree. -/
  height : Nat
  /-- The underlying height-indexed tree. -/
  tree : Tree α height

/-- **Turning an insertion result into a 2-3 tree.** An insertion result at height $h$ becomes a
2-3 tree of unspecified height as follows: a tree $t$ of height $h$ gives $t$ itself, of height
$h$, and a split into trees $l$, $r$ of height $h$ around a key $k$ gives the 2-node with
separator $k$, left child $l$ and right child $r$, of height $h + 1$. -/
public def Overflow.toRoot : {h : Nat} → Overflow α h → Root α
  | _, .ok t => ⟨_, t⟩
  | _, .split l k r => ⟨_, .node2 k l r⟩

/-- **Empty 2-3 tree.** The empty 2-3 tree is the root of height $0$ whose underlying tree is
the leaf. -/
public def Root.empty : Root α :=
  ⟨0, Tree.leaf⟩

/-- **Inorder traversal of a 2-3 tree root.** The flattening of a 2-3 tree root is the
flattening of its underlying tree, that is, the list of its keys in inorder. -/
public def Root.flatten (t : Root α) : List α :=
  TwoThreeTree.flatten t.tree

/-- **Search in a rooted 2-3 tree.** For a linearly ordered key type, searching a root (a 2-3
tree packaged with its height) for a key $x$ returns the Boolean result of the 2-3 tree search
for $x$ in the underlying height-indexed tree. -/
public def Root.contains [LinearOrder α] (x : α) (t : Root α) : Bool :=
  TwoThreeTree.contains x t.tree

/-- **Ordering invariant for 2-3 trees of unspecified height.** Let $\alpha$ be a type with a
relation $<$. A 2-3 tree of unspecified height over $\alpha$ is ordered when its underlying
height-indexed 2-3 tree satisfies the ordering invariant. -/
public def Root.Ordered [LT α] (t : Root α) : Prop :=
  TwoThreeTree.Ordered t.tree

/-- **Insertion into a 2-3 tree root.** To insert a key $x$ into a root, that is, a 2-3 tree
together with its height $h$, insert $x$ into the underlying tree. If this returns a single tree
of height $h$, that tree is the new root, of height $h$. If it returns a split into trees $l$
and $r$ around a key $k$, the new root is the 2-node with key $k$ and children $l$ and $r$, of
height $h + 1$. -/
public def Root.insert [LinearOrder α] (x : α) (t : Root α) : Root α :=
  Overflow.toRoot (ins x t.tree)

/-- **The empty 2-3 tree is ordered.** For every type $\alpha$ with a relation $<$, the empty
2-3 tree of unspecified height over $\alpha$ (the leaf, of height $0$) satisfies the ordering
invariant. -/
public theorem Root.ordered_empty [LT α] : (Root.empty : Root α).Ordered :=
  trivial

@[simp] public theorem Root.flatten_empty :
    (Root.empty : Root α).flatten = [] :=
  rfl

/-- **The stored height of a 2-3 tree root is its computed height.** For every root $t$, that
is, a 2-3 tree together with its height index, the height of the underlying tree computed along
its leftmost spine equals the stored height of $t$. -/
public theorem Root.height_tree (t : Root α) :
    TwoThreeTree.height t.tree = t.height :=
  height_eq t.tree

/-- **Every rooted 2-3 tree is balanced.** For every root, that is, a 2-3 tree packaged with its
height, the underlying height-indexed tree satisfies the balance invariant. -/
public theorem Root.balanced (t : Root α) : Balanced t.tree :=
  TwoThreeTree.balanced t.tree

/-- **Insertion preserves the ordering of 2-3 trees.** Let $\alpha$ be a linearly ordered type.
If $t$ is an ordered 2-3 tree of unspecified height over $\alpha$ and $x \in \alpha$, then the
tree obtained by inserting $x$ into $t$ is ordered. -/
public theorem Root.ordered_insert [LinearOrder α] {x : α} {t : Root α}
    (hOrd : t.Ordered) : (t.insert x).Ordered := by
  have hSpec := ins_spec x t.tree hOrd
  cases hins : ins x t.tree with
  | ok t' =>
    rw [hins] at hSpec
    obtain ⟨hOrd', -⟩ := hSpec
    have hIns : t.insert x = (⟨t.height, t'⟩ : Root α) := by
      simp [Root.insert, Overflow.toRoot, hins]
    rw [hIns]
    exact hOrd'
  | split l k r =>
    rw [hins] at hSpec
    obtain ⟨hOl, hOr, hAl, hAr, -⟩ := hSpec
    have hIns : t.insert x = (⟨t.height + 1, Tree.node2 k l r⟩ : Root α) := by
      simp [Root.insert, Overflow.toRoot, hins]
    rw [hIns]
    exact ⟨hOl, hOr, hAl, hAr⟩

/-- **Insertion into a 2-3 tree is ordered insertion into its traversal.** Let the keys be
linearly ordered, let $t$ be an ordered 2-3 tree root and let $x$ be a key. Then the flattening
of the root obtained by inserting $x$ into $t$ equals the ordered insertion of $x$ into the
flattening of $t$. -/
public theorem Root.flatten_insert [LinearOrder α] {x : α} {t : Root α}
    (hOrd : t.Ordered) : (t.insert x).flatten = orderedInsert x t.flatten := by
  have hSpec := ins_spec x t.tree hOrd
  cases hins : ins x t.tree with
  | ok t' =>
    rw [hins] at hSpec
    obtain ⟨-, hf⟩ := hSpec
    have hIns : t.insert x = (⟨t.height, t'⟩ : Root α) := by
      simp [Root.insert, Overflow.toRoot, hins]
    rw [hIns]
    exact hf
  | split l k r =>
    rw [hins] at hSpec
    obtain ⟨-, -, -, -, hf⟩ := hSpec
    have hIns : t.insert x = (⟨t.height + 1, Tree.node2 k l r⟩ : Root α) := by
      simp [Root.insert, Overflow.toRoot, hins]
    rw [hIns]
    show TwoThreeTree.flatten (Tree.node2 k l r) =
      orderedInsert x (TwoThreeTree.flatten t.tree)
    rw [flatten_node2]
    exact hf

/-- **Keys after insertion into a 2-3 tree.** Let $\alpha$ be linearly ordered and let $t$ be an
ordered 2-3 tree root over $\alpha$. For all $x, y \in \alpha$, $y$ occurs in the inorder
traversal of the root obtained by inserting $x$ into $t$ if and only if $y = x$ or $y$ occurs in
the inorder traversal of $t$. -/
public theorem Root.mem_flatten_insert [LinearOrder α] {x y : α} {t : Root α}
    (hOrd : t.Ordered) : y ∈ (t.insert x).flatten ↔ y = x ∨ y ∈ t.flatten := by
  rw [Root.flatten_insert hOrd, mem_orderedInsert]

/-- **Search in a rooted 2-3 tree is correct.** Let the keys be linearly ordered and let $t$ be
a root (a 2-3 tree packaged with its height) whose underlying tree satisfies the ordering
invariant. Then searching $t$ for a key $x$ returns true if and only if $x$ occurs in the
inorder flattening of $t$. -/
public theorem Root.contains_eq_true_iff [LinearOrder α] {x : α} {t : Root α}
    (hOrd : t.Ordered) : t.contains x = true ↔ x ∈ t.flatten :=
  TwoThreeTree.contains_eq_true_iff hOrd

/-- **Insertion raises the height of a 2-3 tree by at most one.** For linearly ordered keys,
every key $x$ and every 2-3 tree root $t$, the stored height of the root obtained by inserting
$x$ into $t$ is at most the stored height of $t$ plus one. -/
public theorem Root.height_insert_le [LinearOrder α] (x : α) (t : Root α) :
    (t.insert x).height ≤ t.height + 1 := by
  cases hins : ins x t.tree <;> simp [Root.insert, Overflow.toRoot, hins]

/-- **Building a 2-3 tree from a list.** For linearly ordered keys, the 2-3 tree root built from
a list is defined by recursion: the empty list gives the empty 2-3 tree, and a list with head $x$
and tail $xs$ gives the result of inserting $x$ into the root built from $xs$. Thus the elements
are inserted into the empty tree from the last to the first. -/
public def Root.fromList [LinearOrder α] : List α → Root α
  | [] => .empty
  | x :: xs => Root.insert x (Root.fromList xs)

/-- **Building a 2-3 tree from a list gives an ordered tree.** Let $\alpha$ be a linearly ordered
type. For every list $L$ of elements of $\alpha$, the 2-3 tree of unspecified height built from
$L$, by inserting the elements of $L$ from right to left into the empty tree, is ordered. -/
public theorem Root.ordered_fromList [LinearOrder α] (xs : List α) :
    (Root.fromList xs).Ordered := by
  induction xs with
  | nil => exact Root.ordered_empty
  | cons _ _ ih => exact Root.ordered_insert ih

/-- **Keys of a 2-3 tree built from a list.** Let $\alpha$ be linearly ordered. For every list
$L$ over $\alpha$ and every $x \in \alpha$, $x$ occurs in the inorder traversal of the 2-3 tree
built from $L$ (by inserting its elements from right to left into the empty tree) if and only
if $x$ occurs in $L$. -/
public theorem Root.mem_fromList [LinearOrder α] {x : α} {xs : List α} :
    x ∈ (Root.fromList xs).flatten ↔ x ∈ xs := by
  induction xs with
  | nil => simp [Root.fromList]
  | cons y ys ih =>
    show x ∈ ((Root.fromList ys).insert y).flatten ↔ x ∈ y :: ys
    rw [Root.mem_flatten_insert (Root.ordered_fromList ys), ih]
    simp only [List.mem_cons]

example : (Root.insert 3 (Root.insert 1
    (Root.insert 2 (Root.empty : Root Nat)))).flatten = [1, 2, 3] := by
  have h0 : (Root.empty : Root Nat).Ordered := Root.ordered_empty
  have h1 : ((Root.empty : Root Nat).insert 2).Ordered :=
    Root.ordered_insert h0
  have h2 : (((Root.empty : Root Nat).insert 2).insert 1).Ordered :=
    Root.ordered_insert h1
  rw [Root.flatten_insert h2, Root.flatten_insert h1, Root.flatten_insert h0,
    Root.flatten_empty]
  rfl

/-- Deprecated forwarder for the shared `Cslib.Algorithms.Lean.orderedInsert`.
Kept so existing fully qualified references to `TwoThreeTree.orderedInsert`
keep elaborating; new code should use the shared name. -/
@[deprecated "use Cslib.Algorithms.Lean.orderedInsert instead"
  (since := "2026-10-12")]
public def orderedInsert [LinearOrder α] (x : α) : List α → List α :=
  Cslib.Algorithms.Lean.orderedInsert x

/-- Deprecated forwarder for the shared `Cslib.Algorithms.Lean.mem_orderedInsert`. -/
@[deprecated "use Cslib.Algorithms.Lean.mem_orderedInsert instead"
  (since := "2026-10-12")]
public theorem mem_orderedInsert [LinearOrder α] {x y : α} {xs : List α} :
    y ∈ orderedInsert x xs ↔ y = x ∨ y ∈ xs :=
  Cslib.Algorithms.Lean.mem_orderedInsert

end TwoThreeTree
end Cslib.Algorithms.Lean
