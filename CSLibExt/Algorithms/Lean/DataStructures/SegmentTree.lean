/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Segment trees

This file defines a segment tree over a list with values in an additive monoid;
the aggregate of a list is its `List.sum`, accumulated from left to right, so no
commutativity is required. Each internal node caches the aggregate and the length
of its segment, and `Valid` records that every cached aggregate equals the sum of
the children's aggregates and every cached length equals the sum of the children's
lengths, so split positions are available in constant time. The index set of a tree
is the inorder leaf list `toList`. A range query over `[l, r)` returns the sum of
the slice `(toList.drop l).take (r - l)`; it prunes empty, left-disjoint, and
right-disjoint segments, uses cached aggregates for fully covered nodes, and clamps
out-of-range bounds through the slice. Point update replaces the in-range leaf at
an index and leaves the leaf list unchanged out of range. Building splits the list
in half recursively, evaluating each recursive build once. No complexity bounds
are proved.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/-- **Segment tree.** A segment tree with values in $\alpha$ is either empty, a leaf holding a
value in $\alpha$, or an internal node holding a cached segment aggregate in $\alpha$, a cached
segment length in $\mathbb{N}$, a left child and a right child, both segment trees. -/
inductive SegmentTree (α : Type u) where
  | empty : SegmentTree α
  | leaf : α → SegmentTree α
  | node : α → Nat → SegmentTree α → SegmentTree α → SegmentTree α

namespace SegmentTree

/-- **Aggregate of a segment tree.** The aggregate of a segment tree with values in an additive
monoid is $0$ for the empty tree, $x$ for a single leaf with value $x$, and the aggregate cached at
the root for an internal node. -/
def agg {α : Type u} [AddMonoid α] : SegmentTree α → α
  | .empty => 0
  | .leaf x => x
  | .node cached _ _ _ => cached

/-- **Size of a segment tree.** The size of a segment tree is $0$ for the empty tree, $1$ for a
leaf, and, for an internal node, the segment length cached at that node.

When every cached length is the sum of the sizes of the node's children, this is the number of
leaves, and internal nodes answer in constant time. -/
def size {α : Type u} : SegmentTree α → Nat
  | .empty => 0
  | .leaf _ => 1
  | .node _ cachedSize _ _ => cachedSize

/-- **Accumulator traversal of a segment tree.** Given a segment tree and a list $acc$, the
accumulator traversal returns $acc$ for the empty tree, the list $acc$ with $x$ prepended for a
leaf with value $x$, and, for an internal node with left child $L$ and right child $R$, the
traversal of $L$ starting from the result of the traversal of $R$ starting from $acc$.

Threading the output suffix this way collects the leaves of an $n$-leaf tree in linear time
instead of repeatedly appending (and copying) left-subtree results. -/
def toListAux {α : Type u} : SegmentTree α → List α → List α
  | .empty, acc => acc
  | .leaf x, acc => x :: acc
  | .node _ _ left right, acc => left.toListAux (right.toListAux acc)

/-- **Leaf list of a segment tree.** The leaf list of a segment tree is the list of its leaf
values from left to right: the empty list for the empty tree, $[x]$ for a leaf with value $x$,
and the leaf list of the left child followed by the leaf list of the right child for an
internal node. -/
def toList {α : Type u} (t : SegmentTree α) : List α :=
  t.toListAux []

/-- **Accumulator traversal prepends the leaf list.** For every segment tree $t$ and every list
$acc$, the accumulator traversal of $t$ starting from $acc$ returns the leaf list of $t$ followed
by $acc$. -/
@[simp]
theorem toListAux_eq {α : Type u} (t : SegmentTree α) (acc : List α) :
    t.toListAux acc = t.toList ++ acc := by
  induction t generalizing acc with
  | empty => rfl
  | leaf _ => rfl
  | node agg sz left right ihLeft ihRight =>
      show left.toListAux (right.toListAux acc) =
        (SegmentTree.node agg sz left right).toList ++ acc
      rw [ihLeft, ihRight]
      have hnode : (SegmentTree.node agg sz left right).toList =
          left.toList ++ right.toList := by
        show left.toListAux (right.toListAux []) = left.toList ++ right.toList
        rw [ihLeft, ihRight, List.append_nil]
      rw [hnode, List.append_assoc]

@[simp]
theorem toList_empty {α : Type u} : (SegmentTree.empty : SegmentTree α).toList = [] :=
  rfl

@[simp]
theorem toList_leaf {α : Type u} (x : α) : (SegmentTree.leaf x).toList = [x] :=
  rfl

/-- **Leaf list of an internal node.** For every internal node of a segment tree, with any cached
aggregate, any cached length, left child $L$ and right child $R$, its leaf list is the leaf list
of $L$ followed by the leaf list of $R$.

With the accumulator definition of the leaf list this is a theorem, not a definitional
unfolding. -/
@[simp]
theorem toList_node {α : Type u} (agg : α) (sz : Nat) (left right : SegmentTree α) :
    (SegmentTree.node agg sz left right).toList = left.toList ++ right.toList := by
  show left.toListAux (right.toListAux []) = left.toList ++ right.toList
  rw [toListAux_eq, toListAux_eq, List.append_nil]

/-- **Valid segment trees.** Validity of a segment tree over an additive monoid is defined
inductively: the empty tree and every leaf are valid, and an internal node with valid left child
$L$ and valid right child $R$ is valid when its cached aggregate is the aggregate of $L$ plus
the aggregate of $R$ and its cached length is the size of $L$ plus the size of $R$. Here the
aggregate and size of the empty tree are $0$ and $0$, of a leaf with value $x$ are $x$ and $1$,
and of an internal node are its cached aggregate and cached length. -/
inductive Valid {α : Type u} [AddMonoid α] : SegmentTree α → Prop where
  | empty : Valid .empty
  | leaf (x : α) : Valid (.leaf x)
  | node {left right : SegmentTree α} (hLeft : Valid left)
      (hRight : Valid right) :
      Valid (.node (left.agg + right.agg) (left.size + right.size) left right)

/-- **Size of a valid segment tree.** If $t$ is a valid segment tree with values in an additive
monoid, then the length of the list of leaf values of $t$, read from left to right, equals the
size of $t$. -/
theorem length_toList_of_valid {α : Type u} [AddMonoid α] {t : SegmentTree α}
    (h : t.Valid) : t.toList.length = t.size := by
  induction h with
  | empty => rfl
  | leaf _ => rfl
  | node _ _ ihLeft ihRight => simp [size, ihLeft, ihRight]

/-- **Aggregate of a valid segment tree.** If $t$ is a valid segment tree with values in an
additive monoid, then the aggregate of $t$ equals the sum of the leaf values of $t$, taken from
left to right. -/
theorem agg_eq_sum_toList {α : Type u} [AddMonoid α] {t : SegmentTree α}
    (h : t.Valid) : t.agg = t.toList.sum := by
  induction t with
  | empty => rfl
  | leaf x => simp [agg]
  | node _ _ left right ihLeft ihRight =>
      cases h with
      | node hLeft hRight =>
          rw [toList_node]
          show left.agg + right.agg = (left.toList ++ right.toList).sum
          rw [List.sum_append, ihLeft hLeft, ihRight hRight]

/-- **Building a segment tree from a list.** The segment tree built from a list $L$ with entries
in an additive monoid is the empty tree if $L$ is empty, and a single leaf with value $x$ if
$L = (x)$. If $L$ has length $n \ge 2$, it is the internal node whose left child is the tree built
from the first $\lfloor n/2 \rfloor$ entries of $L$, whose right child is the tree built from the
remaining entries, and which caches the aggregate of the left child plus the aggregate of the
right child, in that order, and the sum of the sizes of its children. -/
def build {α : Type u} [AddMonoid α] : List α → SegmentTree α
  | [] => .empty
  | [x] => .leaf x
  | xs@(_ :: _ :: _) =>
      let left := build (xs.take (xs.length / 2))
      let right := build (xs.drop (xs.length / 2))
      .node (left.agg + right.agg) (left.size + right.size) left right
termination_by xs => xs.length
decreasing_by
  all_goals
    simp_all only [List.length_take, List.length_drop, List.length_cons]
    omega

private theorem build_spec {α : Type u} [AddMonoid α] :
    ∀ xs : List α, (build xs).Valid ∧ (build xs).toList = xs := by
  intro xs
  induction hn : xs.length using Nat.strongRecOn generalizing xs with
  | _ n ih =>
      cases xs with
      | nil =>
          rw [build]
          exact ⟨Valid.empty, rfl⟩
      | cons x xs =>
          cases xs with
          | nil =>
              rw [build]
              exact ⟨Valid.leaf x, rfl⟩
          | cons y ys =>
              have htake :
                  ((x :: y :: ys).take ((x :: y :: ys).length / 2)).length < n := by
                rw [← hn]
                simp only [List.length_take, List.length_cons]
                omega
              have hdrop :
                  ((x :: y :: ys).drop ((x :: y :: ys).length / 2)).length < n := by
                rw [← hn]
                simp only [List.length_drop, List.length_cons]
                omega
              have hLeft := ih _ htake _ rfl
              have hRight := ih _ hdrop _ rfl
              rw [build]
              exact ⟨Valid.node hLeft.1 hRight.1, by
                rw [toList_node]
                rw [hLeft.2, hRight.2]
                exact List.take_append_drop _ _⟩

/-- **Built segment trees are valid.** For every list $xs$ over an additive monoid, the segment
tree built from $xs$ is valid. -/
theorem valid_build {α : Type u} [AddMonoid α] (xs : List α) :
    (build xs).Valid :=
  (build_spec (α := α) xs).1

/-- **Building a segment tree preserves the list.** For every list $xs$ with entries in an
additive monoid, the leaf list of the segment tree built from $xs$ is $xs$. -/
@[simp]
theorem toList_build {α : Type u} [AddMonoid α] (xs : List α) :
    (build xs).toList = xs :=
  (build_spec (α := α) xs).2

/-- **Size of a built segment tree.** For every list $xs$ with entries in an additive monoid, the
segment tree built from $xs$ has size equal to the length of $xs$. -/
@[simp]
theorem size_build {α : Type u} [AddMonoid α] (xs : List α) :
    (build xs).size = xs.length := by
  rw [← length_toList_of_valid (valid_build xs), toList_build]

/-- **Aggregate of a built segment tree.** For every list $L$ with entries in an additive
monoid, the aggregate of the segment tree built from $L$ equals the sum of the entries of $L$,
taken from left to right. -/
theorem agg_build {α : Type u} [AddMonoid α] (xs : List α) :
    (build xs).agg = xs.sum := by
  calc
    (build xs).agg = (build xs).toList.sum :=
      agg_eq_sum_toList (valid_build xs)
    _ = xs.sum := by rw [toList_build]

/-- **Range query on a segment tree.** For a segment tree $t$ with values in an additive monoid
and natural numbers $l, r$, the range query over $[l, r)$, with positions counted from the start
of the segment of $t$, is defined recursively. On the empty tree it is $0$. On a leaf with value
$x$ it is $x$ if $l = 0 < r$, and $0$ otherwise. On an internal node with cached aggregate $a$,
cached size $s$ and children $t_1, t_2$, it is $0$ if $r \le l$ or $s \le l$; otherwise it is $a$
if $l = 0$ and $s \le r$; and in all remaining cases it is the query over $[l, r)$ on $t_1$ plus
the query over $[l - m, r - m)$ on $t_2$, where $m$ is the size of $t_1$ and subtraction is
truncated at $0$.

An empty range and a node disjoint from the range contribute $0$ without descending, and a fully
covered node contributes its cached aggregate. -/
def query {α : Type u} [AddMonoid α] : SegmentTree α → Nat → Nat → α
  | .empty, _, _ => 0
  | .leaf x, l, r => if l = 0 ∧ 0 < r then x else 0
  | .node cached segmentSize left right, l, r =>
      if r ≤ l then 0
      else if segmentSize ≤ l then 0
      else if l = 0 ∧ segmentSize ≤ r then cached
      else query left l r + query right (l - left.size) (r - left.size)

private theorem sum_take_drop_append {α : Type u} [AddMonoid α]
    (xs ys : List α) (l r : Nat) :
    (((xs ++ ys).drop l).take (r - l)).sum =
      ((xs.drop l).take (r - l)).sum +
        ((ys.drop (l - xs.length)).take
          ((r - xs.length) - (l - xs.length))).sum := by
  have hcount : (r - l) - (xs.length - l) =
      (r - xs.length) - (l - xs.length) := by
    omega
  rw [List.drop_append, List.take_append, List.length_drop, hcount,
    List.sum_append]

/-- **Correctness of range queries on a valid segment tree.** Let $t$ be a valid segment tree with
values in an additive monoid, let $(x_0, \dots, x_{n-1})$ be its leaf values from left to right,
and let $l, r$ be natural numbers. The range query over $[l, r)$ on $t$ returns
$\sum_{l \le k < \min(r, n)} x_k$, the sum taken in increasing order of $k$; it is $0$ when
$\min(r, n) \le l$. -/
theorem query_eq {α : Type u} [AddMonoid α] {t : SegmentTree α}
    (h : t.Valid) (l r : Nat) :
    t.query l r = ((t.toList.drop l).take (r - l)).sum := by
  induction t generalizing l r with
  | empty => simp [query]
  | leaf x =>
      cases l with
      | zero =>
          cases r with
          | zero => simp [query]
          | succ r => simp [query]
      | succ l => simp [query]
  | node _ _ left right ihLeft ihRight =>
      cases h with
      | node hLeft hRight =>
          by_cases hEmpty : r ≤ l
          · simp [query, hEmpty]
          · by_cases hDisj : left.size + right.size ≤ l
            · have hLen : (left.toList ++ right.toList).length ≤ l := by
                rw [List.length_append, length_toList_of_valid hLeft,
                  length_toList_of_valid hRight]
                exact hDisj
              have hDrop := List.drop_of_length_le hLen
              simp [query, hEmpty, hDisj, hDrop]
            · by_cases hFull : l = 0 ∧ left.size + right.size ≤ r
              · obtain ⟨rfl, hLe⟩ := hFull
                have hEmpty0 : ¬r ≤ 0 := by
                  intro hr
                  exact hEmpty (Nat.le_trans hr (Nat.zero_le _))
                have hLen : (left.toList ++ right.toList).length ≤ r := by
                  rw [List.length_append, length_toList_of_valid hLeft,
                    length_toList_of_valid hRight]
                  exact hLe
                have hTake := List.take_of_length_le hLen
                simp [query, hEmpty0, hDisj, hLe, hTake,
                  agg_eq_sum_toList hLeft, agg_eq_sum_toList hRight]
              · simp only [query, toList_node]
                rw [ite_eq_right hEmpty, ite_eq_right hDisj,
                  ite_eq_right hFull, ihLeft hLeft, ihRight hRight,
                  sum_take_drop_append, length_toList_of_valid hLeft]

/-- **Range queries on a built segment tree.** Let $L = (x_0, \dots, x_{n-1})$ be a list with
entries in an additive monoid and let $l, r$ be natural numbers. The range query over $[l, r)$ on
the segment tree built from $L$ returns $\sum_{l \le k < \min(r, n)} x_k$, the sum taken in
increasing order of $k$; it is $0$ when $\min(r, n) \le l$. -/
theorem query_build {α : Type u} [AddMonoid α] (xs : List α) (l r : Nat) :
    (build xs).query l r = ((xs.drop l).take (r - l)).sum := by
  rw [query_eq (valid_build xs), toList_build]

/-- **Point update of a segment tree.** The point update of a segment tree over an additive
monoid at an index $i \in \mathbb{N}$, relative to the tree's segment, with a value $y$ is
defined recursively. The empty tree stays empty. A leaf becomes a leaf with value $y$ if $i = 0$
and is unchanged otherwise. At an internal node with left child $L$ and right child $R$: if $i$
is less than the size of $L$, then $L$ is replaced by its point update at $i$ with $y$, and
otherwise $R$ is replaced by its point update at $i$ minus the size of $L$ with $y$; the node
keeps its cached length, and its cached aggregate becomes the aggregate of the new left child
plus the aggregate of the new right child. -/
def update {α : Type u} [AddMonoid α] : SegmentTree α → Nat → α → SegmentTree α
  | .empty, _, _ => .empty
  | .leaf x, i, y => if i = 0 then .leaf y else .leaf x
  | .node _ segmentSize left right, i, y =>
      if i < left.size then
        let left' := left.update i y
        .node (left'.agg + right.agg) segmentSize left' right
      else
        let right' := right.update (i - left.size) y
        .node (left.agg + right'.agg) segmentSize left right'

/-- **Point update preserves the size of a segment tree.** For every segment tree $t$ over an
additive monoid, every index $i$ and every value $y$, the point update of $t$ at $i$ with $y$
has the same size as $t$.

Every node on the update path keeps its cached segment length. -/
@[simp]
theorem size_update {α : Type u} [AddMonoid α] (t : SegmentTree α)
    (i : Nat) (y : α) : (t.update i y).size = t.size := by
  induction t generalizing i with
  | empty => rfl
  | leaf _ => by_cases hi : i = 0 <;> simp [update, hi, size]
  | node _ _ _ _ _ _ =>
      unfold update
      split <;> rfl

/-- **Point update preserves validity.** If $t$ is a valid segment tree over an additive monoid,
then for every natural number $i$ and every value $y$, the point update of $t$ at $i$ with $y$ is
valid. -/
theorem Valid.update {α : Type u} [AddMonoid α] {t : SegmentTree α}
    (h : t.Valid) (i : Nat) (y : α) : (t.update i y).Valid := by
  induction t generalizing i with
  | empty =>
      simp only [SegmentTree.update]
      exact Valid.empty
  | leaf x =>
      by_cases hi : i = 0
      · simp only [SegmentTree.update, ite_eq_left hi]
        exact Valid.leaf y
      · simp only [SegmentTree.update, ite_eq_right hi]
        exact Valid.leaf x
  | node _ _ left right ihLeft ihRight =>
      cases h with
      | node hLeft hRight =>
          by_cases hi : i < left.size
          · simp only [SegmentTree.update, ite_eq_left hi]
            rw [← size_update left i y]
            exact Valid.node (ihLeft hLeft i) hRight
          · simp only [SegmentTree.update, ite_eq_right hi]
            rw [← size_update right (i - left.size) y]
            exact Valid.node hLeft (ihRight hRight (i - left.size))

/-- **Leaf list after an in-range point update.** Let $t$ be a valid segment tree over an
additive monoid and let $i$ be a natural number less than the size of $t$. Then for every value
$y$, the leaf list of the point update of $t$ at $i$ with $y$ is the leaf list of $t$ with its
entry at position $i$ (counting from $0$) replaced by $y$.

Validity is what ties the cached sizes used for routing to the leaf list. -/
theorem toList_update_of_lt {α : Type u} [AddMonoid α] {t : SegmentTree α}
    (h : t.Valid) {i : Nat} (hi : i < t.size) (y : α) :
    (t.update i y).toList = t.toList.set i y := by
  induction t generalizing i with
  | empty => simp [size] at hi
  | leaf x =>
      have hi0 : i = 0 := by
        have hi1 : i < 1 := hi
        omega
      subst hi0
      rfl
  | node _ _ left right ihLeft ihRight =>
      cases h with
      | node hLeft hRight =>
          have hiSum : i < left.size + right.size := hi
          by_cases hL : i < left.size
          · have hLeftLen : i < left.toList.length := by
              rw [length_toList_of_valid hLeft]
              exact hL
            simp only [update, ite_eq_left hL, toList_node]
            rw [ihLeft hLeft hL, List.set_append_left i y hLeftLen]
          · have hBound : i - left.size < right.size := by omega
            have hLeLen : left.toList.length ≤ i := by
              rw [length_toList_of_valid hLeft]
              omega
            simp only [update, ite_eq_right hL, toList_node]
            rw [ihRight hRight hBound, List.set_append_right i y hLeLen,
              length_toList_of_valid hLeft]

/-- **Out-of-range point update leaves the leaf list unchanged.** For every valid segment tree $t$
over an additive monoid, every index $i$ at least the size of $t$ and every value $y$, the point
update of $t$ at $i$ with $y$ has the same leaf list as $t$. -/
theorem toList_update_of_le {α : Type u} [AddMonoid α] {t : SegmentTree α}
    (h : t.Valid) {i : Nat} (hi : t.size ≤ i) (y : α) :
    (t.update i y).toList = t.toList := by
  induction t generalizing i with
  | empty => rfl
  | leaf x =>
      have hi0 : i ≠ 0 := by
        have hi1 : 1 ≤ i := hi
        omega
      simp [update, hi0]
  | node _ _ left right _ ihRight =>
      cases h with
      | node _ hRight =>
          have hiSum : left.size + right.size ≤ i := hi
          have hNot : ¬i < left.size := by omega
          have hR : right.size ≤ i - left.size := by omega
          simp only [update, ite_eq_right hNot, toList_node, ihRight hRight hR]

/-- **Point update of a built segment tree.** For every list $xs$ with entries in an additive
monoid, every index $i$ smaller than the length of $xs$ and every value $y$, the leaf list of the
segment tree built from $xs$, after the point update at $i$ with $y$, is $xs$ with its entry at
position $i$ (counting from $0$) replaced by $y$. -/
theorem toList_update_build {α : Type u} [AddMonoid α] {xs : List α}
    {i : Nat} (hi : i < xs.length) (y : α) :
    ((build xs).update i y).toList = xs.set i y := by
  have hiSize : i < (build xs).size := by
    rw [size_build]
    exact hi
  rw [toList_update_of_lt (valid_build xs) hiSize y, toList_build]

/-- **Aggregate after a point update of a built segment tree.** Let $L = (x_0, \dots, x_{n-1})$
be a list with entries in an additive monoid, let $i < n$, and let $y$ be an element of the
monoid. Applying the point update at index $i$ with value $y$ to the segment tree built from $L$
gives a tree whose aggregate is the sum, taken from left to right, of the list obtained from $L$
by replacing $x_i$ with $y$. -/
theorem agg_update_build {α : Type u} [AddMonoid α] {xs : List α}
    {i : Nat} (hi : i < xs.length) (y : α) :
    ((build xs).update i y).agg = (xs.set i y).sum := by
  rw [agg_eq_sum_toList ((valid_build xs).update i y), toList_update_build hi y]

/-- **Range queries after a point update of a built segment tree.** Let $L = (x_0, \dots, x_{n-1})$
be a list with entries in an additive monoid, let $i < n$, let $y$ be an element of the monoid,
and let $L'$ be the list obtained from $L$ by replacing $x_i$ with $y$, with entries
$x'_0, \dots, x'_{n-1}$. Apply the point update at index $i$ with value $y$ to the segment tree
built from $L$. For all natural numbers $l, r$, the range query over $[l, r)$ on the result
returns $\sum_{l \le k < \min(r, n)} x'_k$, the sum taken in increasing order of $k$; it is $0$
when $\min(r, n) \le l$. -/
theorem query_update_build {α : Type u} [AddMonoid α] {xs : List α}
    {i : Nat} (hi : i < xs.length) (y : α) (l r : Nat) :
    ((build xs).update i y).query l r =
      (((xs.set i y).drop l).take (r - l)).sum := by
  rw [query_eq ((valid_build xs).update i y), toList_update_build hi y]

end SegmentTree

end Cslib.Algorithms.Lean
