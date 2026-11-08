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

/-- A segment tree: empty, a single leaf, or a node caching its segment aggregate
and segment length next to its two children. -/
inductive SegmentTree (α : Type u) where
  | empty : SegmentTree α
  | leaf : α → SegmentTree α
  | node : α → Nat → SegmentTree α → SegmentTree α → SegmentTree α

namespace SegmentTree

/-- The cached aggregate of a tree; the empty tree has aggregate `0`. -/
def agg {α : Type u} [AddMonoid α] : SegmentTree α → α
  | .empty => 0
  | .leaf x => x
  | .node cached _ _ _ => cached

/-- The number of leaves of a tree, i.e. the length of its segment. Internal
nodes answer from the cached length, in constant time; `Valid` records that the
cache is honest. -/
def size {α : Type u} : SegmentTree α → Nat
  | .empty => 0
  | .leaf _ => 1
  | .node _ cachedSize _ _ => cachedSize

/-- Accumulator traversal threading the output suffix, so collecting the
leaves of an `n`-leaf tree takes linear time instead of repeatedly
appending (and copying) left-subtree results. -/
def toListAux {α : Type u} : SegmentTree α → List α → List α
  | .empty, acc => acc
  | .leaf x, acc => x :: acc
  | .node _ _ left right, acc => left.toListAux (right.toListAux acc)

/-- The leaf values of a tree from left to right. -/
def toList {α : Type u} (t : SegmentTree α) : List α :=
  t.toListAux []

/-- The accumulator traversal prepends exactly the tree's leaves. -/
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

/-- Characteristic equation for `toList` at an internal node; with the
accumulator definition this is a theorem, not a definitional unfolding. -/
@[simp]
theorem toList_node {α : Type u} (agg : α) (sz : Nat) (left right : SegmentTree α) :
    (SegmentTree.node agg sz left right).toList = left.toList ++ right.toList := by
  show left.toListAux (right.toListAux []) = left.toList ++ right.toList
  rw [toListAux_eq, toListAux_eq, List.append_nil]

/-- A valid tree has every cached aggregate equal to the sum of its children's
aggregates and every cached length equal to the sum of its children's lengths. -/
inductive Valid {α : Type u} [AddMonoid α] : SegmentTree α → Prop where
  | empty : Valid .empty
  | leaf (x : α) : Valid (.leaf x)
  | node {left right : SegmentTree α} (hLeft : Valid left)
      (hRight : Valid right) :
      Valid (.node (left.agg + right.agg) (left.size + right.size) left right)

/-- In a valid tree the cached size is the length of the leaf list. -/
theorem length_toList_of_valid {α : Type u} [AddMonoid α] {t : SegmentTree α}
    (h : t.Valid) : t.toList.length = t.size := by
  induction h with
  | empty => rfl
  | leaf _ => rfl
  | node _ _ ihLeft ihRight => simp [size, ihLeft, ihRight]

/-- In a valid tree the cached root aggregate is the sum of the leaf list. -/
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

/-- Builds a segment tree from a list by recursively splitting the list in half. -/
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

/-- A tree built from a list is valid. -/
theorem valid_build {α : Type u} [AddMonoid α] (xs : List α) :
    (build xs).Valid :=
  (build_spec (α := α) xs).1

/-- The leaf list of a tree built from a list is that list. -/
@[simp]
theorem toList_build {α : Type u} [AddMonoid α] (xs : List α) :
    (build xs).toList = xs :=
  (build_spec (α := α) xs).2

/-- The size of a tree built from a list is the length of that list. -/
@[simp]
theorem size_build {α : Type u} [AddMonoid α] (xs : List α) :
    (build xs).size = xs.length := by
  rw [← length_toList_of_valid (valid_build xs), toList_build]

/-- The root aggregate of a tree built from a list is the sum of that list. -/
theorem agg_build {α : Type u} [AddMonoid α] (xs : List α) :
    (build xs).agg = xs.sum := by
  calc
    (build xs).agg = (build xs).toList.sum :=
      agg_eq_sum_toList (valid_build xs)
    _ = xs.sum := by rw [toList_build]

/--
The range aggregate over `[l, r)`, with indices relative to the tree's segment.

An empty range and a node disjoint from the range on either side contribute
`0` without descending, a fully covered node contributes its cached aggregate,
and otherwise the query recurses into both children.
-/
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

/-- A range query on a valid tree is the sum of the corresponding list slice. -/
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

/-- A range query on a tree built from a list is the sum of the list slice. -/
theorem query_build {α : Type u} [AddMonoid α] (xs : List α) (l r : Nat) :
    (build xs).query l r = ((xs.drop l).take (r - l)).sum := by
  rw [query_eq (valid_build xs), toList_build]

/--
Point update: replaces the leaf at a relative index and recomputes cached
aggregates on the path back to the root.
-/
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

/-- Point update does not change the size of a tree: every node on the update
path keeps its cached segment length. -/
@[simp]
theorem size_update {α : Type u} [AddMonoid α] (t : SegmentTree α)
    (i : Nat) (y : α) : (t.update i y).size = t.size := by
  induction t generalizing i with
  | empty => rfl
  | leaf _ => by_cases hi : i = 0 <;> simp [update, hi, size]
  | node _ _ _ _ _ _ =>
      unfold update
      split <;> rfl

/-- Point update preserves validity. -/
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

/-- Point update at an in-range index of a valid tree updates the leaf list at
that index. Validity is what ties the cached sizes used for routing to the
leaf list. -/
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

/-- Point update at an out-of-range index of a valid tree leaves the leaf
list unchanged. -/
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

/-- Updating a tree built from a list updates that list at the index. -/
theorem toList_update_build {α : Type u} [AddMonoid α] {xs : List α}
    {i : Nat} (hi : i < xs.length) (y : α) :
    ((build xs).update i y).toList = xs.set i y := by
  have hiSize : i < (build xs).size := by
    rw [size_build]
    exact hi
  rw [toList_update_of_lt (valid_build xs) hiSize y, toList_build]

/-- The root aggregate after updating a built tree is the sum of the updated list. -/
theorem agg_update_build {α : Type u} [AddMonoid α] {xs : List α}
    {i : Nat} (hi : i < xs.length) (y : α) :
    ((build xs).update i y).agg = (xs.set i y).sum := by
  rw [agg_eq_sum_toList ((valid_build xs).update i y), toList_update_build hi y]

/-- A range query after updating a built tree is the slice sum of the updated list. -/
theorem query_update_build {α : Type u} [AddMonoid α] {xs : List α}
    {i : Nat} (hi : i < xs.length) (y : α) (l r : Nat) :
    ((build xs).update i y).query l r =
      (((xs.set i y).drop l).take (r - l)).sum := by
  rw [query_eq ((valid_build xs).update i y), toList_update_build hi y]

end SegmentTree

end Cslib.Algorithms.Lean
