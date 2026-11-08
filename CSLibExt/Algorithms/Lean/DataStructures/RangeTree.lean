/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.MinMax

/-!
# Range trees (1D)

This file defines a one-dimensional range tree over `Int`, following Demaine's
MIT 6.851 lecture 3 at the level of the verified report operation. The tree is a
balanced binary tree built from a list by recursively splitting it in half.
Each node caches the interval `[lo, hi]` spanned by its leaves, so the
pruning test at a node is constant-time (`tmin`/`tmax` are projections, not
recomputed traversals); `BoundsOk` records that the cached interval is the
true leaf interval, and the report theorem is stated for `BoundsOk` trees.
The classical leaf-order convention is the separate ordering invariant in
`Valid` (bounds plus sorted leaf list); `build` preserves the input order
verbatim, so `valid_build_of_sorted` gives `Valid (build xs)` under an
explicit `xs.Pairwise (· ≤ ·)` hypothesis — `build [2, 1]` is bounds-valid but
not `Valid`, and no theorem here identifies it with a sorted range tree.
A range report for `[lo, hi]`
prunes a node whose interval is disjoint from `[lo, hi]`, takes a node whose
interval is contained in `[lo, hi]` whole (the canonical-node step), and
otherwise recurses into both children. The main theorem states that the report
is exactly the inorder leaf list filtered to `[lo, hi]`; counting is the length
of the report.

## Main definitions

* `RangeTree.build` builds a balanced tree from a list by halving.
* `RangeTree.report` lists the stored values in `[lo, hi]`.
* `RangeTree.count` counts the stored values in `[lo, hi]`.

## Deferred

The two-dimensional layered range tree with fractional cascading, dynamic
updates, and all complexity bounds (`O(log n)` canonical nodes, and so on) are
not proved here; no cost model is carried.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

/-- A 1D range tree over `Int`: empty, a single leaf, or a binary node
caching the leaf interval `[lo, hi]` of its subtree. -/
inductive RangeTree where
  | empty : RangeTree
  | leaf : Int → RangeTree
  | node : Int → Int → RangeTree → RangeTree → RangeTree

namespace RangeTree

/-- Accumulator leaf traversal: `toListAux t acc = toList t ++ acc`, so
`toList` is linear rather than repeatedly appending left leaf lists. -/
def toListAux : RangeTree → List Int → List Int
  | .empty, acc => acc
  | .leaf x, acc => x :: acc
  | .node _ _ left right, acc => toListAux left (toListAux right acc)

/-- The leaf values of a tree from left to right. -/
def toList (t : RangeTree) : List Int :=
  toListAux t []

/-- The accumulator traversal appends the leaf list onto its accumulator. -/
theorem toListAux_eq (t : RangeTree) (acc : List Int) :
    toListAux t acc = t.toList ++ acc := by
  induction t generalizing acc with
  | empty => rfl
  | leaf x => rfl
  | node lo hi left right ihLeft ihRight =>
      have hnode : (RangeTree.node lo hi left right).toList =
          left.toList ++ right.toList := by
        rw [toList, toListAux, ihRight, ihLeft]
        simp
      rw [toListAux, ihRight, ihLeft, hnode, List.append_assoc]

/-- Characteristic node equation for `toList` (the former definition). -/
theorem toList_node (lo hi : Int) (left right : RangeTree) :
    (RangeTree.node lo hi left right).toList = left.toList ++ right.toList := by
  rw [toList, toListAux, toListAux_eq, toListAux_eq]
  simp

@[simp] theorem toList_empty : (RangeTree.empty).toList = [] := rfl
@[simp] theorem toList_leaf (x : Int) : (RangeTree.leaf x).toList = [x] := rfl

/-- The number of leaves of a tree. -/
def size : RangeTree → Nat
  | .empty => 0
  | .leaf _ => 1
  | .node _ _ left right => left.size + right.size

/-- The length of the leaf list is the size of the tree. -/
@[simp]
theorem length_toList (t : RangeTree) : t.toList.length = t.size := by
  induction t with
  | empty => rfl
  | leaf _ => rfl
  | node _ _ _ _ ihLeft ihRight => simp [toList_node, size, ihLeft, ihRight]

/-- The cached lower leaf bound; `0` for the empty tree (vacuous).
Constant-time: a projection of the node cache, not a traversal. -/
def tmin : RangeTree → Int
  | .empty => 0
  | .leaf x => x
  | .node lo _ _ _ => lo

/-- The cached upper leaf bound; `0` for the empty tree (vacuous). -/
def tmax : RangeTree → Int
  | .empty => 0
  | .leaf x => x
  | .node _ hi _ _ => hi

/-- The cached node intervals are the true leaf intervals:
at every node, `lo = min left.tmin right.tmin` and
`hi = max left.tmax right.tmax`, recursively. Node children must be
nonempty: `tmin`/`tmax` give the empty tree the sentinel `0`, so with an
empty child the node cache would only conservatively enclose the leaves
(for example `.node 0 5 .empty (.leaf 5)` would cache `[0, 5]` for the
single leaf `5`), not equal the true leaf interval. Together
`bounds_of_mem` and `bounds_mem_toList_of_ne_nil` show the cache is
exactly attained by leaves. -/
inductive BoundsOk : RangeTree → Prop where
  | empty : BoundsOk .empty
  | leaf (x : Int) : BoundsOk (.leaf x)
  | node {lo hi : Int} {left right : RangeTree} (hLeft : BoundsOk left)
      (hRight : BoundsOk right) (hLeftNe : left.toList ≠ [])
      (hRightNe : right.toList ≠ []) (hlo : lo = min left.tmin right.tmin)
      (hhi : hi = max left.tmax right.tmax) :
      BoundsOk (.node lo hi left right)

/-- Range-tree validity: correct cached bounds and sorted (classical)
leaf order. -/
def Valid (t : RangeTree) : Prop :=
  BoundsOk t ∧ t.toList.Pairwise (· ≤ ·)

/-- A valid tree has sorted leaf order. -/
theorem Valid.pairwise_toList {t : RangeTree} (h : Valid t) :
    t.toList.Pairwise (· ≤ ·) :=
  h.2

/-- Every leaf value of a bounds-valid tree lies in `[tmin, tmax]`. -/
theorem bounds_of_mem {t : RangeTree} (hb : BoundsOk t) {x : Int}
    (hx : x ∈ t.toList) :
    t.tmin ≤ x ∧ x ≤ t.tmax := by
  induction t with
  | empty => simp [toList_empty] at hx
  | leaf y =>
      have hxy : x = y := by simpa [toList_leaf] using hx
      subst hxy
      exact ⟨le_refl _, le_refl _⟩
  | node lo hi left right ihLeft ihRight =>
      cases hb with
      | node hLeft hRight _ _ hlo hhi =>
          rw [toList_node, List.mem_append] at hx
          change lo ≤ x ∧ x ≤ hi
          cases hx with
          | inl hx =>
              obtain ⟨h1, h2⟩ := ihLeft hLeft hx
              constructor
              · rw [hlo]; exact le_trans (min_le_left _ _) h1
              · rw [hhi]; exact le_trans h2 (le_max_left _ _)
          | inr hx =>
              obtain ⟨h1, h2⟩ := ihRight hRight hx
              constructor
              · rw [hlo]; exact le_trans (min_le_right _ _) h1
              · rw [hhi]; exact le_trans h2 (le_max_right _ _)

/-- The cached bounds of a nonempty bounds-valid tree are attained by
leaves, so `[tmin, tmax]` is the true leaf interval, not merely an
enclosing interval. -/
theorem bounds_mem_toList_of_ne_nil {t : RangeTree} (hb : BoundsOk t)
    (hne : t.toList ≠ []) :
    t.tmin ∈ t.toList ∧ t.tmax ∈ t.toList := by
  induction t with
  | empty => simp [toList_empty] at hne
  | leaf y =>
      exact ⟨by simp [toList_leaf, tmin], by simp [toList_leaf, tmax]⟩
  | node lo hi left right ihLeft ihRight =>
      cases hb with
      | node hLeft hRight hLeftNe hRightNe hlo hhi =>
          obtain ⟨hlMin, hlMax⟩ := ihLeft hLeft hLeftNe
          obtain ⟨hrMin, hrMax⟩ := ihRight hRight hRightNe
          refine ⟨?_, ?_⟩ <;> rw [toList_node, List.mem_append]
          · change lo ∈ left.toList ∨ lo ∈ right.toList
            rw [hlo]
            cases le_total left.tmin right.tmin with
            | inl h => rw [min_eq_left h]; exact Or.inl hlMin
            | inr h => rw [min_eq_right h]; exact Or.inr hrMin
          · change hi ∈ left.toList ∨ hi ∈ right.toList
            rw [hhi]
            cases le_total left.tmax right.tmax with
            | inl h => rw [max_eq_right h]; exact Or.inr hrMax
            | inr h => rw [max_eq_left h]; exact Or.inl hlMax

private theorem filter_eq_nil_of_all {xs : List Int} {lo hi : Int}
    (h : ∀ x ∈ xs, ¬(lo ≤ x ∧ x ≤ hi)) :
    xs.filter (fun x => lo ≤ x ∧ x ≤ hi) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  simpa using h x hx

private theorem filter_eq_self_of_all {xs : List Int} {lo hi : Int}
    (h : ∀ x ∈ xs, lo ≤ x ∧ x ≤ hi) :
    xs.filter (fun x => lo ≤ x ∧ x ≤ hi) = xs := by
  rw [List.filter_eq_self]
  intro x hx
  simpa using h x hx

/--
Accumulator range report for `[lo, hi]`: a node whose cached interval is
disjoint from the query contributes nothing, a node contained in it
contributes its whole leaf list onto the accumulator (the canonical-node
case, via the linear `toListAux`), and otherwise both children are
searched. The cached bounds make each pruning test constant-time.
-/
def reportAux : RangeTree → Int → Int → List Int → List Int
  | .empty, _, _, acc => acc
  | .leaf x, lo, hi, acc => if lo ≤ x ∧ x ≤ hi then x :: acc else acc
  | .node nlo nhi left right, lo, hi, acc =>
      if nhi < lo ∨ hi < nlo then acc
      else if lo ≤ nlo ∧ nhi ≤ hi then
        toListAux (.node nlo nhi left right) acc
      else reportAux left lo hi (reportAux right lo hi acc)

/-- The range report for `[lo, hi]`; see `reportAux`. -/
def report (t : RangeTree) (lo hi : Int) : List Int :=
  reportAux t lo hi []

/-- The accumulator report of a bounds-valid tree is its filtered leaf
list on the accumulator. -/
theorem reportAux_eq_filter_append {t : RangeTree} (hb : BoundsOk t)
    (lo hi : Int) (acc : List Int) :
    t.reportAux lo hi acc =
      t.toList.filter (fun x => lo ≤ x ∧ x ≤ hi) ++ acc := by
  induction t generalizing acc with
  | empty => rfl
  | leaf x =>
      by_cases hx : lo ≤ x ∧ x ≤ hi
      · simp [reportAux, toList_leaf, hx]
      · simp [reportAux, toList_leaf, hx]
  | node nlo nhi left right ihLeft ihRight =>
      cases hb with
      | node hLeft hRight hLeftNe hRightNe hlo hhi =>
          by_cases hDisj : nhi < lo ∨ hi < nlo
          · have hNil : (RangeTree.node nlo nhi left right).toList.filter
                (fun x => lo ≤ x ∧ x ≤ hi) = [] := by
              apply filter_eq_nil_of_all
              intro x hx hxIn
              have hbnd := bounds_of_mem (BoundsOk.node hLeft hRight hLeftNe hRightNe hlo hhi) hx
              have hbnd' : nlo ≤ x ∧ x ≤ nhi := hbnd
              cases hDisj with
              | inl h => omega
              | inr h => omega
            change reportAux (.node nlo nhi left right) lo hi acc = _
            rw [reportAux, ite_eq_left hDisj, hNil]
            rfl
          · by_cases hIn : lo ≤ nlo ∧ nhi ≤ hi
            · have hSelf : (RangeTree.node nlo nhi left right).toList.filter
                  (fun x => lo ≤ x ∧ x ≤ hi) =
                  (RangeTree.node nlo nhi left right).toList := by
                apply filter_eq_self_of_all
                intro x hx
                have hbnd := bounds_of_mem
                  (BoundsOk.node hLeft hRight hLeftNe hRightNe hlo hhi) hx
                have hbnd' : nlo ≤ x ∧ x ≤ nhi := hbnd
                omega
              change reportAux (.node nlo nhi left right) lo hi acc = _
              rw [reportAux, ite_eq_right hDisj, ite_eq_left hIn, toListAux_eq,
                hSelf]
            · show reportAux (.node nlo nhi left right) lo hi acc = _
              rw [reportAux, ite_eq_right hDisj, ite_eq_right hIn,
                ihRight hRight, ihLeft hLeft, toList_node, List.filter_append,
                List.append_assoc]

/-- The report of a bounds-valid tree is the leaf list filtered to `[lo, hi]`. -/
theorem report_eq_filter {t : RangeTree} (hb : BoundsOk t) (lo hi : Int) :
    t.report lo hi = t.toList.filter (fun x => lo ≤ x ∧ x ≤ hi) := by
  rw [report, reportAux_eq_filter_append hb]
  simp

/-- Membership in the report is membership in the tree inside `[lo, hi]`. -/
theorem mem_report_iff {t : RangeTree} (hb : BoundsOk t) {lo hi x : Int} :
    x ∈ t.report lo hi ↔ x ∈ t.toList ∧ lo ≤ x ∧ x ≤ hi := by
  rw [report_eq_filter hb]
  simp

/-- The number of stored values in `[lo, hi]`. -/
def count (t : RangeTree) (lo hi : Int) : Nat :=
  (t.report lo hi).length

/-- The count is the length of the leaf list filtered to `[lo, hi]`. -/
theorem count_eq {t : RangeTree} (hb : BoundsOk t) (lo hi : Int) :
    t.count lo hi = (t.toList.filter (fun x => lo ≤ x ∧ x ≤ hi)).length := by
  rw [count, report_eq_filter hb]

/-- Builds a balanced range tree from a list by recursively splitting in
half, caching each node's leaf interval from its (once-built) children.
The input order is preserved verbatim (see `toList_build`); sortedness is
a hypothesis on the caller, recorded by `valid_build_of_sorted`. -/
def build : List Int → RangeTree
  | [] => .empty
  | [x] => .leaf x
  | xs@(_ :: _ :: _) =>
      let left := build (xs.take (xs.length / 2))
      let right := build (xs.drop (xs.length / 2))
      .node (min left.tmin right.tmin) (max left.tmax right.tmax) left right
termination_by xs => xs.length
decreasing_by
  all_goals
    simp_all only [List.length_take, List.length_drop, List.length_cons]
    omega

/-- The leaf list of a tree built from a list is that list. -/
@[simp]
theorem toList_build : ∀ xs : List Int, (build xs).toList = xs := by
  intro xs
  induction hn : xs.length using Nat.strongRecOn generalizing xs with
  | _ n ih =>
      cases xs with
      | nil => rw [build]; rfl
      | cons x xs =>
          cases xs with
          | nil => rw [build]; rfl
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
              have hBuild : build (x :: y :: ys) =
                  .node (min (build ((x :: y :: ys).take
                      ((x :: y :: ys).length / 2))).tmin
                    (build ((x :: y :: ys).drop
                      ((x :: y :: ys).length / 2))).tmin)
                    (max (build ((x :: y :: ys).take
                      ((x :: y :: ys).length / 2))).tmax
                    (build ((x :: y :: ys).drop
                      ((x :: y :: ys).length / 2))).tmax)
                    (build ((x :: y :: ys).take ((x :: y :: ys).length / 2)))
                    (build ((x :: y :: ys).drop ((x :: y :: ys).length / 2))) := by
                rw [build]
              rw [hBuild, toList_node, hLeft, hRight]
              exact List.take_append_drop _ _

/-- The size of a tree built from a list is the length of that list. -/
@[simp]
theorem size_build (xs : List Int) : (build xs).size = xs.length := by
  rw [← length_toList, toList_build]

/-- A built tree has correct cached bounds. -/
theorem boundsOk_build : ∀ xs : List Int, BoundsOk (build xs) := by
  intro xs
  induction hn : xs.length using Nat.strongRecOn generalizing xs with
  | _ n ih =>
      cases xs with
      | nil => rw [build]; exact BoundsOk.empty
      | cons x xs =>
          cases xs with
          | nil => rw [build]; exact BoundsOk.leaf x
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
              have hBuild : build (x :: y :: ys) =
                  .node (min (build ((x :: y :: ys).take
                      ((x :: y :: ys).length / 2))).tmin
                    (build ((x :: y :: ys).drop
                      ((x :: y :: ys).length / 2))).tmin)
                    (max (build ((x :: y :: ys).take
                      ((x :: y :: ys).length / 2))).tmax
                    (build ((x :: y :: ys).drop
                      ((x :: y :: ys).length / 2))).tmax)
                    (build ((x :: y :: ys).take ((x :: y :: ys).length / 2)))
                    (build ((x :: y :: ys).drop ((x :: y :: ys).length / 2))) := by
                rw [build]
              have hLeftNe :
                  (build ((x :: y :: ys).take
                    ((x :: y :: ys).length / 2))).toList ≠ [] := by
                rw [toList_build]
                intro hNil
                have hlen := congrArg List.length hNil
                simp only [List.length_take, List.length_cons,
                  List.length_nil] at hlen
                omega
              have hRightNe :
                  (build ((x :: y :: ys).drop
                    ((x :: y :: ys).length / 2))).toList ≠ [] := by
                rw [toList_build]
                intro hNil
                have hlen := congrArg List.length hNil
                simp only [List.length_drop, List.length_cons,
                  List.length_nil] at hlen
                omega
              rw [hBuild]
              exact BoundsOk.node hLeft hRight hLeftNe hRightNe rfl rfl

/-- Building from a sorted list yields a valid (classical) range tree:
correct cached bounds and sorted leaf order. Without the sortedness
hypothesis only `boundsOk_build` holds. -/
theorem valid_build_of_sorted {xs : List Int} (h : xs.Pairwise (· ≤ ·)) :
    Valid (build xs) :=
  ⟨boundsOk_build xs, by rw [toList_build]; exact h⟩

/-- The report on a tree built from a list is that list filtered to `[lo, hi]`. -/
theorem report_build (xs : List Int) (lo hi : Int) :
    (build xs).report lo hi = xs.filter (fun x => lo ≤ x ∧ x ≤ hi) := by
  rw [report_eq_filter (boundsOk_build xs), toList_build]

/-- The count on a tree built from a list is the filtered length of that list. -/
theorem count_build (xs : List Int) (lo hi : Int) :
    (build xs).count lo hi =
      (xs.filter (fun x => lo ≤ x ∧ x ≤ hi)).length := by
  rw [count_eq (boundsOk_build xs), toList_build]

/-- Membership in the report on a built tree, stated on the input list. -/
theorem mem_report_build_iff {xs : List Int} {lo hi x : Int} :
    x ∈ (build xs).report lo hi ↔ x ∈ xs ∧ lo ≤ x ∧ x ≤ hi := by
  rw [mem_report_iff (boundsOk_build xs), toList_build]

end RangeTree

end Cslib.Algorithms.Lean
