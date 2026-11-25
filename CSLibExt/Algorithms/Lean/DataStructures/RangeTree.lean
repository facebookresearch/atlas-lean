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

/-- **Range tree.** A one-dimensional range tree over the integers is either empty, a single leaf
holding an integer, or a binary node made of two integers $l$ and $h$ together with a left and a
right subtree. The integers $l$ and $h$ are meant to cache the interval $[l, h]$ spanned by the
leaf values of the node's subtree; the type does not enforce this, the bounds-correctness
predicate does. -/
inductive RangeTree where
  | empty : RangeTree
  | leaf : Int → RangeTree
  | node : Int → Int → RangeTree → RangeTree → RangeTree

namespace RangeTree

/-- **Leaf traversal of a range tree with an accumulator.** For a range tree $t$ and a list $a$
of integers, $\operatorname{aux}(t, a)$ is $a$ if $t$ is empty, the list $x$ followed by $a$ if
$t$ is a single leaf with value $x$, and $\operatorname{aux}(L, \operatorname{aux}(R, a))$ if $t$
is a node with left subtree $L$ and right subtree $R$.

Equivalently, $\operatorname{aux}(t, a)$ is the leaf list of $t$ followed by $a$, so the leaf list
is computed in linear time rather than by repeatedly appending left leaf lists. -/
def toListAux : RangeTree → List Int → List Int
  | .empty, acc => acc
  | .leaf x, acc => x :: acc
  | .node _ _ left right, acc => toListAux left (toListAux right acc)

/-- **Leaf list of a range tree.** The leaf list of a range tree $t$ is the list of the integers
stored at its leaves, read from left to right and with repetitions. -/
def toList (t : RangeTree) : List Int :=
  toListAux t []

/-- **Range-tree leaf traversal appends to its accumulator.** For every range tree $t$ and every
list $a$ of integers, the accumulator leaf traversal of $t$ started from $a$ equals the leaf list
of $t$ followed by $a$. -/
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

/-- **Leaf list of a range-tree node.** For all integers $lo$, $hi$ and range trees $L$, $R$, the
leaf list of the node with stored bounds $lo$, $hi$, left subtree $L$ and right subtree $R$ is
the leaf list of $L$ followed by the leaf list of $R$. -/
theorem toList_node (lo hi : Int) (left right : RangeTree) :
    (RangeTree.node lo hi left right).toList = left.toList ++ right.toList := by
  rw [toList, toListAux, toListAux_eq, toListAux_eq]
  simp

@[simp] theorem toList_empty : (RangeTree.empty).toList = [] := rfl
@[simp] theorem toList_leaf (x : Int) : (RangeTree.leaf x).toList = [x] := rfl

/-- **Number of leaves of a range tree.** The size of a range tree is its number of leaves: $0$ for
the empty tree, $1$ for a leaf, and the sum of the sizes of the two children for a node. -/
def size : RangeTree → Nat
  | .empty => 0
  | .leaf _ => 1
  | .node _ _ left right => left.size + right.size

/-- **Length of the leaf list of a range tree.** For every range tree $t$, the list of leaf values
of $t$ read from left to right has length equal to the number of leaves of $t$. -/
@[simp]
theorem length_toList (t : RangeTree) : t.toList.length = t.size := by
  induction t with
  | empty => rfl
  | leaf _ => rfl
  | node _ _ _ _ ihLeft ihRight => simp [toList_node, size, ihLeft, ihRight]

/-- **Cached lower bound of a range tree.** For a range tree $t$, $\operatorname{tmin}(t)$ is
$0$ if $t$ is empty, $x$ if $t$ is a single leaf with value $x$, and the stored lower bound
$lo$ if $t$ is a node with stored bounds $lo$, $hi$ and two subtrees.

The value $0$ for the empty tree is a sentinel without meaning. Computing
$\operatorname{tmin}(t)$ takes constant time: it reads the bound cached at the root and does not
traverse the tree. -/
def tmin : RangeTree → Int
  | .empty => 0
  | .leaf x => x
  | .node lo _ _ _ => lo

/-- **Cached upper bound of a range tree.** For a range tree $t$, $\operatorname{tmax}(t)$ is
$0$ if $t$ is empty, $x$ if $t$ is a single leaf with value $x$, and the stored upper bound
$hi$ if $t$ is a node with stored bounds $lo$, $hi$ and two subtrees.

The value $0$ for the empty tree is a sentinel without meaning. -/
def tmax : RangeTree → Int
  | .empty => 0
  | .leaf x => x
  | .node _ hi _ _ => hi

/-- **Bounds-valid range trees.** For a range tree $s$, write $s_{\min}$ and $s_{\max}$ for its
cached lower and upper bounds: the stored interval endpoints at a node, the value itself at a
leaf, and $0$ for the empty tree. Bounds-validity is defined inductively: the empty tree and every
leaf are bounds-valid, and a node with cached interval $[a, b]$, left child $\ell$ and right child
$r$ is bounds-valid when $\ell$ and $r$ are bounds-valid, each of them has at least one leaf,
$a = \min(\ell_{\min}, r_{\min})$ and $b = \max(\ell_{\max}, r_{\max})$.

The children must be nonempty because the empty tree has cached bounds $0$: with an empty child
the node cache would only enclose the leaves (a node over an empty child and the single leaf $5$
could cache $[0, 5]$), not equal their true interval. In a bounds-valid tree every leaf value lies
in the cached interval, and if the tree has a leaf, both cached bounds are leaf values. -/
inductive BoundsOk : RangeTree → Prop where
  | empty : BoundsOk .empty
  | leaf (x : Int) : BoundsOk (.leaf x)
  | node {lo hi : Int} {left right : RangeTree} (hLeft : BoundsOk left)
      (hRight : BoundsOk right) (hLeftNe : left.toList ≠ [])
      (hRightNe : right.toList ≠ []) (hlo : lo = min left.tmin right.tmin)
      (hhi : hi = max left.tmax right.tmax) :
      BoundsOk (.node lo hi left right)

/-- **Valid range tree.** A range tree $t$ is valid when it has correct cached bounds (every node
has two subtrees with nonempty leaf lists, and its stored lower and upper bounds are the minimum
of the lower bounds and the maximum of the upper bounds of its two subtrees, recursively) and
its leaf list is sorted in nondecreasing order. -/
def Valid (t : RangeTree) : Prop :=
  BoundsOk t ∧ t.toList.Pairwise (· ≤ ·)

/-- **Valid range trees have sorted leaves.** If a range tree $t$ is valid, then its list of leaf
values, read from left to right, is sorted in nondecreasing order. -/
theorem Valid.pairwise_toList {t : RangeTree} (h : Valid t) :
    t.toList.Pairwise (· ≤ ·) :=
  h.2

/-- **Leaf values of a bounds-valid tree lie between the cached bounds.** Let $t$ be a
bounds-valid range tree, and write $t_{\min}$ and $t_{\max}$ for its cached lower and upper
bounds. Then every leaf value $x$ of $t$ satisfies $t_{\min} \le x \le t_{\max}$. -/
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

/-- **The cached bounds of a nonempty bounds-valid range tree are leaf values.** Let $t$ be a
bounds-valid range tree with at least one leaf. Then the cached lower bound of $t$ and the cached
upper bound of $t$ are both leaf values of $t$.

Together with the fact that every leaf value lies between the cached bounds, this shows that the
cached interval is exactly the interval spanned by the leaves, not merely an enclosing one. -/
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
**Accumulator range report.** For integers $a$, $b$ and a list $\mathit{acc}$ of integers, the
accumulator range report of a range tree for $[a, b]$ starting from $\mathit{acc}$ is defined by
recursion on the tree. The empty tree returns $\mathit{acc}$. A leaf with value $x$ returns $x$
followed by $\mathit{acc}$ if $a \le x \le b$, and $\mathit{acc}$ otherwise. A node with cached
interval $[l, h]$ returns $\mathit{acc}$ if $h < a$ or $b < l$; otherwise, if $a \le l$ and
$h \le b$, it returns the node's leaf values from left to right followed by $\mathit{acc}$;
otherwise it returns the report of the left child starting from the report of the right child
starting from $\mathit{acc}$.

The cached bounds make each pruning test constant-time.
-/
def reportAux : RangeTree → Int → Int → List Int → List Int
  | .empty, _, _, acc => acc
  | .leaf x, lo, hi, acc => if lo ≤ x ∧ x ≤ hi then x :: acc else acc
  | .node nlo nhi left right, lo, hi, acc =>
      if nhi < lo ∨ hi < nlo then acc
      else if lo ≤ nlo ∧ nhi ≤ hi then
        toListAux (.node nlo nhi left right) acc
      else reportAux left lo hi (reportAux right lo hi acc)

/-- **Range report.** The range report of a range tree $t$ for integers $a$ and $b$ is the
accumulator range report of $t$ for $[a, b]$ starting from the empty list. -/
def report (t : RangeTree) (lo hi : Int) : List Int :=
  reportAux t lo hi []

/-- **Accumulator range report of a bounds-valid range tree.** Let $t$ be a bounds-valid range
tree, let $a$ and $b$ be integers and let $\mathit{acc}$ be a list of integers. Then the
accumulator range report of $t$ for $[a, b]$ starting from $\mathit{acc}$ is the list of the leaf
values $x$ of $t$ with $a \le x \le b$, in left-to-right order and with repetitions, followed by
$\mathit{acc}$. -/
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

/-- **Correctness of the range report.** Let $t$ be a range tree satisfying the bounds-correctness
predicate: every node has two subtrees with at least one leaf each and caches the least and the
greatest leaf value of its subtree. For all integers $a$ and $b$, the range report of $t$ for
$[a, b]$ equals the list of leaf values $x$ of $t$ with $a \le x \le b$, in left-to-right order. -/
theorem report_eq_filter {t : RangeTree} (hb : BoundsOk t) (lo hi : Int) :
    t.report lo hi = t.toList.filter (fun x => lo ≤ x ∧ x ≤ hi) := by
  rw [report, reportAux_eq_filter_append hb]
  simp

/-- **Membership in a range report.** Let $t$ be a range tree satisfying the bounds-correctness
predicate: every node has two subtrees with at least one leaf each and caches the least and the
greatest leaf value of its subtree. For all integers $a$, $b$ and $x$, the value $x$ occurs in the
range report of $t$ for $[a, b]$ if and only if $x$ is a leaf value of $t$ and $a \le x \le b$. -/
theorem mem_report_iff {t : RangeTree} (hb : BoundsOk t) {lo hi x : Int} :
    x ∈ t.report lo hi ↔ x ∈ t.toList ∧ lo ≤ x ∧ x ≤ hi := by
  rw [report_eq_filter hb]
  simp

/-- **Range count.** For a range tree $t$ and integers $a$ and $b$, the range count of $t$ over
$[a, b]$ is the length of the range report of $t$ for $[a, b]$.

On a bounds-valid tree this is the number of leaves whose value lies in $[a, b]$. -/
def count (t : RangeTree) (lo hi : Int) : Nat :=
  (t.report lo hi).length

/-- **Range count of a bounds-valid tree.** Let $t$ be a bounds-valid range tree and let $a$ and
$b$ be integers. Then the range count of $t$ over $[a, b]$ equals the number of leaves of $t$
whose value lies in $[a, b]$. -/
theorem count_eq {t : RangeTree} (hb : BoundsOk t) (lo hi : Int) :
    t.count lo hi = (t.toList.filter (fun x => lo ≤ x ∧ x ≤ hi)).length := by
  rw [count, report_eq_filter hb]

/-- **Building a range tree from a list.** For a range tree $s$, write $s_{\min}$ and $s_{\max}$
for its cached lower and upper bounds. The range tree built from a list $L$ of integers of length
$n$ is defined by recursion on $n$: the empty list gives the empty tree, a one-element list $[x]$
gives the leaf $x$, and for $n \ge 2$ it is the node whose left child $\ell$ is the tree built from
the first $\lfloor n/2 \rfloor$ entries of $L$, whose right child $r$ is the tree built from the
remaining entries, and whose cached interval is
$[\min(\ell_{\min}, r_{\min}), \max(\ell_{\max}, r_{\max})]$.

The entries of $L$ are kept in their given order; $L$ is not sorted first. -/
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

/-- **Building a range tree preserves the list.** For every list $xs$ of integers, the leaf list
of the range tree built from $xs$ is $xs$. -/
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

/-- **Size of a built range tree.** For every list $\mathit{xs}$ of integers, the range tree built
from $\mathit{xs}$ has exactly as many leaves as $\mathit{xs}$ has elements. -/
@[simp]
theorem size_build (xs : List Int) : (build xs).size = xs.length := by
  rw [← length_toList, toList_build]

/-- **Built range trees are bounds-valid.** For every list $L$ of integers, the range tree built
from $L$ by recursive halving is bounds-valid. -/
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

/-- **Building from a sorted list gives a valid range tree.** For every list $xs$ of integers that
is sorted in nondecreasing order, the range tree built from $xs$ is valid.

Without the sortedness hypothesis the built tree still has correct cached bounds, but it need not
be valid. -/
theorem valid_build_of_sorted {xs : List Int} (h : xs.Pairwise (· ≤ ·)) :
    Valid (build xs) :=
  ⟨boundsOk_build xs, by rw [toList_build]; exact h⟩

/-- **Range report on a built tree.** For every list $\mathit{xs}$ of integers and all integers $a$
and $b$, the range report for $[a, b]$ on the range tree built from $\mathit{xs}$ equals the list
of elements $x$ of $\mathit{xs}$ with $a \le x \le b$, in their original order. -/
theorem report_build (xs : List Int) (lo hi : Int) :
    (build xs).report lo hi = xs.filter (fun x => lo ≤ x ∧ x ≤ hi) := by
  rw [report_eq_filter (boundsOk_build xs), toList_build]

/-- **Range counting on a built tree.** For every list $L$ of integers and all integers $a$ and
$b$, the range count over $[a, b]$ of the range tree built from $L$ equals the number of entries
of $L$, counted with multiplicity, that lie in $[a, b]$. -/
theorem count_build (xs : List Int) (lo hi : Int) :
    (build xs).count lo hi =
      (xs.filter (fun x => lo ≤ x ∧ x ≤ hi)).length := by
  rw [count_eq (boundsOk_build xs), toList_build]

/-- **Range report membership on a built tree.** For every list $L$ of integers and all integers
$a$, $b$ and $x$, the value $x$ occurs in the range report for $[a, b]$ on the range tree built
from $L$ if and only if $x$ is an entry of $L$ and $a \le x \le b$. -/
theorem mem_report_build_iff {xs : List Int} {lo hi x : Int} :
    x ∈ (build xs).report lo hi ↔ x ∈ xs ∧ lo ≤ x ∧ x ≤ hi := by
  rw [mem_report_iff (boundsOk_build xs), toList_build]

end RangeTree

end Cslib.Algorithms.Lean
