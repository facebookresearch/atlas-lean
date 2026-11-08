/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Sort

/-!
# Kd-trees

This file defines a kd-tree over points `Fin d → Int`, following La Rocca,
*Advanced Algorithms and Data Structures*, chapter 9, at the level of the
verified orthogonal range report. Internal nodes store a split axis and a split
value; the points are the leaves. `Valid` records the kd invariant at a node
with axis `a` and split value `s`: every point in the left subtree has
`a`-coordinate at most `s` and every point in the right subtree has
`a`-coordinate at least `s` (points on the split hyperplane may occur on both
sides). Building sorts the points by the current axis, splits the sorted list
in half (a median split), takes the split value from the first point of the
right half, and recurses with the next axis cyclically. The range report for
an axis-aligned box `[lo, hi]` prunes a child when the split value already
separates it from the box, and the main theorem states that the report of a
valid tree is exactly its leaf list filtered by the box predicate.

## Main definitions

* `KdTree.build` builds a tree by alternating-axis median splits.
* `KdTree.Valid` is the split invariant.
* `KdTree.report` lists the points of the tree inside an axis-aligned box.

## Deferred

Nearest-neighbor search, dynamic insertion and rebalancing, and all complexity
bounds are not proved here; no cost model is carried.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

/-- A kd-tree over points `Fin d → Int`: empty, a point leaf, or a split node. -/
inductive KdTree (d : Nat) where
  | empty : KdTree d
  | leaf : (Fin d → Int) → KdTree d
  | node : Fin d → Int → KdTree d → KdTree d → KdTree d

namespace KdTree

variable {d : Nat}

/-- Accumulator traversal threading the output suffix, so collecting the
points of an `n`-point tree takes linear time instead of repeatedly
appending (and copying) left-subtree results. -/
def toListAux : KdTree d → List (Fin d → Int) → List (Fin d → Int)
  | .empty, acc => acc
  | .leaf p, acc => p :: acc
  | .node _ _ left right, acc => left.toListAux (right.toListAux acc)

/-- The points stored in a tree, from left to right. -/
def toList (t : KdTree d) : List (Fin d → Int) :=
  t.toListAux []

/-- The accumulator traversal prepends exactly the tree's points. -/
@[simp]
theorem toListAux_eq (t : KdTree d) (acc : List (Fin d → Int)) :
    t.toListAux acc = t.toList ++ acc := by
  induction t generalizing acc with
  | empty => rfl
  | leaf _ => rfl
  | node a s left right ihLeft ihRight =>
      show left.toListAux (right.toListAux acc) =
        (KdTree.node a s left right).toList ++ acc
      rw [ihLeft, ihRight]
      have hnode : (KdTree.node a s left right).toList =
          left.toList ++ right.toList := by
        show left.toListAux (right.toListAux []) = left.toList ++ right.toList
        rw [ihLeft, ihRight, List.append_nil]
      rw [hnode, List.append_assoc]

@[simp]
theorem toList_empty : (KdTree.empty : KdTree d).toList = [] :=
  rfl

@[simp]
theorem toList_leaf (p : Fin d → Int) : (KdTree.leaf p).toList = [p] :=
  rfl

/-- Characteristic equation for `toList` at a split node; with the
accumulator definition this is a theorem, not a definitional unfolding. -/
@[simp]
theorem toList_node (a : Fin d) (s : Int) (left right : KdTree d) :
    (KdTree.node a s left right).toList = left.toList ++ right.toList := by
  show left.toListAux (right.toListAux []) = left.toList ++ right.toList
  rw [toListAux_eq, toListAux_eq, List.append_nil]

/-- The number of points stored in a tree. -/
def size : KdTree d → Nat
  | .empty => 0
  | .leaf _ => 1
  | .node _ _ left right => left.size + right.size

/-- The length of the point list is the size of the tree. -/
@[simp]
theorem length_toList (t : KdTree d) : t.toList.length = t.size := by
  induction t with
  | empty => rfl
  | leaf _ => rfl
  | node _ _ _ _ ihLeft ihRight => simp [size, ihLeft, ihRight]

/-- The next split axis, cyclically. -/
def nextAxis [NeZero d] (a : Fin d) : Fin d :=
  Fin.ofNat d (a.val + 1)

/-- A point lies in the axis-aligned box `[lo, hi]`. -/
abbrev inBox (lo hi p : Fin d → Int) : Prop :=
  ∀ i, lo i ≤ p i ∧ p i ≤ hi i

private theorem filter_inBox_eq_nil {lo hi : Fin d → Int}
    {xs : List (Fin d → Int)} (h : ∀ p ∈ xs, ¬ inBox lo hi p) :
    xs.filter (fun p => inBox lo hi p) = [] := by
  rw [List.filter_eq_nil_iff]
  intro p hp
  simpa using h p hp

/--
Accumulator form of the orthogonal range report: `reportAux t lo hi acc`
prepends the reported points (in left-to-right order) onto `acc`. The
accumulator avoids repeatedly appending left results, so constructing the
output list costs only work linear in the number of reported points; the
traversal itself still visits every node that pruning does not cut, which
can be the whole tree even for an empty report, and no complexity bound is
proved here. At a split node with axis `a` and value `s`, the left child is
pruned when `s < lo a` and the right child is pruned when `hi a < s`.
-/
def reportAux : KdTree d → (Fin d → Int) → (Fin d → Int) →
    List (Fin d → Int) → List (Fin d → Int)
  | .empty, _, _, acc => acc
  | .leaf p, lo, hi, acc => if inBox lo hi p then p :: acc else acc
  | .node a s left right, lo, hi, acc =>
      let rightAcc := if hi a < s then acc else reportAux right lo hi acc
      if s < lo a then rightAcc else reportAux left lo hi rightAcc

/-- The orthogonal range report for the box `[lo, hi]`; see `reportAux`. -/
def report (t : KdTree d) (lo hi : Fin d → Int) : List (Fin d → Int) :=
  reportAux t lo hi []

/--
The kd invariant: at a node with axis `a` and split value `s`, every point on
the left has `a`-coordinate at most `s` and every point on the right has
`a`-coordinate at least `s`.
-/
inductive Valid : KdTree d → Prop where
  | empty : Valid .empty
  | leaf (p : Fin d → Int) : Valid (.leaf p)
  | node {a : Fin d} {s : Int} {left right : KdTree d} (hLeft : Valid left)
      (hRight : Valid right) (hL : ∀ p ∈ left.toList, p a ≤ s)
      (hR : ∀ p ∈ right.toList, s ≤ p a) : Valid (.node a s left right)

/-- The accumulator report of a valid tree is its filtered point list on `acc`. -/
theorem reportAux_eq_filter_append {t : KdTree d} (h : t.Valid)
    (lo hi : Fin d → Int) (acc : List (Fin d → Int)) :
    t.reportAux lo hi acc =
      t.toList.filter (fun p => inBox lo hi p) ++ acc := by
  induction t generalizing acc with
  | empty => rfl
  | leaf p =>
      by_cases hp : inBox lo hi p
      · have hd : decide (inBox lo hi p) = true := by
          simp only [decide_eq_true_eq]
          exact hp
        simp [reportAux, hp, hd]
      · simp [reportAux, hp]
  | node a s left right ihLeft ihRight =>
      cases h with
      | node hLeft hRight hL hR =>
          have hRightEq : (if hi a < s then acc else reportAux right lo hi acc) =
              right.toList.filter (fun p => inBox lo hi p) ++ acc := by
            by_cases h2 : hi a < s
            · rw [ite_eq_left h2]
              rw [filter_inBox_eq_nil (xs := right.toList) ?_]
              · rfl
              · intro p hp hpBox
                have hpa := hR p hp
                have hbox := hpBox a
                omega
            · rw [ite_eq_right h2]
              exact ihRight hRight acc
          have hLeftEq : ∀ acc', (if s < lo a then acc'
              else reportAux left lo hi acc') =
              left.toList.filter (fun p => inBox lo hi p) ++ acc' := by
            intro acc'
            by_cases h1 : s < lo a
            · rw [ite_eq_left h1]
              rw [filter_inBox_eq_nil (xs := left.toList) ?_]
              · rfl
              · intro p hp hpBox
                have hpa := hL p hp
                have hbox := hpBox a
                omega
            · rw [ite_eq_right h1]
              exact ihLeft hLeft acc'
          show reportAux (.node a s left right) lo hi acc = _
          rw [reportAux]
          simp only [hRightEq]
          rw [hLeftEq]
          simp [List.filter_append, List.append_assoc]

/-- The report of a valid tree is its point list filtered by the box. -/
theorem report_eq_filter {t : KdTree d} (h : t.Valid)
    (lo hi : Fin d → Int) :
    t.report lo hi = t.toList.filter (fun p => inBox lo hi p) := by
  rw [report, reportAux_eq_filter_append h]
  simp

/-- Membership in the report of a valid tree, stated on its point list. -/
theorem mem_report_iff {t : KdTree d} (h : t.Valid)
    {lo hi p : Fin d → Int} :
    p ∈ t.report lo hi ↔ p ∈ t.toList ∧ inBox lo hi p := by
  rw [report_eq_filter h]
  simp

/-- The `a`-coordinate of the first point of a list, or `0` if it is empty. -/
def headCoord (a : Fin d) (xs : List (Fin d → Int)) : Int :=
  (xs.head?.map (fun p => p a)).getD 0

/--
Builds a kd-tree by alternating-axis median splits: sort by the current axis,
split the sorted list in half, take the split value from the first point of
the right half, and recurse on the next axis.
-/
def build [NeZero d] : Fin d → List (Fin d → Int) → KdTree d
  | _, [] => .empty
  | _, [p] => .leaf p
  | a, pts@(_ :: _ :: _) =>
      let sorted := pts.mergeSort (fun p q => p a ≤ q a)
      let k := sorted.length / 2
      .node a (headCoord a (sorted.drop k))
        (build (nextAxis a) (sorted.take k))
        (build (nextAxis a) (sorted.drop k))
termination_by _ pts => pts.length
decreasing_by
  all_goals
    simp_all only [List.length_take, List.length_drop, List.length_mergeSort,
      List.length_cons]
    omega

private theorem build_spec [NeZero d] :
    ∀ (a : Fin d) (pts : List (Fin d → Int)),
      (build a pts).Valid ∧ (build a pts).toList.Perm pts := by
  intro a pts
  induction hn : pts.length using Nat.strongRecOn generalizing a pts with
  | _ n ih =>
      cases pts with
      | nil =>
          rw [build]
          exact ⟨Valid.empty, List.Perm.refl _⟩
      | cons x pts =>
          cases pts with
          | nil =>
              rw [build]
              exact ⟨Valid.leaf x, List.Perm.refl _⟩
          | cons y ys =>
              set S := (x :: y :: ys).mergeSort (fun p q => p a ≤ q a) with hS
              set k := S.length / 2 with hk
              have hSlen : S.length = (x :: y :: ys).length := by
                rw [hS, List.length_mergeSort]
              have hSperm : S.Perm (x :: y :: ys) := by
                rw [hS]
                exact List.mergeSort_perm _ _
              have hlen2 : 2 ≤ S.length := by
                rw [hSlen]
                simp only [List.length_cons]
                omega
              have htake : (S.take k).length < n := by
                rw [← hn, ← hSlen]
                simp only [List.length_take]
                omega
              have hdrop : (S.drop k).length < n := by
                rw [← hn, ← hSlen]
                simp only [List.length_drop]
                omega
              have hLeft := ih _ htake (nextAxis a) (S.take k) rfl
              have hRight := ih _ hdrop (nextAxis a) (S.drop k) rfl
              have hSorted : S.Pairwise
                  (fun p q => decide (p a ≤ q a) = true) := by
                rw [hS]
                apply List.pairwise_mergeSort
                · intro p q r hpq hqr
                  simp only [decide_eq_true_eq] at hpq hqr ⊢
                  omega
                · intro p q
                  simp only [Bool.or_eq_true, decide_eq_true_eq]
                  omega
              have hApp : (S.take k ++ S.drop k).Pairwise
                  (fun p q => decide (p a ≤ q a) = true) := by
                rwa [List.take_append_drop]
              obtain ⟨-, hPairDrop, hCross⟩ := List.pairwise_append.mp hApp
              have hDropNe : S.drop k ≠ [] := by
                intro hne
                have hlen := congrArg List.length hne
                simp only [List.length_drop, List.length_nil] at hlen
                omega
              obtain ⟨q, qs, hqs⟩ :
                  ∃ q qs, S.drop k = q :: qs :=
                List.exists_cons_of_ne_nil hDropNe
              have hHeadMem : q ∈ S.drop k := by
                rw [hqs]
                simp
              have hSplit : headCoord a (S.drop k) = q a := by
                rw [hqs]
                rfl
              have hL : ∀ p ∈ (build (nextAxis a) (S.take k)).toList,
                  p a ≤ headCoord a (S.drop k) := by
                intro p hp
                rw [hSplit]
                have hpTake : p ∈ S.take k := hLeft.2.mem_iff.mp hp
                have hle := hCross p hpTake _ hHeadMem
                simpa using hle
              have hR : ∀ p ∈ (build (nextAxis a) (S.drop k)).toList,
                  headCoord a (S.drop k) ≤ p a := by
                intro p hp
                rw [hSplit]
                have hpDrop : p ∈ S.drop k := hRight.2.mem_iff.mp hp
                rw [hqs] at hpDrop hPairDrop
                cases hpDrop with
                | head _ => omega
                | tail _ hpTail =>
                    have hle := (List.pairwise_cons.mp hPairDrop).1 p hpTail
                    simpa using hle
              have hBuild : build a (x :: y :: ys) =
                  .node a (headCoord a (S.drop k))
                    (build (nextAxis a) (S.take k))
                    (build (nextAxis a) (S.drop k)) := by
                rw [build]
              rw [hBuild]
              refine ⟨Valid.node hLeft.1 hRight.1 hL hR, ?_⟩
              rw [toList_node]
              apply List.Perm.trans (hLeft.2.append hRight.2)
              rw [List.take_append_drop]
              exact hSperm

/-- A tree built by median splits satisfies the kd invariant. -/
theorem valid_build [NeZero d] (a : Fin d) (pts : List (Fin d → Int)) :
    (build a pts).Valid :=
  (build_spec a pts).1

/-- The point list of a built tree is a permutation of the input. -/
theorem toList_build_perm [NeZero d] (a : Fin d) (pts : List (Fin d → Int)) :
    (build a pts).toList.Perm pts :=
  (build_spec a pts).2

/-- Membership in the point list of a built tree is membership in the input. -/
theorem mem_toList_build_iff [NeZero d] (a : Fin d) (pts : List (Fin d → Int))
    (p : Fin d → Int) :
    p ∈ (build a pts).toList ↔ p ∈ pts :=
  (toList_build_perm a pts).mem_iff

/-- The size of a built tree is the number of input points. -/
@[simp]
theorem size_build [NeZero d] (a : Fin d) (pts : List (Fin d → Int)) :
    (build a pts).size = pts.length := by
  rw [← length_toList]
  exact (toList_build_perm a pts).length_eq

/-- Builds a kd-tree starting from axis `0`. -/
def buildRoot [NeZero d] (pts : List (Fin d → Int)) : KdTree d :=
  build (Fin.ofNat d 0) pts

/-- A tree built from axis `0` satisfies the kd invariant. -/
theorem valid_buildRoot [NeZero d] (pts : List (Fin d → Int)) :
    (buildRoot pts).Valid :=
  valid_build _ pts

/-- The point list of a tree built from axis `0` permutes the input. -/
theorem toList_buildRoot_perm [NeZero d] (pts : List (Fin d → Int)) :
    (buildRoot pts).toList.Perm pts :=
  toList_build_perm _ pts

/-- The report of a built tree is its point list filtered by the box. -/
theorem report_build [NeZero d] (a : Fin d) (pts : List (Fin d → Int))
    (lo hi : Fin d → Int) :
    (build a pts).report lo hi =
      (build a pts).toList.filter (fun p => inBox lo hi p) :=
  report_eq_filter (valid_build a pts) lo hi

/-- The report of a built tree permutes the input filtered by the box. -/
theorem report_build_perm [NeZero d] (a : Fin d) (pts : List (Fin d → Int))
    (lo hi : Fin d → Int) :
    ((build a pts).report lo hi).Perm
      (pts.filter (fun p => inBox lo hi p)) := by
  rw [report_build]
  exact (toList_build_perm a pts).filter _

/-- Membership in the report of a built tree, stated on the input. -/
theorem mem_report_build_iff [NeZero d] (a : Fin d) (pts : List (Fin d → Int))
    {lo hi p : Fin d → Int} :
    p ∈ (build a pts).report lo hi ↔ p ∈ pts ∧ inBox lo hi p := by
  rw [mem_report_iff (valid_build a pts), mem_toList_build_iff]

/-- Membership in the report of a tree built from axis `0`. -/
theorem mem_report_buildRoot_iff [NeZero d] (pts : List (Fin d → Int))
    {lo hi p : Fin d → Int} :
    p ∈ (buildRoot pts).report lo hi ↔ p ∈ pts ∧ inBox lo hi p :=
  mem_report_build_iff _ pts

end KdTree

end Cslib.Algorithms.Lean
