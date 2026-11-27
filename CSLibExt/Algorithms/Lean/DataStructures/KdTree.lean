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

/-- **Kd-trees.** A kd-tree over points of $\mathbb{Z}^d$ is either empty, a leaf holding one
point of $\mathbb{Z}^d$, or a split node holding a split axis $a \in \{0, \dots, d-1\}$, a split
value $s \in \mathbb{Z}$ and two kd-trees, its left and right subtrees. -/
inductive KdTree (d : Nat) where
  | empty : KdTree d
  | leaf : (Fin d → Int) → KdTree d
  | node : Fin d → Int → KdTree d → KdTree d → KdTree d

namespace KdTree

variable {d : Nat}

/-- **Kd-tree point traversal with an accumulator.** For a kd-tree $t$ over points of
$\mathbb{Z}^d$ and a list $\mathit{acc}$ of such points, the accumulator traversal of $t$ onto
$\mathit{acc}$ is $\mathit{acc}$ when $t$ is empty, the point $p$ followed by $\mathit{acc}$ when
$t$ is a leaf holding $p$, and, when $t$ is a split node with left subtree $L$ and right subtree
$R$, the traversal of $L$ onto the traversal of $R$ onto $\mathit{acc}$.

Threading the output suffix avoids repeatedly appending (and copying) left-subtree results. -/
def toListAux : KdTree d → List (Fin d → Int) → List (Fin d → Int)
  | .empty, acc => acc
  | .leaf p, acc => p :: acc
  | .node _ _ left right, acc => left.toListAux (right.toListAux acc)

/-- **Point list of a kd-tree.** The point list of a kd-tree is the list of the points stored at
its leaves, from left to right. -/
def toList (t : KdTree d) : List (Fin d → Int) :=
  t.toListAux []

/-- **Accumulator traversal of a kd-tree.** For every kd-tree $t$ over $\mathbb{Z}^d$ and
every list $acc$ of points, the accumulator traversal of $t$ onto $acc$ equals the list of
points of $t$ in left-to-right order followed by $acc$. -/
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

/-- **Point list of a kd-tree split node.** For a split node with axis $a$, split value $s$, left
subtree $L$ and right subtree $R$, the point list of the node is the point list of $L$ followed
by the point list of $R$. -/
@[simp]
theorem toList_node (a : Fin d) (s : Int) (left right : KdTree d) :
    (KdTree.node a s left right).toList = left.toList ++ right.toList := by
  show left.toListAux (right.toListAux []) = left.toList ++ right.toList
  rw [toListAux_eq, toListAux_eq, List.append_nil]

/-- **Size of a kd-tree.** The size of a kd-tree is defined by recursion: the empty tree has
size $0$, a leaf has size $1$, and a split node has the sum of the sizes of its two
children. Since points are stored only at leaves, this is the number of points stored in the
tree, counted with multiplicity. -/
def size : KdTree d → Nat
  | .empty => 0
  | .leaf _ => 1
  | .node _ _ left right => left.size + right.size

/-- **Length of the point list of a kd-tree.** For every kd-tree $t$, the list of the points
stored in $t$, read from left to right, has length equal to the size of $t$, the number of
points stored in $t$. -/
@[simp]
theorem length_toList (t : KdTree d) : t.toList.length = t.size := by
  induction t with
  | empty => rfl
  | leaf _ => rfl
  | node _ _ _ _ ihLeft ihRight => simp [size, ihLeft, ihRight]

/-- **Next split axis of a kd-tree.** For a dimension $d \ge 1$ and an axis
$a \in \{0, \dots, d - 1\}$, the next split axis is $(a + 1) \bmod d$, so the axes are
visited cyclically. -/
def nextAxis [NeZero d] (a : Fin d) : Fin d :=
  Fin.ofNat d (a.val + 1)

/-- **Membership in an axis-aligned box.** For $lo, hi, p \in \mathbb{Z}^d$, the point $p$ lies
in the closed axis-aligned box $[lo, hi]$ when $lo_i \le p_i \le hi_i$ for every coordinate
$i \in \{0, \dots, d-1\}$. -/
abbrev inBox (lo hi p : Fin d → Int) : Prop :=
  ∀ i, lo i ≤ p i ∧ p i ≤ hi i

private theorem filter_inBox_eq_nil {lo hi : Fin d → Int}
    {xs : List (Fin d → Int)} (h : ∀ p ∈ xs, ¬ inBox lo hi p) :
    xs.filter (fun p => inBox lo hi p) = [] := by
  rw [List.filter_eq_nil_iff]
  intro p hp
  simpa using h p hp

/--
**Accumulator range report of a kd-tree.** Points are vectors in $\mathbb{Z}^d$ with
coordinates $p_0, \dots, p_{d-1}$; the box $[lo, hi]$ consists of the points $p$ with
$lo_i \le p_i \le hi_i$ for every $i$. For a kd-tree $t$ and a list $acc$ of points, the
accumulator report of $t$ for $[lo, hi]$ onto $acc$ is defined by recursion on $t$. For the
empty tree it is $acc$. For a leaf $p$ it is $p$ followed by $acc$ if $p$ lies in the box,
and $acc$ otherwise. For a split node with axis $a$, split value $s$, left child $L$ and
right child $R$, let $acc'$ be $acc$ if $hi_a < s$ and the report of $R$ onto $acc$
otherwise; the result is $acc'$ if $s < lo_a$ and the report of $L$ onto $acc'$ otherwise.

The accumulator avoids repeatedly appending the results of left subtrees, so building the
output list costs work linear in the number of reported points; the traversal still visits
every node that pruning does not cut, which can be the whole tree even for an empty report.
No complexity bound is formalized.
-/
def reportAux : KdTree d → (Fin d → Int) → (Fin d → Int) →
    List (Fin d → Int) → List (Fin d → Int)
  | .empty, _, _, acc => acc
  | .leaf p, lo, hi, acc => if inBox lo hi p then p :: acc else acc
  | .node a s left right, lo, hi, acc =>
      let rightAcc := if hi a < s then acc else reportAux right lo hi acc
      if s < lo a then rightAcc else reportAux left lo hi rightAcc

/-- **Orthogonal range report of a kd-tree.** For a kd-tree $t$ over $\mathbb{Z}^d$ and
$lo, hi \in \mathbb{Z}^d$, the range report of $t$ for the box $[lo, hi]$ is the accumulator
range report of $t$ for $[lo, hi]$ onto the empty list. -/
def report (t : KdTree d) (lo hi : Fin d → Int) : List (Fin d → Int) :=
  reportAux t lo hi []

/-- **Kd invariant.** A kd-tree satisfies the kd invariant when at every split node, with axis $a$
and split value $s$, every point of the left subtree has $a$-coordinate at most $s$ and every
point of the right subtree has $a$-coordinate at least $s$. -/
inductive Valid : KdTree d → Prop where
  | empty : Valid .empty
  | leaf (p : Fin d → Int) : Valid (.leaf p)
  | node {a : Fin d} {s : Int} {left right : KdTree d} (hLeft : Valid left)
      (hRight : Valid right) (hL : ∀ p ∈ left.toList, p a ≤ s)
      (hR : ∀ p ∈ right.toList, s ≤ p a) : Valid (.node a s left right)

/-- **Accumulator range report of a valid kd-tree.** Let $t$ be a valid kd-tree over
$\mathbb{Z}^d$, let $lo, hi \in \mathbb{Z}^d$, and let $acc$ be a list of points. The
accumulator range report of $t$ for the box $[lo, hi]$ onto $acc$ equals the list of points
of $t$, in left-to-right order, that lie in the box (the points $p$ with
$lo_i \le p_i \le hi_i$ for every coordinate $i$), followed by $acc$. -/
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

/-- **Correctness of the kd-tree range report.** For every valid kd-tree $t$ over
$\mathbb{Z}^d$ and all $lo, hi \in \mathbb{Z}^d$, the range report of $t$ for the box
$[lo, hi]$ equals the list of points of $t$, in left-to-right order, that lie in the box,
that is, the points $p$ with $lo_i \le p_i \le hi_i$ for every coordinate $i$. -/
theorem report_eq_filter {t : KdTree d} (h : t.Valid)
    (lo hi : Fin d → Int) :
    t.report lo hi = t.toList.filter (fun p => inBox lo hi p) := by
  rw [report, reportAux_eq_filter_append h]
  simp

/-- **Range report of a valid kd-tree.** Let $t$ be a kd-tree over $\mathbb{Z}^d$ that
satisfies the kd invariant, and let $lo, hi, p \in \mathbb{Z}^d$. Then $p$ occurs in the range
report of $t$ for the box $[lo, hi]$ if and only if $p$ is one of the points stored in $t$ and
$lo_i \le p_i \le hi_i$ for every coordinate $i$. -/
theorem mem_report_iff {t : KdTree d} (h : t.Valid)
    {lo hi p : Fin d → Int} :
    p ∈ t.report lo hi ↔ p ∈ t.toList ∧ inBox lo hi p := by
  rw [report_eq_filter h]
  simp

/-- **First-point coordinate.** For an axis $a \in \{0, \dots, d-1\}$ and a list of points in
$\mathbb{Z}^d$, this is the $a$-coordinate of the first point of the list, or $0$ if the list
is empty. -/
def headCoord (a : Fin d) (xs : List (Fin d → Int)) : Int :=
  (xs.head?.map (fun p => p a)).getD 0

/-- **Kd-tree construction by median splits.** Let $d \ge 1$, let $a \in \{0, \dots, d-1\}$ be
an axis and let $P$ be a list of points in $\mathbb{Z}^d$. The kd-tree built from $P$ starting at
axis $a$ is the empty tree if $P$ is empty and the leaf holding $p$ if $P = [p]$. If $P$ has
$n \ge 2$ points, sort $P$ by $a$-coordinate with merge sort, let $L$ be the first
$\lfloor n/2 \rfloor$ points of the sorted list and $R$ the remaining ones. The result is the
split node with axis $a$ whose split value is the $a$-coordinate of the first point of $R$, whose
left subtree is built from $L$ and whose right subtree is built from $R$, both starting at the
next axis $(a + 1) \bmod d$. -/
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

/-- **Median-split kd-trees satisfy the kd invariant.** For $d \ge 1$, every axis $a$ and every
list of points of $\mathbb{Z}^d$, the kd-tree built from the list by median splits starting at
axis $a$ satisfies the kd invariant. -/
theorem valid_build [NeZero d] (a : Fin d) (pts : List (Fin d → Int)) :
    (build a pts).Valid :=
  (build_spec a pts).1

/-- **Building a kd-tree preserves its points.** For $d \ge 1$, every axis $a$ and every list of
points of $\mathbb{Z}^d$, the point list of the kd-tree built from the list by median splits
starting at axis $a$ is a permutation of the list. -/
theorem toList_build_perm [NeZero d] (a : Fin d) (pts : List (Fin d → Int)) :
    (build a pts).toList.Perm pts :=
  (build_spec a pts).2

/-- **A built kd-tree holds the same points as its input.** Let $d \ge 1$, let
$a \in \{0, \dots, d-1\}$ and let $P$ be a list of points in $\mathbb{Z}^d$. A point
$p \in \mathbb{Z}^d$ is stored in the kd-tree built from $P$ by median splits starting at axis
$a$ if and only if $p$ occurs in $P$. -/
theorem mem_toList_build_iff [NeZero d] (a : Fin d) (pts : List (Fin d → Int))
    (p : Fin d → Int) :
    p ∈ (build a pts).toList ↔ p ∈ pts :=
  (toList_build_perm a pts).mem_iff

/-- **Size of a built kd-tree.** Let $d \ge 1$. For every starting axis $a$ and every list
$P$ of points of $\mathbb{Z}^d$, the size of the kd-tree built from $P$ starting at axis $a$
equals the length of $P$ (repeated points counted with multiplicity). -/
@[simp]
theorem size_build [NeZero d] (a : Fin d) (pts : List (Fin d → Int)) :
    (build a pts).size = pts.length := by
  rw [← length_toList]
  exact (toList_build_perm a pts).length_eq

/-- **Kd-tree construction from the first axis.** For $d \ge 1$ and a list of points in
$\mathbb{Z}^d$, this is the kd-tree built from the list by alternating-axis median splits,
starting with split axis $0$. -/
def buildRoot [NeZero d] (pts : List (Fin d → Int)) : KdTree d :=
  build (Fin.ofNat d 0) pts

/-- **Kd-trees built from axis 0 satisfy the kd invariant.** For $d \ge 1$ and every list of
points of $\mathbb{Z}^d$, the kd-tree built from the list by median splits starting at axis $0$
satisfies the kd invariant. -/
theorem valid_buildRoot [NeZero d] (pts : List (Fin d → Int)) :
    (buildRoot pts).Valid :=
  valid_build _ pts

/-- **Building a kd-tree from axis 0 preserves its points.** For $d \ge 1$ and every list of
points of $\mathbb{Z}^d$, the point list of the kd-tree built from the list by median splits
starting at axis $0$ is a permutation of the list. -/
theorem toList_buildRoot_perm [NeZero d] (pts : List (Fin d → Int)) :
    (buildRoot pts).toList.Perm pts :=
  toList_build_perm _ pts

/-- **Range report of a built kd-tree as a filter.** Let $d \ge 1$. For every starting axis
$a$, every list $P$ of points of $\mathbb{Z}^d$ and all $lo, hi \in \mathbb{Z}^d$, let $T$ be
the kd-tree built from $P$ starting at axis $a$. The range report of $T$ for the box
$[lo, hi]$ equals the list of points of $T$, in left-to-right order, that lie in the box,
that is, the points $p$ with $lo_i \le p_i \le hi_i$ for every coordinate $i$. -/
theorem report_build [NeZero d] (a : Fin d) (pts : List (Fin d → Int))
    (lo hi : Fin d → Int) :
    (build a pts).report lo hi =
      (build a pts).toList.filter (fun p => inBox lo hi p) :=
  report_eq_filter (valid_build a pts) lo hi

/-- **Range report of a built kd-tree up to order.** Let $d \ge 1$. For every starting axis $a$,
every list $P$ of points of $\mathbb{Z}^d$ and all $lo, hi \in \mathbb{Z}^d$, the range report
for the box $[lo, hi]$ of the kd-tree built from $P$ starting at axis $a$ is a permutation of
the list of entries of $P$ that lie in the box, that is, the points $p$ with
$lo_i \le p_i \le hi_i$ for every coordinate $i$. -/
theorem report_build_perm [NeZero d] (a : Fin d) (pts : List (Fin d → Int))
    (lo hi : Fin d → Int) :
    ((build a pts).report lo hi).Perm
      (pts.filter (fun p => inBox lo hi p)) := by
  rw [report_build]
  exact (toList_build_perm a pts).filter _

/-- **Membership in the range report of a built kd-tree.** Let $d \ge 1$, let
$a \in \{0, \dots, d-1\}$, let $P$ be a list of points in $\mathbb{Z}^d$ and let
$lo, hi, p \in \mathbb{Z}^d$. Then $p$ occurs in the range report, for the box $[lo, hi]$, of the
kd-tree built from $P$ by median splits starting at axis $a$ if and only if $p$ occurs in $P$ and
$lo_i \le p_i \le hi_i$ for every coordinate $i$. -/
theorem mem_report_build_iff [NeZero d] (a : Fin d) (pts : List (Fin d → Int))
    {lo hi p : Fin d → Int} :
    p ∈ (build a pts).report lo hi ↔ p ∈ pts ∧ inBox lo hi p := by
  rw [mem_report_iff (valid_build a pts), mem_toList_build_iff]

/-- **Range report of a kd-tree built from the first axis.** Let $d \ge 1$, let $P$ be a list
of points in $\mathbb{Z}^d$ and let $lo, hi, p \in \mathbb{Z}^d$. Then $p$ occurs in the range
report, for the box $[lo, hi]$, of the kd-tree built from $P$ by median splits starting at
axis $0$ if and only if $p$ occurs in $P$ and $lo_i \le p_i \le hi_i$ for every coordinate
$i$. -/
theorem mem_report_buildRoot_iff [NeZero d] (pts : List (Fin d → Int))
    {lo hi p : Fin d → Int} :
    p ∈ (buildRoot pts).report lo hi ↔ p ∈ pts ∧ inBox lo hi p :=
  mem_report_build_iff _ pts

end KdTree

end Cslib.Algorithms.Lean
