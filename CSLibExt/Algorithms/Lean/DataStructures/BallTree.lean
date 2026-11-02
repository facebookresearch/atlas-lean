/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Ball trees

This file defines a simplified verified bounding-sphere (ball) tree for
similarity search. Points are functions `Fin d → Int`, and similarity
is measured by the squared Euclidean distance `distSq`, a natural number,
so neither real numbers nor square roots occur. Each internal node stores
a bounding sphere: a center point and a squared-radius bound covering
every point in the subtree, which is the invariant `Valid`. Leaves hold a
single point. Building splits the point list in half recursively, taking
the first point as the sphere center and the largest squared distance
from it as the bound. The similarity (range) search for a query point and
a squared radius prunes a subtree whose bounding sphere is provably
disjoint from the query ball, via the squared-distance estimate
`distSq a c ≤ 2 * (distSq a b + distSq b c)` in `distSq_le_two_mul`, and
the main theorem states that the search of a valid tree is exactly its
point list filtered by the distance predicate.

## Main definitions

* `BallTree.distSq` is squared Euclidean distance over `Fin d → Int`.
* `BallTree.build` builds a tree by recursive halving.
* `BallTree.search` lists the points of the tree within a squared radius of
  a query point.

## Deferred

Bounded fanout and multi-point leaves, centroid- or variance-based split
heuristics, dynamic insertion with node splitting, nearest-neighbor
search, and all complexity bounds are not proved here; no cost model is
carried.

This is a binary ball tree only. It is not an SS-tree: the bounded-fanout
multiway nodes, centroid-and-radius directory entries, occupancy bounds,
and variance-based node splitting that define SS-trees are all deferred
above, and SS-trees remain a separate coverage gap.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

/-- **Ball tree.** For a dimension $d$, a ball tree over the integer points $\mathbb{Z}^d$
(functions $\{0, \dots, d-1\} \to \mathbb{Z}$) is either empty, a leaf holding one point,
or a node holding a center point $c \in \mathbb{Z}^d$, a natural number $b$ (the squared-radius
bound of the node's sphere) and two child ball trees.

That the sphere around $c$ actually contains the points below the node is a separate validity
invariant, not part of this definition. -/
inductive BallTree (d : Nat) where
  | empty : BallTree d
  | leaf : (Fin d → Int) → BallTree d
  | node : (Fin d → Int) → Nat → BallTree d → BallTree d → BallTree d

namespace BallTree

variable {d : Nat}

/-- **Accumulating traversal of a ball tree.** For a ball tree $T$ and a list $A$ of points, the
accumulating traversal returns $A$ when $T$ is empty, the point $p$ followed by $A$ when $T$ is a
leaf holding $p$, and, when $T$ is a node with children $L$ and $R$, the accumulating traversal of
$L$ whose accumulator is the accumulating traversal of $R$ with accumulator $A$.

The result is the leaf points of $T$, from left to right, followed by $A$. -/
def toListAux : BallTree d → List (Fin d → Int) → List (Fin d → Int)
  | .empty, acc => acc
  | .leaf p, acc => p :: acc
  | .node _ _ left right, acc => left.toListAux (right.toListAux acc)

/-- **Point list of a ball tree.** The point list of a ball tree is the list of the points held
at its leaves, from left to right: the empty tree gives the empty list, a leaf holding $p$ gives
the list $[p]$, and a node gives the point list of its left subtree followed by the point list of
its right subtree. The centers stored at nodes are not included. -/
def toList (t : BallTree d) : List (Fin d → Int) :=
  t.toListAux []

theorem toListAux_append (t : BallTree d) (acc : List (Fin d → Int)) :
    t.toListAux acc = t.toListAux [] ++ acc := by
  induction t generalizing acc with
  | empty => rfl
  | leaf _ => rfl
  | node center bound left right ihLeft ihRight =>
      have h1 := ihRight (acc := acc)
      have h2 := ihLeft (acc := right.toListAux acc)
      have h3 := ihLeft (acc := right.toListAux [])
      show left.toListAux (right.toListAux acc) =
        left.toListAux (right.toListAux []) ++ acc
      rw [h2, h1, h3, List.append_assoc]

@[simp]
theorem toList_empty : (BallTree.empty : BallTree d).toList = [] :=
  rfl

@[simp]
theorem toList_leaf (p : Fin d → Int) : (BallTree.leaf p).toList = [p] :=
  rfl

theorem toList_node (center : Fin d → Int) (bound : Nat)
    (left right : BallTree d) :
    (BallTree.node center bound left right).toList =
      left.toList ++ right.toList := by
  show left.toListAux (right.toListAux []) =
    left.toListAux [] ++ right.toListAux []
  exact toListAux_append left (right.toListAux [])

/-- **Size of a ball tree.** The size of a ball tree is the number of points held in its leaves:
it is $0$ for the empty tree, $1$ for a leaf, and the sum of the sizes of the two children for a
node; the center of a node is not counted. -/
def size : BallTree d → Nat
  | .empty => 0
  | .leaf _ => 1
  | .node _ _ left right => left.size + right.size

theorem length_toListAux (t : BallTree d) (acc : List (Fin d → Int)) :
    (t.toListAux acc).length = t.size + acc.length := by
  induction t generalizing acc with
  | empty => simp [toListAux, size]
  | leaf _ => simp only [toListAux, size, List.length_cons]; omega
  | node _ _ _ _ ihLeft ihRight =>
      rw [toListAux, ihLeft, ihRight]
      simp only [size]
      omega

/-- **Number of points of a ball tree.** For every ball tree $t$, the list of points stored in
$t$, read from left to right, has length equal to the size of $t$. -/
@[simp]
theorem length_toList (t : BallTree d) : t.toList.length = t.size := by
  simp [toList, length_toListAux]

/-- **Squared Euclidean distance.** For points $p, q \in \mathbb{Z}^d$, the squared distance
from $p$ to $q$ is the natural number $\sum_{i=0}^{d-1} (p_i - q_i)^2$, computed in
$\mathbb{Z}$ and then converted to $\mathbb{N}$. -/
def distSq (p q : Fin d → Int) : Nat :=
  (∑ i, (p i - q i) ^ 2).toNat

/-- **Symmetry of squared distance.** For all points $p, q \in \mathbb{Z}^d$, the squared
distance from $p$ to $q$ equals the squared distance from $q$ to $p$. -/
theorem distSq_comm (p q : Fin d → Int) : distSq p q = distSq q p := by
  unfold distSq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem sum_sq_nonneg (p q : Fin d → Int) :
    0 ≤ ∑ i, (p i - q i) ^ 2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg (p i - q i)

/-- **Relaxed triangle inequality for squared distance.** For all points
$a, b, c \in \mathbb{Z}^d$, writing $\delta(x, y)$ for the squared distance from $x$ to $y$,
we have $\delta(a, c) \le 2\,(\delta(a, b) + \delta(b, c))$.

The factor $2$ comes from $(x + y)^2 \le 2(x^2 + y^2)$ applied coordinatewise. This is the
estimate that makes bounding-sphere pruning sound without square roots. -/
theorem distSq_le_two_mul (a b c : Fin d → Int) :
    distSq a c ≤ 2 * (distSq a b + distSq b c) := by
  have hInt : (∑ i, (a i - c i) ^ 2) ≤
      2 * ((∑ i, (a i - b i) ^ 2) + (∑ i, (b i - c i) ^ 2)) := by
    have hEq : (2 : Int) *
        ((∑ i, (a i - b i) ^ 2) + (∑ i, (b i - c i) ^ 2)) =
        ∑ i, (2 * ((a i - b i) ^ 2 + (b i - c i) ^ 2)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    rw [hEq]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg ((a i - b i) - (b i - c i))]
  have hab := sum_sq_nonneg a b
  have hbc := sum_sq_nonneg b c
  have hac := sum_sq_nonneg a c
  unfold distSq
  omega

/-- **Squared covering radius.** For a center $c \in \mathbb{Z}^d$ and a list $P$ of points of
$\mathbb{Z}^d$, the squared covering radius of $P$ about $c$ is the largest squared distance from
$c$ to a point of $P$, or $0$ if $P$ is empty. -/
def radiusSq (c : Fin d → Int) (pts : List (Fin d → Int)) : Nat :=
  pts.foldl (fun acc p => max acc (distSq c p)) 0

private theorem foldl_radiusSq_spec (c : Fin d → Int) :
    ∀ (xs : List (Fin d → Int)) (acc : Nat),
      acc ≤ xs.foldl (fun acc p => max acc (distSq c p)) acc ∧
        ∀ p ∈ xs,
          distSq c p ≤ xs.foldl (fun acc p => max acc (distSq c p)) acc := by
  intro xs acc
  induction xs generalizing acc with
  | nil => exact ⟨le_refl acc, fun p hp => by simp at hp⟩
  | cons x xs ih =>
      have h := ih (acc := max acc (distSq c x))
      constructor
      · change acc ≤ xs.foldl (fun acc p => max acc (distSq c p))
          (max acc (distSq c x))
        exact le_trans (le_max_left _ _) h.1
      · intro p hp
        change distSq c p ≤ xs.foldl (fun acc p => max acc (distSq c p))
          (max acc (distSq c x))
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact le_trans (le_max_right _ _) h.1
        · exact h.2 p hp

/-- **Points lie within the squared radius.** Let $c \in \mathbb{Z}^d$ and let $L$ be a list
of points of $\mathbb{Z}^d$. For every point $p$ of $L$, the squared distance from $c$ to $p$
is at most the squared radius of $L$ around $c$, the largest squared distance from $c$ to a
point of $L$. -/
theorem distSq_le_radiusSq {c p : Fin d → Int} {pts : List (Fin d → Int)}
    (hp : p ∈ pts) : distSq c p ≤ radiusSq c pts :=
  (foldl_radiusSq_spec c pts 0).2 p hp

/-- **Accumulating ball-tree search.** Let $d$ be a dimension and write $\delta(x, y)$ for the
squared distance from $x$ to $y$ in $\mathbb{Z}^d$. For a ball tree $T$ over $\mathbb{Z}^d$, a
query point $q \in \mathbb{Z}^d$, a squared radius $r \in \mathbb{N}$ and a list $A$ of points,
the accumulating search of $T$ for $q$ and $r$ with accumulator $A$ is $A$ when $T$ is empty;
when $T$ is a leaf holding $p$, it is $p$ followed by $A$ if $\delta(q, p) \le r$ and $A$
otherwise; when $T$ is a node with center $c$, squared-radius bound $b$ and children $L$ and $R$,
it is $A$ if $2(b + r) < \delta(c, q)$, and otherwise the accumulating search of $L$ for $q$ and
$r$ whose accumulator is the accumulating search of $R$ for $q$ and $r$ with accumulator $A$.

When $T$ satisfies the bounding-sphere invariant, this pruning is sound by the relaxed triangle
inequality $\delta(x, z) \le 2(\delta(x, y) + \delta(y, z))$ for all $x, y, z \in \mathbb{Z}^d$,
and the result is the points of $T$ within squared distance $r$ of $q$, from left to right,
followed by $A$. -/
def searchAux : BallTree d → (Fin d → Int) → Nat →
    List (Fin d → Int) → List (Fin d → Int)
  | .empty, _, _, acc => acc
  | .leaf p, query, radius, acc =>
      if distSq query p ≤ radius then p :: acc else acc
  | .node center bound left right, query, radius, acc =>
      if 2 * (bound + radius) < distSq center query then acc
      else left.searchAux query radius (right.searchAux query radius acc)

/-- **Ball-tree similarity search.** The search of a ball tree $T$ for a query point
$q \in \mathbb{Z}^d$ and a squared radius $r \in \mathbb{N}$ is the accumulating search of $T$ for
$q$ and $r$ started with the empty accumulator.

When $T$ satisfies the bounding-sphere invariant, the search lists exactly the points of $T$
within squared distance $r$ of $q$, from left to right. -/
def search (t : BallTree d) (query : Fin d → Int) (radius : Nat) :
    List (Fin d → Int) :=
  t.searchAux query radius []

/-- **Bounding-sphere invariant of a ball tree.** Validity of a ball tree is defined inductively:
the empty tree and every leaf are valid, and a node with center $c$ and squared-radius bound $b$
is valid when both of its subtrees are valid and every point in the point list of either subtree
lies within squared Euclidean distance $b$ of $c$. -/
inductive Valid : BallTree d → Prop where
  | empty : Valid .empty
  | leaf (p : Fin d → Int) : Valid (.leaf p)
  | node {center : Fin d → Int} {bound : Nat} {left right : BallTree d}
      (hLeft : Valid left) (hRight : Valid right)
      (hSphereLeft : ∀ p ∈ left.toList, distSq center p ≤ bound)
      (hSphereRight : ∀ p ∈ right.toList, distSq center p ≤ bound) :
      Valid (.node center bound left right)

private theorem filter_within_eq_nil {query : Fin d → Int} {radius : Nat}
    {xs : List (Fin d → Int)} (h : ∀ p ∈ xs, ¬ distSq query p ≤ radius) :
    xs.filter (fun p => distSq query p ≤ radius) = [] := by
  rw [List.filter_eq_nil_iff]
  intro p hp
  simpa using h p hp

theorem searchAux_eq_filter_append {t : BallTree d} (h : t.Valid)
    (query : Fin d → Int) (radius : Nat) (acc : List (Fin d → Int)) :
    t.searchAux query radius acc =
      t.toList.filter (fun p => distSq query p ≤ radius) ++ acc := by
  induction t generalizing acc with
  | empty => simp [searchAux, toList, toListAux]
  | leaf p =>
      by_cases hp : distSq query p ≤ radius
      · simp [searchAux, toList, toListAux, hp]
      · simp [searchAux, toList, toListAux, hp]
  | node center bound left right ihLeft ihRight =>
      cases h with
      | node hLeft hRight hSphereLeft hSphereRight =>
          by_cases hPrune : 2 * (bound + radius) < distSq center query
          · have hNil : (left.toList ++ right.toList).filter
                (fun p => distSq query p ≤ radius) = [] := by
              apply filter_within_eq_nil
              intro p hp hpLe
              rw [List.mem_append] at hp
              have hSphere : distSq center p ≤ bound := by
                rcases hp with hp | hp
                · exact hSphereLeft p hp
                · exact hSphereRight p hp
              have hTri := distSq_le_two_mul center p query
              have hComm : distSq p query = distSq query p :=
                distSq_comm p query
              omega
            simp [searchAux, hPrune, toList_node, hNil]
          · simp [searchAux, hPrune, toList_node, List.filter_append,
              ihLeft hLeft, ihRight hRight, List.append_assoc]

/-- **Ball-tree search is exact.** For every ball tree $T$ over $\mathbb{Z}^d$ satisfying the
bounding-sphere invariant, every query point $q \in \mathbb{Z}^d$ and every $r \in \mathbb{N}$, the
search of $T$ for $q$ and $r$ equals the list of points of $T$, from left to right, filtered to
the points $p$ whose squared distance from $q$ is at most $r$, in their order. Pruning against
the bounding spheres loses no point. -/
theorem search_eq_filter {t : BallTree d} (h : t.Valid)
    (query : Fin d → Int) (radius : Nat) :
    t.search query radius =
      t.toList.filter (fun p => distSq query p ≤ radius) := by
  rw [search, searchAux_eq_filter_append h]
  simp

/-- **Search of a valid ball tree.** Let $t$ be a ball tree satisfying the bounding-sphere
invariant. For all $q, p \in \mathbb{Z}^d$ and every natural number $r$, $p$ is returned by the
similarity search of $t$ with query $q$ and squared radius $r$ if and only if $p$ is one of the
points stored in $t$ and the squared distance from $q$ to $p$ is at most $r$. -/
theorem mem_search_iff {t : BallTree d} (h : t.Valid)
    {query p : Fin d → Int} {radius : Nat} :
    p ∈ t.search query radius ↔ p ∈ t.toList ∧ distSq query p ≤ radius := by
  rw [search_eq_filter h]
  simp

/--
**Building a ball tree by halving.** The ball tree built from a list of points of
$\mathbb{Z}^d$ is defined by recursion on the list. The empty list gives the empty tree and a
one-point list $[p]$ gives the leaf $p$. A list $L = [x_1, \dots, x_n]$ with $n \ge 2$ gives a
node whose center is $x_1$, whose bound is the squared radius of $L$ around $x_1$ (the largest
squared distance from $x_1$ to a point of $L$), whose left child is the tree built from the
first $\lfloor n/2 \rfloor$ points of $L$, and whose right child is the tree built from the
remaining points of $L$.
-/
def build : List (Fin d → Int) → BallTree d
  | [] => .empty
  | [p] => .leaf p
  | pts@(x :: _ :: _) =>
      .node x (radiusSq x pts)
        (build (pts.take (pts.length / 2)))
        (build (pts.drop (pts.length / 2)))
termination_by pts => pts.length
decreasing_by
  all_goals
    simp_all only [List.length_take, List.length_drop, List.length_cons]
    omega

private theorem mem_of_mem_take_or_drop {pts : List (Fin d → Int)}
    {p : Fin d → Int} (hp : p ∈ pts.take (pts.length / 2)) : p ∈ pts := by
  have hMem : p ∈ pts.take (pts.length / 2) ++ pts.drop (pts.length / 2) :=
    List.mem_append_left _ hp
  rwa [List.take_append_drop] at hMem

private theorem mem_of_mem_drop_half {pts : List (Fin d → Int)}
    {p : Fin d → Int} (hp : p ∈ pts.drop (pts.length / 2)) : p ∈ pts := by
  have hMem : p ∈ pts.take (pts.length / 2) ++ pts.drop (pts.length / 2) :=
    List.mem_append_right _ hp
  rwa [List.take_append_drop] at hMem

private theorem build_spec :
    ∀ pts : List (Fin d → Int),
      (build pts).Valid ∧ (build pts).toList.Perm pts := by
  intro pts
  induction hn : pts.length using Nat.strongRecOn generalizing pts with
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
              have hSphereLeft :
                  ∀ p ∈ (build ((x :: y :: ys).take
                      ((x :: y :: ys).length / 2))).toList,
                    distSq x p ≤ radiusSq x (x :: y :: ys) := by
                intro p hp
                apply distSq_le_radiusSq
                exact mem_of_mem_take_or_drop (hLeft.2.mem_iff.mp hp)
              have hSphereRight :
                  ∀ p ∈ (build ((x :: y :: ys).drop
                      ((x :: y :: ys).length / 2))).toList,
                    distSq x p ≤ radiusSq x (x :: y :: ys) := by
                intro p hp
                apply distSq_le_radiusSq
                exact mem_of_mem_drop_half (hRight.2.mem_iff.mp hp)
              rw [build]
              refine ⟨Valid.node hLeft.1 hRight.1 hSphereLeft hSphereRight, ?_⟩
              rw [toList_node]
              apply List.Perm.trans (hLeft.2.append hRight.2)
              rw [List.take_append_drop]

/-- **Ball trees built by halving are valid.** For every list of points in $\mathbb{Z}^d$, the
ball tree built from it by recursive halving satisfies the bounding-sphere invariant. -/
theorem valid_build (pts : List (Fin d → Int)) : (build pts).Valid :=
  (build_spec pts).1

/-- **A built ball tree stores a permutation of its input.** For every list $P$ of points of
$\mathbb{Z}^d$, the list of points of the ball tree built from $P$, from left to right, is a
permutation of $P$. -/
theorem toList_build_perm (pts : List (Fin d → Int)) :
    (build pts).toList.Perm pts :=
  (build_spec pts).2

/-- **Points of a built ball tree.** For every list $L$ of points of $\mathbb{Z}^d$ and every
point $p \in \mathbb{Z}^d$, $p$ is one of the points stored in the ball tree built from $L$ if
and only if $p$ occurs in $L$. -/
theorem mem_toList_build_iff (pts : List (Fin d → Int)) (p : Fin d → Int) :
    p ∈ (build pts).toList ↔ p ∈ pts :=
  (toList_build_perm pts).mem_iff

/-- **Size of a built ball tree.** For every list $P$ of points of $\mathbb{Z}^d$, the size of
the ball tree built from $P$ equals the length of $P$, that is, the number of entries of $P$
counted with repetition. -/
@[simp]
theorem size_build (pts : List (Fin d → Int)) :
    (build pts).size = pts.length := by
  rw [← length_toList]
  exact (toList_build_perm pts).length_eq

/-- **Ball-tree search of a built tree.** For every list $P$ of points of $\mathbb{Z}^d$, every
query point $q \in \mathbb{Z}^d$ and every $r \in \mathbb{N}$, let $T$ be the ball tree built from
$P$. The search of $T$ for $q$ and $r$ equals the list of points of $T$, from left to right,
filtered to the points $p$ whose squared distance from $q$ is at most $r$, in their order. -/
theorem search_build (pts : List (Fin d → Int)) (query : Fin d → Int)
    (radius : Nat) :
    (build pts).search query radius =
      (build pts).toList.filter (fun p => distSq query p ≤ radius) :=
  search_eq_filter (valid_build pts) query radius

/-- **Ball-tree search of a built tree, up to order.** For every list $P$ of points of
$\mathbb{Z}^d$, every query point $q \in \mathbb{Z}^d$ and every $r \in \mathbb{N}$, the search of
the ball tree built from $P$ for $q$ and $r$ is a permutation of the sublist of $P$ consisting of
the points $p$ whose squared distance from $q$ is at most $r$, kept with their multiplicities. -/
theorem search_build_perm (pts : List (Fin d → Int)) (query : Fin d → Int)
    (radius : Nat) :
    ((build pts).search query radius).Perm
      (pts.filter (fun p => distSq query p ≤ radius)) := by
  rw [search_build]
  exact (toList_build_perm pts).filter _

/-- **Search of a built ball tree.** Let $L$ be a list of points of $\mathbb{Z}^d$, let
$q, p \in \mathbb{Z}^d$ and let $r$ be a natural number. Then $p$ is returned by the similarity
search with query $q$ and squared radius $r$ on the ball tree built from $L$ if and only if $p$
occurs in $L$ and the squared distance from $q$ to $p$ is at most $r$. -/
theorem mem_search_build_iff (pts : List (Fin d → Int))
    {query p : Fin d → Int} {radius : Nat} :
    p ∈ (build pts).search query radius ↔
      p ∈ pts ∧ distSq query p ≤ radius := by
  rw [mem_search_iff (valid_build pts), mem_toList_build_iff]

end BallTree

end Cslib.Algorithms.Lean
