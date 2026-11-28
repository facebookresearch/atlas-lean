/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Tactic.Abel

/-!
# Metric TSP: the double-tree 2-approximation

`APPROX-TSP-TOUR` from CLRS, third edition, Section 35.2.1, and the proof of Theorem 35.2: on a
complete graph whose costs are symmetric and satisfy the triangle inequality, the vertices of a
minimum spanning tree listed in preorder form a tour costing at most twice an optimal tour.

The two inequalities of the proof are formalized for an arbitrary cost function `d : α → α → R`
into an ordered additive monoid (`IsMetricCost`: symmetric, zero on the diagonal, nonnegative,
triangle inequality):

* `tourCost_preorder_le`: the preorder tour of a rooted tree costs at most twice the tree (CLRS's
  full walk visits every tree edge twice, and shortcutting repeated vertices does not increase the
  cost, by the triangle inequality);
* `weight_le_tourCost`: a minimum spanning tree costs at most any tour (deleting one edge of a tour
  leaves a spanning path, which is a spanning tree).

`approxTSPTour_two_approx` combines them. Here the minimum spanning tree is an *input* in rooted
form, a left-child right-sibling `Forest` below a root, with the minimality hypothesis quantified
over all rooted spanning trees. Computing it with Prim's algorithm (CLRS step 2,
`CSLibExt.Algorithms.Lean.Graph.Prim`) and converting Prim's parent array to this form is a
separate step.

## Cost model

One unit per vertex visited by the preorder walk; the tree is given. A tour of `n` vertices costs
`n`. The walk threads a suffix accumulator, so the host-language work is linear as well. CLRS's
`Θ(V²)` bound is dominated by Prim's algorithm, which is not part of this module.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MetricTSP

open Cslib.Algorithms.Lean TimeM

universe u v

variable {α : Type u} {R : Type v} [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]

/-- **Metric cost function.** A cost function $d$ assigning to each pair of vertices a value in a
linearly ordered additive commutative monoid is metric when, for all vertices $x$, $y$, $z$, it
is symmetric, $d(x, y) = d(y, x)$, zero on the diagonal, $d(x, x) = 0$, nonnegative,
$0 \le d(x, y)$, and satisfies the triangle inequality $d(x, z) \le d(x, y) + d(y, z)$. -/
structure IsMetricCost (d : α → α → R) : Prop where
  symm : ∀ x y, d x y = d y x
  self : ∀ x, d x x = 0
  nonneg : ∀ x y, 0 ≤ d x y
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- **Cost of a walk.** Let $d$ be a cost function on the vertices with values in an additive
commutative monoid. For a vertex $x$ and a list $L = [y_1, \dots, y_n]$ of vertices, the cost of
the walk from $x$ through $L$ is $d(x, y_1) + d(y_1, y_2) + \dots + d(y_{n-1}, y_n)$, and $0$
when $L$ is empty. -/
def pathFrom (d : α → α → R) : α → List α → R
  | _, [] => 0
  | x, y :: L => d x y + pathFrom d y L

/-- **Cost of a closed tour.** For a cost function $d$ on the vertices with values in an additive
commutative monoid, the cost of the closed tour that visits $x_0, x_1, \dots, x_k$ in order and
returns to its first vertex is $\sum_{i=1}^{k} d(x_{i-1}, x_i) + d(x_k, x_0)$. The empty tour
costs $0$. -/
def tourCost (d : α → α → R) : List α → R
  | [] => 0
  | h :: t => pathFrom d h (t ++ [h])

/-- **Rooted forest in left-child right-sibling form.** A rooted forest with vertices in $\alpha$
is either empty, or consists of a first tree with root $v$, whose subtrees form a forest (the
children of $v$), followed by a forest of the remaining trees (the siblings of $v$). -/
inductive Forest (α : Type u) where
  | nil : Forest α
  | cons (v : α) (children siblings : Forest α) : Forest α

namespace Forest

/-- **Preorder of a forest.** The list of the vertices of a forest in preorder: empty for the empty
forest, and for a forest with first root $v$, children forest $C$ and sibling forest $S$, the
vertex $v$, followed by the preorder of $C$, followed by the preorder of $S$.

The preorder walk computes this list without appending lists. -/
def preorder : Forest α → List α
  | nil => []
  | cons v ch sib => v :: ch.preorder ++ sib.preorder

/-- **Weight of a forest below a vertex.** For a cost function $d$ and a vertex $p$, the weight
of a forest hanging below $p$ is the total cost of its tree edges: each top-level vertex $v$ is
joined to $p$ by an edge of cost $d(p, v)$, and each vertex $u$ is joined to each of its children
$c$ by an edge of cost $d(u, c)$. The empty forest has weight $0$. -/
def weight (d : α → α → R) (p : α) : Forest α → R
  | nil => 0
  | cons v ch sib => d p v + ch.weight d v + sib.weight d p

/-- **Path as a forest.** The forest of a list $x_1, x_2, \dots, x_n$ of vertices is the path
$x_1, x_2, \dots, x_n$: $x_1$ is its only top-level vertex and each $x_{i+1}$ is the only child
of $x_i$. The empty list gives the empty forest. -/
def chain : List α → Forest α
  | [] => nil
  | x :: xs => cons x (chain xs) nil

end Forest

/-- **Preorder walk with an accumulator.** For a forest $F$ and a list $a$ of vertices, this is the
timed computation defined as follows. On the empty forest it returns $a$ at no cost. On a forest
with first root $v$, children forest $C$ and sibling forest $S$, it charges one time unit, walks
$S$ with accumulator $a$ to get a list $b$, walks $C$ with accumulator $b$ to get a list $c$, and
returns $v$ followed by $c$. It thus returns the vertices of $F$ in preorder followed by $a$, at
one time unit per vertex of $F$.

The accumulator means no list is ever appended, so the untimed work is linear as well. -/
def preorderWalkAux : Forest α → List α → TimeM ℕ (List α)
  | .nil, acc => pure acc
  | .cons v ch sib, acc => do
      ✓
      let b ← preorderWalkAux sib acc
      let a ← preorderWalkAux ch b
      pure (v :: a)

/-- **Preorder walk.** For a forest $F$, the preorder walk of $F$ is the preorder walk of $F$ with
the empty list as accumulator: a timed computation that returns the vertices of $F$ in preorder,
at one time unit per vertex. -/
def preorderWalk (F : Forest α) : TimeM ℕ (List α) := preorderWalkAux F []

/-- **The APPROX-TSP-TOUR algorithm.** CLRS `APPROX-TSP-TOUR`, steps 3 and 4: given a root $r$
and a forest $F$ (the subtrees of a spanning tree with root $r$), return the tour that lists $r$
followed by the vertices of $F$ in preorder. As a timed computation it charges one unit for $r$
and one unit for each vertex visited by the preorder walk of $F$. -/
def approxTSPTour (r : α) (F : Forest α) : TimeM ℕ (List α) := do
  ✓
  let w ← preorderWalk F
  pure (r :: w)

/-! ## The walk -/

/-- **Result of the preorder walk with an accumulator.** For every forest $F$ and every list $a$
of vertices, the preorder walk of $F$ with accumulator $a$ returns the vertices of $F$ in
preorder followed by $a$. -/
theorem preorderWalkAux_ret (F : Forest α) (acc : List α) :
    (preorderWalkAux F acc).ret = F.preorder ++ acc := by
  induction F generalizing acc with
  | nil => rfl
  | cons v ch sib ihc ihs => simp [preorderWalkAux, Forest.preorder, ihc, ihs]

theorem preorderWalkAux_time (F : Forest α) (acc : List α) :
    (preorderWalkAux F acc).time = F.preorder.length := by
  induction F generalizing acc with
  | nil => rfl
  | cons v ch sib ihc ihs =>
      simp only [preorderWalkAux, time_bind, time_tick, time_pure, ihc, ihs, Forest.preorder,
        List.length_cons, List.length_append]
      omega

@[simp]
theorem preorderWalk_ret (F : Forest α) : (preorderWalk F).ret = F.preorder := by
  simp [preorderWalk, preorderWalkAux_ret]

@[simp]
theorem preorderWalk_time (F : Forest α) : (preorderWalk F).time = F.preorder.length :=
  preorderWalkAux_time F []

@[simp]
theorem approxTSPTour_ret (r : α) (F : Forest α) : (approxTSPTour r F).ret = r :: F.preorder := by
  simp [approxTSPTour]

/-- **Running time of `APPROX-TSP-TOUR`.** For every root $r$ and forest $F$, the running time of
`APPROX-TSP-TOUR` on $r$ and $F$ equals the length of the list of $r$ followed by the vertices of
$F$ in preorder: one unit per vertex of the returned tour. -/
@[simp]
theorem approxTSPTour_time (r : α) (F : Forest α) :
    (approxTSPTour r F).time = (r :: F.preorder).length := by
  simp only [approxTSPTour, time_bind, time_tick, time_pure, preorderWalk_time, List.length_cons]
  omega

/-! ## Path costs -/

omit [LinearOrder R] [IsOrderedAddMonoid R] in
theorem pathFrom_append (d : α → α → R) (x : α) (A B : List α) :
    pathFrom d x (A ++ B) = pathFrom d x A + pathFrom d (A.getLastD x) B := by
  induction A generalizing x with
  | nil => simp [pathFrom]
  | cons y A ih =>
      simp only [List.cons_append, pathFrom, ih, List.getLastD_cons, add_assoc]

variable {d : α → α → R}

/-- **Changing the starting vertex of a walk.** Let $d$ be a cost function on the vertices with
values in a linearly ordered additive commutative monoid, which is symmetric, zero on the
diagonal, nonnegative, and satisfies the triangle inequality. For vertices $q$, $p$ and a list $L$
of vertices, the cost of the walk from $q$ through $L$ is at most $d(q, p)$ plus the cost of the
walk from $p$ through $L$. -/
theorem pathFrom_le_add (hd : IsMetricCost d) (q p : α) (L : List α) :
    pathFrom d q L ≤ d q p + pathFrom d p L := by
  cases L with
  | nil => simpa [pathFrom] using hd.nonneg q p
  | cons y L =>
      simp only [pathFrom, ← add_assoc]
      exact add_le_add (hd.triangle q p y) le_rfl

/-- **Shortcutting a closed walk through its base point.** Let $d$ be a cost function on the
vertices with values in a linearly ordered additive commutative monoid, which is symmetric, zero
on the diagonal, nonnegative, and satisfies the triangle inequality. For a vertex $p$ and lists
$A$, $B$ of vertices, the cost of the walk that starts at $p$, visits $A$ and then $B$ in order
and returns to $p$ is at most the cost of the walk from $p$ through $A$ back to $p$ plus the cost
of the walk from $p$ through $B$ back to $p$. -/
theorem pathFrom_append_append_le (hd : IsMetricCost d) (p : α) (A B : List α) :
    pathFrom d p (A ++ B ++ [p]) ≤ pathFrom d p (A ++ [p]) + pathFrom d p (B ++ [p]) := by
  rw [List.append_assoc, pathFrom_append, pathFrom_append d p A [p]]
  simp only [pathFrom, add_zero, add_assoc]
  exact add_le_add le_rfl (pathFrom_le_add hd _ p _)

/-- **Rerouting the end of a walk.** Let $d$ be a cost function on the vertices with values in a
linearly ordered additive commutative monoid, which is symmetric, zero on the diagonal,
nonnegative, and satisfies the triangle inequality. For vertices $v$, $p$ and a list $C$ of
vertices, the cost of the walk from $v$ through $C$ ending at $p$ is at most the cost of the walk
from $v$ through $C$ ending back at $v$, plus $d(v, p)$. -/
theorem pathFrom_append_singleton_le (hd : IsMetricCost d) (v p : α) (C : List α) :
    pathFrom d v (C ++ [p]) ≤ pathFrom d v (C ++ [v]) + d v p := by
  rw [pathFrom_append, pathFrom_append]
  simp only [pathFrom, add_zero, add_assoc]
  exact add_le_add le_rfl (hd.triangle _ v p)

/-! ## The double-tree bound -/

/-- **The closed preorder walk below a vertex costs at most twice the forest.** Let $d$ be a cost
function on the vertices with values in a linearly ordered additive commutative monoid, which is
symmetric, zero on the diagonal, nonnegative, and satisfies the triangle inequality. For a forest
$F$ and a vertex $p$, let $w$ be the weight of $F$ hanging below $p$: the total cost of the edges
joining $p$ to the top-level vertices of $F$ and each vertex of $F$ to its children. Then the cost
of the walk that starts at $p$, visits the vertices of $F$ in preorder and returns to $p$ is at
most $w + w$. -/
theorem pathFrom_preorder_le (hd : IsMetricCost d) (F : Forest α) (p : α) :
    pathFrom d p (F.preorder ++ [p]) ≤ F.weight d p + F.weight d p := by
  induction F generalizing p with
  | nil => simp [Forest.preorder, Forest.weight, pathFrom, hd.self]
  | cons v ch sib ihc ihs =>
      simp only [Forest.preorder, Forest.weight]
      have hsplit := pathFrom_append_append_le hd p (v :: ch.preorder) sib.preorder
      have hchild : pathFrom d p (v :: ch.preorder ++ [p]) ≤
          d p v + (ch.weight d v + ch.weight d v) + d p v := by
        simp only [List.cons_append, pathFrom]
        rw [add_assoc]
        refine add_le_add le_rfl ?_
        calc pathFrom d v (ch.preorder ++ [p])
            ≤ pathFrom d v (ch.preorder ++ [v]) + d v p := pathFrom_append_singleton_le hd v p _
          _ ≤ (ch.weight d v + ch.weight d v) + d p v := by
            rw [hd.symm v p]
            exact add_le_add (ihc v) le_rfl
      calc pathFrom d p ((v :: ch.preorder) ++ sib.preorder ++ [p])
          ≤ pathFrom d p (v :: ch.preorder ++ [p]) + pathFrom d p (sib.preorder ++ [p]) := hsplit
        _ ≤ (d p v + (ch.weight d v + ch.weight d v) + d p v) +
              (sib.weight d p + sib.weight d p) := add_le_add hchild (ihs p)
        _ = d p v + ch.weight d v + sib.weight d p + (d p v + ch.weight d v + sib.weight d p) := by
          abel

/-- **The preorder tour costs at most twice the tree.** Let $d$ be a cost function on the
vertices with values in a linearly ordered additive commutative monoid that is symmetric, zero on
the diagonal, nonnegative and satisfies the triangle inequality. Let $T$ be a rooted tree with
root $r$, given by the forest $F$ of the subtrees of $r$, and let $w(T)$ be its weight, the total
cost of its edges. Then the closed tour that visits $r$, then the vertices of $F$ in preorder, and
returns to $r$ costs at most $2\,w(T)$.

Source: CLRS Theorem 35.2, first half. -/
theorem tourCost_preorder_le (hd : IsMetricCost d) (r : α) (F : Forest α) :
    tourCost d (r :: F.preorder) ≤ 2 • F.weight d r := by
  rw [two_nsmul]
  exact pathFrom_preorder_le hd F r

/-! ## The spanning-tree lower bound -/

/-- **Preorder of a path.** For every list $L$ of vertices, the preorder of the forest of $L$
(the path through the vertices of $L$ in order) is $L$ itself. -/
@[simp]
theorem Forest.preorder_chain (xs : List α) : (Forest.chain xs).preorder = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Forest.chain, Forest.preorder, ih]

omit [LinearOrder R] [IsOrderedAddMonoid R] in
@[simp]
theorem Forest.weight_chain (d : α → α → R) (p : α) (xs : List α) :
    (Forest.chain xs).weight d p = pathFrom d p xs := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp [Forest.chain, Forest.weight, pathFrom, ih]

/-- **Rooted spanning tree of a vertex list.** The tree with root $r$ and subtree forest $F$ is a
spanning tree of a list $V$ of vertices when the vertices of $V$ are distinct and the list of $r$
followed by the vertices of $F$ in preorder is a permutation of $V$: the vertices of the tree are
those of $V$, each exactly once. -/
def IsSpanning (V : List α) (r : α) (F : Forest α) : Prop := V.Nodup ∧ (r :: F.preorder).Perm V

/-- **Minimum spanning tree of a vertex list.** Let $d$ be a cost function on the vertices with
values in a linearly ordered additive commutative monoid. The tree with root $r$ and subtree
forest $F$ is a minimum spanning tree of a list $V$ of vertices for $d$ when it is a spanning tree
of $V$ (the vertices of $V$ are distinct and the list of $r$ followed by the vertices of $F$ in
preorder is a permutation of $V$) and, for every vertex $r'$ and forest $F'$ such that the tree
with root $r'$ and subtree forest $F'$ is a spanning tree of $V$, the weight of $F$ below $r$ is
at most the weight of $F'$ below $r'$. -/
def IsMinSpanning (d : α → α → R) (V : List α) (r : α) (F : Forest α) : Prop :=
  IsSpanning V r F ∧ ∀ r' F', IsSpanning V r' F' → F.weight d r ≤ F'.weight d r'

/-- **Tour of a vertex list.** A list $H$ is a tour of a list $V$ of vertices when the vertices of
$V$ are distinct and $H$ is a permutation of $V$: $H$ lists each vertex of $V$ exactly once and
nothing else. -/
def IsTour (V H : List α) : Prop := V.Nodup ∧ H.Perm V

/-- **A minimum spanning tree costs at most any tour.** Let $d$ be a cost function on the
vertices with values in a linearly ordered additive commutative monoid that is symmetric, zero on
the diagonal, nonnegative and satisfies the triangle inequality. Let $V$ be a list of distinct
vertices. Let $T$ be a minimum spanning tree of $V$ for $d$: a rooted tree whose vertices are the
elements of $V$, each once, whose weight (the total cost of its edges) is at most that of every
such tree. Let $H$ be a tour of $V$, a list that is a permutation of $V$. Then the weight of $T$
is at most the cost of the closed tour $H$.

A tour minus its closing edge is a spanning path, which is a spanning tree.

Source: CLRS Theorem 35.2, second half. -/
theorem weight_le_tourCost (hd : IsMetricCost d) {V : List α} {r : α} {F : Forest α}
    (hT : IsMinSpanning d V r F) {H : List α} (hH : IsTour V H) :
    F.weight d r ≤ tourCost d H := by
  cases H with
  | nil =>
      have h1 := hT.1.2.length_eq
      have h2 : ([] : List α).length = V.length := List.Perm.length_eq hH.2
      rw [List.length_cons] at h1
      rw [List.length_nil] at h2
      omega
  | cons h t =>
      have hpath := hT.2 h (Forest.chain t) ⟨hH.1, by simpa using hH.2⟩
      rw [Forest.weight_chain] at hpath
      refine hpath.trans ?_
      simp only [tourCost, pathFrom_append]
      exact le_add_of_nonneg_right (by simp only [pathFrom, add_zero]; exact hd.nonneg _ _)

/-! ## The 2-approximation -/

/-- **The approximate TSP tour is a tour.** Let $V$ be a list of distinct vertices, and let $r$
and $F$ be such that $r$ followed by the vertices of the forest $F$ in preorder is a permutation
of $V$ (the tree with root $r$ and subtree forest $F$ spans $V$). Then the list returned by
`APPROX-TSP-TOUR` on $r$ and $F$ is a tour of $V$: it is a permutation of $V$. -/
theorem approxTSPTour_isTour {V : List α} {r : α} {F : Forest α} (hT : IsSpanning V r F) :
    IsTour V (approxTSPTour r F).ret := by
  exact ⟨hT.1, by simpa using hT.2⟩

/-- **APPROX-TSP-TOUR on a given minimum spanning tree costs at most twice any tour.** Let $d$ be a
cost function on vertices with values in a linearly ordered additive commutative monoid that is
symmetric, zero on the diagonal, nonnegative and satisfies the triangle inequality. Let $V$ be a
list of vertices, let the tree with root $r$ and subtree forest $F$ be a minimum spanning tree of
$V$ for $d$, and let $H$ be a tour of $V$. Then the cost under $d$ of the closed tour returned by
`APPROX-TSP-TOUR` on $r$ and $F$ is at most twice the cost under $d$ of the closed tour $H$.

Source: CLRS, third edition, Theorem 35.2. -/
theorem approxTSPTour_two_approx (hd : IsMetricCost d) {V : List α} {r : α} {F : Forest α}
    (hT : IsMinSpanning d V r F) {H : List α} (hH : IsTour V H) :
    tourCost d (approxTSPTour r F).ret ≤ 2 • tourCost d H := by
  rw [approxTSPTour_ret]
  have h := weight_le_tourCost hd hT hH
  refine (tourCost_preorder_le hd r F).trans ?_
  rw [two_nsmul, two_nsmul]
  exact add_le_add h h

end Cslib.Algorithms.Lean.MetricTSP
