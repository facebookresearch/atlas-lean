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

/-- Symmetric, zero on the diagonal, nonnegative, and satisfying the triangle inequality. -/
structure IsMetricCost (d : α → α → R) : Prop where
  symm : ∀ x y, d x y = d y x
  self : ∀ x, d x x = 0
  nonneg : ∀ x y, 0 ≤ d x y
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- The cost of walking from `x` through the vertices of `L` in order. -/
def pathFrom (d : α → α → R) : α → List α → R
  | _, [] => 0
  | x, y :: L => d x y + pathFrom d y L

/-- The cost of the closed tour visiting `H` in order and returning to its first vertex. -/
def tourCost (d : α → α → R) : List α → R
  | [] => 0
  | h :: t => pathFrom d h (t ++ [h])

/-- A rooted forest in left-child right-sibling form: `cons v children siblings`. -/
inductive Forest (α : Type u) where
  | nil : Forest α
  | cons (v : α) (children siblings : Forest α) : Forest α

namespace Forest

/-- The vertices of the forest in preorder (the specification; `preorderWalk` computes it
without appending). -/
def preorder : Forest α → List α
  | nil => []
  | cons v ch sib => v :: ch.preorder ++ sib.preorder

/-- The total cost of the tree edges when the forest hangs below the vertex `p`: each top-level
vertex is joined to `p`, and each vertex to its children. -/
def weight (d : α → α → R) (p : α) : Forest α → R
  | nil => 0
  | cons v ch sib => d p v + ch.weight d v + sib.weight d p

/-- The path `x₁, x₂, …` as a forest: each vertex is the only child of the previous one. -/
def chain : List α → Forest α
  | [] => nil
  | x :: xs => cons x (chain xs) nil

end Forest

/-- The preorder walk of `F` followed by `acc`, one unit per vertex visited. The suffix
accumulator keeps the host-language work linear: no list is appended. -/
def preorderWalkAux : Forest α → List α → TimeM ℕ (List α)
  | .nil, acc => pure acc
  | .cons v ch sib, acc => do
      ✓
      let b ← preorderWalkAux sib acc
      let a ← preorderWalkAux ch b
      pure (v :: a)

/-- The preorder walk, one unit per vertex visited. -/
def preorderWalk (F : Forest α) : TimeM ℕ (List α) := preorderWalkAux F []

/-- CLRS `APPROX-TSP-TOUR`, steps 3 and 4, on a spanning tree with root `r` and the forest `F` of
its subtrees: the tour lists the vertices in preorder. -/
def approxTSPTour (r : α) (F : Forest α) : TimeM ℕ (List α) := do
  ✓
  let w ← preorderWalk F
  pure (r :: w)

/-! ## The walk -/

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

/-- One unit per vertex of the tour. -/
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

/-- Starting from `q` instead of `p` costs at most `d q p` more. -/
theorem pathFrom_le_add (hd : IsMetricCost d) (q p : α) (L : List α) :
    pathFrom d q L ≤ d q p + pathFrom d p L := by
  cases L with
  | nil => simpa [pathFrom] using hd.nonneg q p
  | cons y L =>
      simp only [pathFrom, ← add_assoc]
      exact add_le_add (hd.triangle q p y) le_rfl

/-- Shortcutting through `p`: a closed walk from `p` through `A` and then `B` costs at most the
closed walk through `A` plus the closed walk through `B`. -/
theorem pathFrom_append_append_le (hd : IsMetricCost d) (p : α) (A B : List α) :
    pathFrom d p (A ++ B ++ [p]) ≤ pathFrom d p (A ++ [p]) + pathFrom d p (B ++ [p]) := by
  rw [List.append_assoc, pathFrom_append, pathFrom_append d p A [p]]
  simp only [pathFrom, add_zero, add_assoc]
  exact add_le_add le_rfl (pathFrom_le_add hd _ p _)

/-- Ending at `p` instead of returning to `v` costs at most `d v p` more. -/
theorem pathFrom_append_singleton_le (hd : IsMetricCost d) (v p : α) (C : List α) :
    pathFrom d v (C ++ [p]) ≤ pathFrom d v (C ++ [v]) + d v p := by
  rw [pathFrom_append, pathFrom_append]
  simp only [pathFrom, add_zero, add_assoc]
  exact add_le_add le_rfl (hd.triangle _ v p)

/-! ## The double-tree bound -/

/-- The closed walk from `p` through the preorder of a forest hanging below `p` costs at most twice
the forest's edges. -/
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

/-- CLRS Theorem 35.2, first half: the preorder tour of a tree costs at most twice the tree. -/
theorem tourCost_preorder_le (hd : IsMetricCost d) (r : α) (F : Forest α) :
    tourCost d (r :: F.preorder) ≤ 2 • F.weight d r := by
  rw [two_nsmul]
  exact pathFrom_preorder_le hd F r

/-! ## The spanning-tree lower bound -/

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

/-- `T = (r, F)` is a spanning tree of the list `V` of distinct vertices: its vertices are `V`,
each once. -/
def IsSpanning (V : List α) (r : α) (F : Forest α) : Prop := V.Nodup ∧ (r :: F.preorder).Perm V

/-- `T = (r, F)` is a minimum spanning tree of `V` for the costs `d`. -/
def IsMinSpanning (d : α → α → R) (V : List α) (r : α) (F : Forest α) : Prop :=
  IsSpanning V r F ∧ ∀ r' F', IsSpanning V r' F' → F.weight d r ≤ F'.weight d r'

/-- A tour of the list `V` of distinct vertices lists each of them once. -/
def IsTour (V H : List α) : Prop := V.Nodup ∧ H.Perm V

/-- CLRS Theorem 35.2, second half: a minimum spanning tree costs at most any tour, because a tour
minus its closing edge is a spanning path. -/
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

/-- The result is a tour. -/
theorem approxTSPTour_isTour {V : List α} {r : α} {F : Forest α} (hT : IsSpanning V r F) :
    IsTour V (approxTSPTour r F).ret := by
  exact ⟨hT.1, by simpa using hT.2⟩

/-- CLRS Theorem 35.2: given a minimum spanning tree, `APPROX-TSP-TOUR` returns a tour costing at
most twice any tour, in particular an optimal one. -/
theorem approxTSPTour_two_approx (hd : IsMetricCost d) {V : List α} {r : α} {F : Forest α}
    (hT : IsMinSpanning d V r F) {H : List α} (hH : IsTour V H) :
    tourCost d (approxTSPTour r F).ret ≤ 2 • tourCost d H := by
  rw [approxTSPTour_ret]
  have h := weight_le_tourCost hd hT hH
  refine (tourCost_preorder_le hd r F).trans ?_
  rw [two_nsmul, two_nsmul]
  exact add_le_add h h

end Cslib.Algorithms.Lean.MetricTSP
