/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Euler tour of a rooted tree

The Euler tour of a rooted tree records each node on entry
and again after every child subtree, with depths; it has
`2n - 1` entries for a tree with `n` nodes. This is the tour
used by the Euler-tour plus RMQ reduction for LCA; the RMQ
step is not included here.
-/

@[expose] public section

/-- Rooted trees for LCA/Euler-tour (core of ALG-15a). -/
inductive RTree : Type
  | node (a : ℕ) (children : List RTree) : RTree

/-- Number of nodes. -/
def RTree.size : RTree → ℕ
  | .node _ cs => 1 + (cs.map RTree.size).sum

/-- Euler tour with depths: entering a node records it, and it
is recorded again after each child subtree. -/
def RTree.tour : ℕ → RTree → List (ℕ × ℕ)
  | d, .node a cs => (a, d) :: cs.flatMap (fun c => c.tour (d + 1) ++ [(a, d)])

/-- The tour of a tree with `n` nodes has `2n - 1` entries:
`length + 1 = 2 * size`. -/
theorem RTree.tour_length_add_one (d : ℕ) (t : RTree) :
    (t.tour d).length + 1 = 2 * t.size := by
  have h : ∀ (d : ℕ), (t.tour d).length + 1 = 2 * t.size :=
    RTree.rec (motive_1 := fun t => ∀ d, (t.tour d).length + 1 = 2 * t.size)
      (motive_2 := fun cs => ∀ d a, (cs.flatMap (fun c => c.tour (d + 1) ++ [(a, d)])).length = (cs.map (fun c => 2 * c.size)).sum)
      (fun a cs ih d => by
        simp only [RTree.tour.eq_1, RTree.size.eq_1, List.length_cons]
        rw [ih d a]
        have h2 : ∀ l : List RTree,
            (l.map (fun c => 2 * c.size)).sum = 2 * (l.map RTree.size).sum := by
          intro l
          induction l with
          | nil => rfl
          | cons c cs ih3 =>
              rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih3,
                Nat.mul_add]
        rw [h2 cs]
        omega)
      (fun d a => by simp)
      (fun head tail ih1 ih2 d a => by
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
          List.map_cons, List.sum_cons]
        rw [ih1 (d + 1), ih2 d a])
      t
  exact h d

/-- The root entry is first in the tour. -/
theorem RTree.tour_head (d : ℕ) (a : ℕ) (cs : List RTree) :
    (RTree.node a cs).tour d = (a, d) :: cs.flatMap (fun c => c.tour (d + 1) ++ [(a, d)]) := by
  exact RTree.tour.eq_1 d a cs

end
