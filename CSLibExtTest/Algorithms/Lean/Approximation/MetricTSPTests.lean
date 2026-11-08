/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.MetricTSP
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
public meta import CSLibExt.Algorithms.Lean.Approximation.MetricTSP
public meta import Mathlib.Algebra.Order.Ring.Int

/-!
# Metric TSP tests

The cost is the Manhattan distance on `ℤ × ℤ`, proved to be an `IsMetricCost`. Executed fixtures
build rooted spanning trees, run `approxTSPTour`, and compare the tour, its cost, twice the tree
weight, and the walk cost with expected values, including a tree where shortcutting saves cost and
a single vertex. Closed examples check the spanning and tour predicates (a repeated vertex is not a
tour), instantiate the double-tree bound on a concrete tree, and the 2-approximation abstractly.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MetricTSP

/-- Manhattan distance. -/
private def manhattan (p q : ℤ × ℤ) : ℤ := |p.1 - q.1| + |p.2 - q.2|

private theorem manhattan_isMetric : IsMetricCost manhattan where
  symm x y := by simp only [manhattan, abs_sub_comm]
  self x := by simp [manhattan]
  nonneg x y := add_nonneg (abs_nonneg _) (abs_nonneg _)
  triangle x y z := by
    simp only [manhattan]
    have h1 := abs_sub_le x.1 y.1 z.1
    have h2 := abs_sub_le x.2 y.2 z.2
    linarith

private meta def check (d : ℤ × ℤ → ℤ × ℤ → ℤ) (label : String) (r : ℤ × ℤ)
    (F : Forest (ℤ × ℤ)) (tour : List (ℤ × ℤ)) (cost twiceTree ops : ℤ) : IO Unit := do
  let res := approxTSPTour r F
  let c := tourCost d res.ret
  let w := 2 * F.weight d r
  unless res.ret == tour && c == cost && w == twiceTree && (res.time : ℤ) == ops && c ≤ w do
    throw (IO.userError s!"{label}: tour {res.ret}, cost {c}, 2 * tree {w}, {res.time} ops")
  IO.println s!"{label}: tour {res.ret}, cost {c} ≤ 2 * tree {w}, {res.time} ops"

open Forest in
/-- A star centered at `(1, 1)` over the corners of a 2-by-2 square. -/
private def star : Forest (ℤ × ℤ) :=
  cons (0, 0) nil (cons (0, 2) nil (cons (2, 2) nil (cons (2, 0) nil nil)))

open Forest in
/-- A path along three sides of the square, rooted at a corner. -/
private def sides : Forest (ℤ × ℤ) := chain [(0, 2), (2, 2), (2, 0)]

open Forest in
/-- A tree with two branches below the root, where the walk shortcuts from one leaf to the next
branch: root `(0, 0)` with children `(0, 3)` (child `(1, 3)`) and `(3, 0)` (child `(3, 1)`). -/
private def branches : Forest (ℤ × ℤ) :=
  cons (0, 3) (cons (1, 3) nil nil) (cons (3, 0) (cons (3, 1) nil nil) nil)

#eval check manhattan "star over the square" (1, 1) star
  [(1, 1), (0, 0), (0, 2), (2, 2), (2, 0)] 10 16 5
#eval check manhattan "path along three sides" (0, 0) sides [(0, 0), (0, 2), (2, 2), (2, 0)] 8 12 4
#eval check manhattan "two branches (shortcut (1,3) to (3,0))" (0, 0) branches
  [(0, 0), (0, 3), (1, 3), (3, 0), (3, 1)] 14 16 5
#eval check manhattan "single vertex" (5, 5) .nil [(5, 5)] 0 0 1
/-- A path of `n` unit steps along the `x` axis: the walk threads an accumulator (no appends), so a
long path runs in linear time. -/
private meta def checkLongPath (d : ℤ × ℤ → ℤ × ℤ → ℤ) (n : ℕ) : IO Unit := do
  let pts := (List.range n).map fun i : ℕ => ((i : ℤ) + 1, (0 : ℤ))
  let res := approxTSPTour ((0 : ℤ), (0 : ℤ)) (Forest.chain pts)
  let c := tourCost d res.ret
  unless res.ret == (0, 0) :: pts && c == 2 * n && res.time == n + 1 do
    throw (IO.userError s!"long path: cost {c}, {res.time} ops")
  IO.println s!"path of {n + 1} vertices: cost {c} = 2 * tree {n}, {res.time} ops"

#eval checkLongPath manhattan 20000

/-- The path tree spans the four corners, each once. -/
example : IsSpanning [(0, 0), (0, 2), (2, 2), (2, 0)] (0, 0) sides := by
  unfold IsSpanning
  decide

/-- Repeating a vertex is not a tour, even of a list with the same repetition. -/
example : ¬ IsTour [((0 : ℤ), (0 : ℤ)), (0, 0)] [(0, 0), (0, 0)] := by
  unfold IsTour
  decide

/-- The double-tree bound on a concrete tree. -/
example : tourCost manhattan (approxTSPTour (0, 0) branches).ret ≤
    2 • branches.weight manhattan (0, 0) := by
  rw [approxTSPTour_ret]
  exact tourCost_preorder_le manhattan_isMetric _ _

/-- The 2-approximation for Manhattan costs, for any minimum spanning tree and any tour. -/
example {V : List (ℤ × ℤ)} {r : ℤ × ℤ} {F : Forest (ℤ × ℤ)}
    (hT : IsMinSpanning manhattan V r F) {H : List (ℤ × ℤ)} (hH : IsTour V H) :
    tourCost manhattan (approxTSPTour r F).ret ≤ 2 • tourCost manhattan H :=
  approxTSPTour_two_approx manhattan_isMetric hT hH

example (r : ℤ × ℤ) (F : Forest (ℤ × ℤ)) :
    (approxTSPTour r F).time = (r :: F.preorder).length := approxTSPTour_time r F

#print axioms approxTSPTour
#print axioms approxTSPTour_two_approx
#print axioms tourCost_preorder_le
#print axioms weight_le_tourCost
#print axioms approxTSPTour_isTour
#print axioms approxTSPTour_time

end Cslib.Algorithms.Lean.MetricTSP
