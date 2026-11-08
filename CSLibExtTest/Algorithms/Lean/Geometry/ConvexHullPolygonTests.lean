/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.ConvexHullPolygon
public meta import CSLibExt.Algorithms.Lean.Geometry.ConvexHullPolygon
public meta import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Rat

/-!
# Convex hull polygon tests

Executed fixtures over `ℚ`: the input is sorted by `(x, y)` first, then the hull is compared with
the expected counterclockwise polygon where known, and on every fixture the run re-checks that
every input point is on or left of every edge of the closed polygon, that the vertices are input
points, that the closed polygon turns strictly left at every vertex (except on the collinear
inputs, where the theorem does not apply), and the bound of `4 n` orientation tests.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

private meta def check (label : String) (ps : List (ℚ × ℚ))
    (expected : Option (List (ℚ × ℚ)) := none) (strict : Bool := true) : IO Unit := do
  let qs := ps.mergeSort fun a b => decide (toLex a ≤ toLex b)
  let r := convexHull qs
  let H := r.ret
  let W := H ++ H.take 1
  let left := ps.all fun s => (List.range (W.length - 1)).all fun i =>
    decide (0 ≤ cross (W[i + 1]! - W[i]!) (s - W[i]!))
  let sub := H.all fun c => ps.contains c
  let W2 := H ++ H.take 2
  let turns := (List.range (W2.length - 2)).all fun i =>
    decide (0 < cross (W2[i + 1]! - W2[i]!) (W2[i + 2]! - W2[i]!))
  let exp := match expected with
    | some e => H == e
    | none => true
  unless left && sub && exp && (!strict || turns) && r.time ≤ 4 * ps.length do
    throw (IO.userError s!"{label}: hull {H}, {r.time} tests")
  IO.println s!"{label}: {H.length} of {ps.length} points, {r.time} tests ≤ {4 * ps.length}"
  if H.length ≤ 8 then IO.println s!"  hull {H}"

#eval check "square, interior and edge points"
  [(1, 1), (2, 2), (0, 2), (1, 0), (0, 0), (2, 0), (1, 1/2), (3/2, 0), (1, 2), (0, 1)]
  (some [(0, 0), (2, 0), (2, 2), (0, 2)])
#eval check "triangle with a vertical edge" [(0, 0), (1, 0), (1, 1)] (some [(0, 0), (1, 0), (1, 1)])
#eval check "collinear points" ((List.range 6).map fun i => ((i : ℚ), 2 * (i : ℚ)))
  (some [(0, 0), (5, 10)]) (strict := false)
#eval check "two points" [(3, 1), (0, 0)] (some [(0, 0), (3, 1)]) (strict := false)
#eval check "200 scattered points"
  ((List.range 200).map fun i => (((i * 37 + 11) % 211 : ℕ), ((i * 53 + 7) % 199 : ℕ)))

example (ps : List (ℚ × ℚ)) (hs : ps.Pairwise fun a b => toLex a < toLex b)
    (hlen : 2 ≤ ps.length) {s : ℚ × ℚ} (h : s ∈ ps) :
    ((convexHull ps).ret ++ (convexHull ps).ret.take 1).IsChain fun a b =>
      0 ≤ cross (b - a) (s - a) :=
  convexHull_left_of_edges ps hs hlen h

example (ps : List (ℚ × ℚ)) (hs : ps.Pairwise fun a b => toLex a < toLex b)
    (hncol : ∃ a ∈ ps, ∃ b ∈ ps, ∃ c ∈ ps, cross (b - a) (c - a) ≠ 0) :
    TurnsLeft ((convexHull ps).ret ++ (convexHull ps).ret.take 2) :=
  convexHull_turnsLeft ps hs hncol

#print axioms convexHull_turnsLeft
#print axioms upperHull_eq
#print axioms upperHull_sublist
#print axioms upperHull_head?
#print axioms upperHull_getLast?
#print axioms upperHull_turn_left
#print axioms upperHull_left_of_edges
#print axioms upperHull_time_le
#print axioms convexHull_subset
#print axioms convexHull_left_of_edges
#print axioms convexHull_time_le

end Cslib.Algorithms.Lean.Geometry
