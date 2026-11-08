/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.ConvexHull
public meta import CSLibExt.Algorithms.Lean.Geometry.ConvexHull
public meta import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Rat

/-!
# Lower convex chain tests

Executed fixtures over `ℚ`, unsorted input: the chain is compared with the expected vertices
where known, and on every fixture the run re-checks the specification (strict left turns, every
input point on or left of every edge, first and last points lexicographically least and greatest)
and the bound of `2 n` orientation tests. Degenerate inputs: collinear points on an edge, a
vertical edge, all points on one vertical line, a concave arc (only the endpoints remain).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

private meta def lexLe (a b : ℚ × ℚ) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

private meta def check (label : String) (ps : List (ℚ × ℚ))
    (expected : Option (List (ℚ × ℚ)) := none) : IO Unit := do
  let r := lowerHullOfPoints ps
  let C := r.ret
  let turns := (List.range (C.length - 2)).all fun i =>
    decide (0 < cross (C[i + 1]! - C[i]!) (C[i + 2]! - C[i]!))
  let left := ps.all fun s => (List.range (C.length - 1)).all fun i =>
    decide (0 ≤ cross (C[i + 1]! - C[i]!) (s - C[i]!))
  let ends := ps.all fun s => lexLe C.head! s && lexLe s C.getLast!
  let exp := match expected with
    | some e => C == e
    | none => true
  unless turns && left && ends && exp && r.time ≤ 2 * ps.length do
    throw (IO.userError s!"{label}: chain {C}, {r.time} tests")
  IO.println s!"{label}: {C.length} of {ps.length} points, {r.time} tests ≤ {2 * ps.length}"
  if C.length ≤ 6 then IO.println s!"  chain {C}"

#eval check "square, interior and bottom-edge points"
  [(1, 1), (2, 2), (0, 2), (1, 0), (0, 0), (2, 0), (1, 1/2), (3/2, 0)]
  (some [(0, 0), (2, 0), (2, 2)])
#eval check "vertical line" ((List.range 6).map fun i => (0, (i : ℚ))) (some [(0, 0), (0, 5)])
#eval check "concave arc y = -x²"
  ((List.range 11).map fun i => ((i : ℚ) - 5, -((i : ℚ) - 5) ^ 2)) (some [(-5, -25), (5, -25)])
#eval check "convex arc y = x²" ((List.range 11).map fun i => ((i : ℚ) - 5, ((i : ℚ) - 5) ^ 2))
#eval check "200 scattered points"
  ((List.range 200).map fun i => (((i * 37 + 11) % 211 : ℕ), ((i * 53 + 7) % 199 : ℕ)))

example (ps : List (ℚ × ℚ)) (hs : ps.Pairwise fun a b => toLex a < toLex b) {s : ℚ × ℚ}
    (h : s ∈ ps) :
    (lowerHull ps).ret.IsChain fun a b => 0 ≤ cross (b - a) (s - a) :=
  lowerHull_left_of_edges ps hs h

example (ps : List (ℚ × ℚ)) : (lowerHull ps).time ≤ 2 * ps.length := lowerHull_time_le ps

#print axioms lowerHull_sublist
#print axioms lowerHull_head?
#print axioms lowerHull_getLast?
#print axioms lowerHull_turn_left
#print axioms lowerHull_left_of_edges
#print axioms lowerHull_time_le
#print axioms lowerHullOfPoints_spec

end Cslib.Algorithms.Lean.Geometry
