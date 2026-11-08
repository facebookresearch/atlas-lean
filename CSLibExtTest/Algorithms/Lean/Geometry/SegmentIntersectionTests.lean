/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.SegmentIntersection
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Rat
public meta import CSLibExt.Algorithms.Lean.Geometry.SegmentIntersection
public meta import Mathlib.Algebra.Order.Field.Rat

/-!
# Segment-intersection tests

Executed fixtures over `ℚ` check the answer and the cost on a proper crossing, parallel and
same-side disjoint segments, a T junction, collinear overlapping and collinear disjoint segments,
vertical segments, and segments that are single points. Closed examples evaluate the test with
`decide +kernel` (`ℚ` arithmetic does not reduce under plain `decide`) and turn the Boolean answer
into a common point, or its absence, through the main theorem; the theorem is also instantiated
over `ℝ`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

private meta def check (label : String) (p1 p2 p3 p4 : ℚ × ℚ) (expected : Bool) (cost : ℕ) :
    IO Unit := do
  let r := segmentsIntersect p1 p2 p3 p4
  unless r.ret == expected && r.time == cost do
    throw (IO.userError s!"{label}: got {r.ret} with cost {r.time}")
  IO.println s!"{label}: {r.ret}, cost {r.time}"

#eval check "proper crossing" (0, 0) (4, 4) (0, 4) (4, 0) true 4
#eval check "parallel, disjoint" (0, 0) (1, 1) (2, 0) (3, 1) false 4
#eval check "same side of the other line" (0, 0) (1, 1) (3, 0) (2, 1) false 4
#eval check "crossing, CLRS Figure 33.3(a) shape" (0, 0) (2, 2) (3, 0) (1, 2) true 4
#eval check "T junction (endpoint on the other segment)" (0, 0) (2, 0) (1, 0) (1, 2) true 5
#eval check "collinear, overlapping" (0, 0) (2, 2) (1, 1) (3, 3) true 6
#eval check "collinear, one inside the other" (0, 0) (3, 3) (1, 1) (2, 2) true 7
#eval check "collinear, disjoint" (0, 0) (1, 1) (2, 2) (3, 3) false 8
#eval check "collinear, touching at an endpoint" (0, 0) (1, 1) (1, 1) (3, 3) true 6
#eval check "vertical, overlapping" (0, 0) (0, 2) (0, 1) (0, 3) true 6
#eval check "point on a segment" (1, 1) (1, 1) (0, 0) (2, 2) true 5
#eval check "two distinct points" (0, 0) (0, 0) (1, 1) (1, 1) false 8
#eval check "the same point twice" (1, 1) (1, 1) (1, 1) (1, 1) true 5
#eval check "fractional crossing" (0, 0) (1, 1 / 3) (1 / 2, 0) (1 / 2, 1) true 4

example : (segmentsIntersect ((0, 0) : ℚ × ℚ) (4, 4) (0, 4) (4, 0)).ret = true := by
  decide +kernel
example : (segmentsIntersect ((0, 0) : ℚ × ℚ) (1, 1) (2, 2) (3, 3)).ret = false := by
  decide +kernel

/-- The collinear disjoint pair has no common point, by the theorem rather than by hand. -/
example : ¬ (segment ℚ ((0, 0) : ℚ × ℚ) (1, 1) ∩ segment ℚ (2, 2) (3, 3)).Nonempty := by
  rw [← segmentsIntersect_ret_eq_true_iff]
  decide +kernel

example : (segment ℚ ((0, 0) : ℚ × ℚ) (2, 0) ∩ segment ℚ (1, 0) (1, 2)).Nonempty :=
  (segmentsIntersect_ret_eq_true_iff _ _ _ _).1 (by decide +kernel)

/-- Over the reals, a common point exists exactly when the test says so. -/
example (p1 p2 p3 p4 : ℝ × ℝ) :
    (segmentsIntersect p1 p2 p3 p4).ret = true ↔ (segment ℝ p1 p2 ∩ segment ℝ p3 p4).Nonempty :=
  segmentsIntersect_ret_eq_true_iff p1 p2 p3 p4

example (p1 p2 p3 p4 : ℝ × ℝ) :
    4 ≤ (segmentsIntersect p1 p2 p3 p4).time ∧ (segmentsIntersect p1 p2 p3 p4).time ≤ 8 :=
  segmentsIntersect_time p1 p2 p3 p4

#print axioms segmentsIntersect
#print axioms segmentsIntersect_ret_eq_true_iff
#print axioms segmentsIntersect_time
#print axioms mem_segment_of_direction_eq_zero
#print axioms inter_nonempty_of_straddles
#print axioms straddles_or_endpoint_mem

end Cslib.Algorithms.Lean.Geometry
