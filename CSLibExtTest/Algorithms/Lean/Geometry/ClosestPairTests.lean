/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.ClosestPair
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Rat
public meta import CSLibExt.Algorithms.Lean.Geometry.ClosestPair
public meta import Mathlib.Algebra.Order.Field.Rat

/-!
# Closest-pair tests

Executed fixtures over `ℚ` compare the divide-and-conquer answer (squared distance) with the
expected value and with the brute force, on a closest pair that straddles the dividing line, a
closest pair inside one half, repeated points, collinear points, a vertical line of points (all
`x` equal), small inputs handled by the base case, and a 40-point pseudo-random set. Closed
examples instantiate the specification and the agreement theorem.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

private meta def check (label : String) (ps : List (ℚ × ℚ)) (expected : Option ℚ) :
    IO Unit := do
  let r := closestPair ps
  let b := bruteMin ps
  unless r.ret == expected && r.ret == b.ret do
    throw (IO.userError s!"{label}: got {r.ret}, brute force {b.ret}")
  IO.println s!"{label}: {r.ret} (brute force agrees), {r.time} distances vs {b.time}"

#eval check "empty" [] none
#eval check "one point" [(1, 1)] none
#eval check "two points" [(0, 0), (3, 4)] (some 25)
#eval check "pair across the dividing line" [(0, 0), (10, 0), (4, 5), (5, 5), (20, 1), (30, 9)]
  (some 1)
#eval check "pair inside the left half" [(0, 0), (0, 1), (10, 10), (20, 20), (30, 30), (40, 40)]
  (some 1)
#eval check "repeated point" [(3, 3), (7, 1), (3, 3), (9, 9), (0, 5)] (some 0)
#eval check "collinear" [(0, 0), (5, 0), (2, 0), (9, 0), (11, 0), (15, 0)] (some 4)
#eval check "vertical line (equal x)" [(0, 9), (0, 0), (0, 4), (0, 6), (0, 13)] (some 4)
#eval check "fractions" [(0, 0), (1 / 2, 1 / 3), (3, 3), (3, 7 / 2)] (some (1 / 4))

/-- 40 pseudo-random points on a 100-by-100 grid (a linear congruential sequence). -/
private def scattered : List (ℚ × ℚ) :=
  (List.range 40).map fun i => (((i * 37 + 11) % 101 : ℕ), ((i * 53 + 7) % 97 : ℕ))

#eval check "40 scattered points" scattered (bruteMin scattered).ret

example (ps : List (ℚ × ℚ)) (h : 2 ≤ ps.length) :
    ∃ δ, (closestPair ps).ret = some δ ∧ IsMinPairDist2 ps δ :=
  closestPair_spec ps h

example (ps : List (ℝ × ℝ)) : (closestPair ps).ret = (bruteMin ps).ret :=
  closestPair_eq_bruteMin ps

example (ps : List (ℚ × ℚ)) : (closestPair ps).ret = none ↔ ps.length < 2 :=
  closestPair_eq_none_iff ps

example (ps : List (ℚ × ℚ)) : 2 * (bruteMin ps).time = ps.length * (ps.length - 1) :=
  bruteMin_time ps

#print axioms closestPair
#print axioms closestPair_spec
#print axioms closestPair_eq_bruteMin
#print axioms closestPair_eq_none_iff
#print axioms closestRec_isAnswer
#print axioms bruteMin_time

end Cslib.Algorithms.Lean.Geometry
