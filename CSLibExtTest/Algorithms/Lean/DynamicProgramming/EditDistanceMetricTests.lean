/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Metric
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Metric

/-!
# Edit-distance metric tests

Executed fixtures: `d(kitten, sitting) = d(sitting, kitten) = 3`; the triangle through
`sitten`: `3 ≤ 1 + 2`; a strict triangle inequality `d(ab, ba) = 2 < 4`. Closed checks: the
theorems instantiated, including positivity off the diagonal. Axiom audit follows.
-/

namespace Cslib.Algorithms.Lean

/-- The unit-cost distance, for the fixtures below. -/
def lev (x y : String) : Nat := (editDistance x.toList y.toList).ret.distance

#guard lev "kitten" "sitting" = 3
#guard lev "sitting" "kitten" = 3
#guard lev "kitten" "sitten" = 1
#guard lev "sitten" "sitting" = 2
#guard lev "ab" "ba" = 2
#guard lev "ab" "aa" + lev "aa" "ba" = 2
#guard lev "ab" "bb" + lev "bb" "ba" = 2
#guard lev "ab" "xy" + lev "xy" "ba" = 4

example (x y : List Char) :
    (editDistance x y).ret.distance = (editDistance y x).ret.distance :=
  editDistance_comm x y

example (x y z : List Char) :
    (editDistance x z).ret.distance ≤
      (editDistance x y).ret.distance + (editDistance y z).ret.distance :=
  editDistance_triangle x y z

example : 0 < (editDistance "ab".toList "ba".toList).ret.distance :=
  (editDistance_pos_iff _ _).mpr (by decide)

#print axioms EditScript.exists_inverse
#print axioms EditScript.exists_compose
#print axioms editDistance_comm
#print axioms editDistance_triangle
#print axioms editDistance_pos_iff

end Cslib.Algorithms.Lean
