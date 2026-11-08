/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.BandedAlignment
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.BandedAlignment

/-!
# Banded alignment tests

Closed checks with match `2`, mismatch `-1`, gap `-1`: width `0` forces the
diagonal (`[true, false]` vs `[true, false]` scores `4`), width `0` admits no
alignment when the lengths differ, and width `1` recovers the optimum `1` for
`[true]` vs `[true, false]`. Axiom audit follows.
-/

namespace Cslib.Algorithms.Lean

/-- Match `2`, mismatch `-1` scoring, used by the tests below. -/
def bandedTestScore : Bool → Bool → ℤ := fun a b => if a = b then 2 else -1

example : bandedScore bandedTestScore (-1) 0 [true, false] [true, false] = some 4 := by
  decide

example : bandedScore bandedTestScore (-1) 0 [true] [true, false] = none := by decide

example : bandedScore bandedTestScore (-1) 1 [true] [true, false] = some 1 := by
  decide

example : bandedScore bandedTestScore (-1) 0 [true, false] [false, true]
    = some (-2) := by decide

example (σ : Bool → Bool → ℤ) (xs ys : List Bool) (s : ℤ)
    (h : bandedScore σ (-1) 2 xs ys = some s) :
    s ≤ nwScore σ (-1) xs ys :=
  bandedScore_le_nwScore σ (-1) 2 h

example (σ : Bool → Bool → ℤ) (xs ys : List Bool)
    (h : (2 : ℤ) < |(xs.length : ℤ) - (ys.length : ℤ)|) :
    bandedScore σ (-1) 2 xs ys = none :=
  bandedScore_none_of_length_diff_gt σ (-1) 2 h

example (σ : Bool → Bool → ℤ) (xs ys : List Bool)
    (h : |(xs.length : ℤ) - (ys.length : ℤ)| ≤ (2 : ℤ)) :
    ∃ s, bandedScore σ (-1) 2 xs ys = some s :=
  bandedScore_some_of_length_diff_le σ (-1) 2 h

#print axioms bandedScore_le_nwScore
#print axioms bandedScore_eq_nwScore_of_banded_optimal
#print axioms bandedScore_none_of_length_diff_gt
#print axioms bandedScore_some_of_length_diff_le

end Cslib.Algorithms.Lean
