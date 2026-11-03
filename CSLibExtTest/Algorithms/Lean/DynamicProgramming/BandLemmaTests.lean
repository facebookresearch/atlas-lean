/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.BandLemma
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.BandLemma

/-!
# Band lemma tests

Unit-cost Levenshtein scoring (`0` for a match, `-1` for a substitution or a gap): gap counts of
concrete alignments, a cost-`2` alignment that is `2`-banded, the banded optimum with width `1`
equal to the Needleman–Wunsch optimum `-1`, and the theorems instantiated. Boundary: with a
positive match score the band lemma's hypothesis fails, and an alignment scoring `1 ≥ -0` leaves
the width-`0` band. Axiom audit follows.
-/

namespace Cslib.Algorithms.Lean

/-- Unit-cost Levenshtein scores in the maximization convention. -/
def unitScore : Bool → Bool → ℤ := fun a b => if a = b then 0 else -1

/-- A positive match score, outside the band lemma's hypothesis. -/
def matchTwoScore : Bool → Bool → ℤ := fun a b => if a = b then 2 else -1

/-- Two gap columns. -/
def twoGaps : Alignment Bool := [(some true, none), (none, some false)]

example : gapColumns twoGaps = 2 := by decide
example : alignmentScore unitScore (-1) twoGaps = -2 := by decide
example : IsBanded 2 twoGaps := by unfold IsBanded; decide

example : IsBanded 2 twoGaps :=
  isBanded_of_neg_le_alignmentScore (σ := unitScore) (gap := -1)
    (by intro a b; unfold unitScore; split <;> norm_num) le_rfl (by decide)

example : nwScore unitScore (-1) [true, false, true] [false, true] = -1 := by decide

example : bandedScore unitScore (-1) 1 [true, false, true] [false, true] = some (-1) := by
  decide

example : bandedScore unitScore (-1) 1 [true, false, true] [false, true] =
    some (nwScore unitScore (-1) [true, false, true] [false, true]) :=
  bandedScore_eq_nwScore_of_neg_le (by intro a b; unfold unitScore; split <;> norm_num)
    le_rfl (by decide)

/-- Insert first, then match: leaves the diagonal before returning to it. -/
def detour : Alignment Bool := [(none, some false), (some true, some true)]

example : alignmentScore matchTwoScore (-1) detour = 1 := by decide
example : ¬ IsBanded 0 detour := by unfold IsBanded; decide

#print axioms bandedFrom_of_abs_add_gapColumns_le
#print axioms alignmentScore_le_neg_gapColumns
#print axioms isBanded_of_neg_le_alignmentScore
#print axioms bandedScore_eq_nwScore_of_neg_le

end Cslib.Algorithms.Lean
