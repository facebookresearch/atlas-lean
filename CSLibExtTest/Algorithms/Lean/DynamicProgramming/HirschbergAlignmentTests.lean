/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.HirschbergAlignment
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.HirschbergAlignment

/-!
# Hirschberg reconstruction tests

Closed checks with match `2`, mismatch `-1`, gap `-1`: the reconstruction
recovers the optimal alignments for `[true, false]` vs `[true, true]` (score
`1`) and `[true]` vs `[true, false]` (score `1`). Axiom audit follows.
-/

namespace Cslib.Algorithms.Lean

/-- Match `2`, mismatch `-1` scoring, used by the tests below. -/
def hirschbergTestScore : Bool → Bool → ℤ := fun a b => if a = b then 2 else -1

example : hirschberg hirschbergTestScore (-1) [true, false] [true, true]
    = [(some true, some true), (some false, some true)] := by decide

example : hirschberg hirschbergTestScore (-1) [true] [true, false]
    = [(some true, some true), (none, some false)] := by decide

example : alignmentScore hirschbergTestScore (-1)
    (hirschberg hirschbergTestScore (-1) [true, false] [true, true]) = 1 := by
  decide

example (σ : Bool → Bool → ℤ) (xs ys : List Bool) :
    IsAlignment (hirschberg σ (-1) xs ys) xs ys :=
  isAlignment_hirschberg σ (-1) xs ys

example (σ : Bool → Bool → ℤ) (xs ys : List Bool) :
    alignmentScore σ (-1) (hirschberg σ (-1) xs ys) = nwScore σ (-1) xs ys :=
  alignmentScore_hirschberg σ (-1) xs ys

example :
    nwScore hirschbergTestScore (-1) (List.take 1 [true, false])
        (List.take 1 [true, true]) +
      nwScore hirschbergTestScore (-1) (List.drop 1 [true, false])
        (List.drop 1 [true, true]) ≤
      nwScore hirschbergTestScore (-1) [true, false] [true, true] :=
  splitScore_le_nwScore_ys hirschbergTestScore (-1) [true, false] [true, true]

#print axioms isAlignment_hirschberg
#print axioms alignmentScore_hirschberg
#print axioms nwScore_eq_bestSplit_ys
#print axioms nwScore_eq_bestSplit_xs

end Cslib.Algorithms.Lean
