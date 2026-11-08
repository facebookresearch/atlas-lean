/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SemiGlobalAlignment
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.SemiGlobalAlignment

/-!
# Semi-global and overlap alignment tests

Closed checks with match `2`, mismatch `-1`, gap `-1`: the overlap score of
`[true]` against `[false]` is `0` (the empty pair), the fitting score of
`[true]` against `[false, true]` is `2` (the `[true]` infix), and the
theorems instantiate. Axiom audit follows.
-/

namespace Cslib.Algorithms.Lean

/-- Match `2`, mismatch `-1` scoring, used by the tests below. -/
def semiglobalTestScore : Bool → Bool → ℤ := fun a b => if a = b then 2 else -1

example : overlapScore semiglobalTestScore (-1) [true] [false] = 0 := by decide

example : fittingScore semiglobalTestScore (-1) [true] [false, true] = 2 := by decide

/-- Negative optima are not floored at `0`: the only fitting alignments of
`[true]` against `[false]` or `[]` score `-1`. -/
example : fittingScore semiglobalTestScore (-1) [true] [false] = -1 := by decide

example : fittingScore semiglobalTestScore (-1) [true] [] = -1 := by decide

/-- With empty `xs`, the empty infix attains `0`. -/
example : fittingScore semiglobalTestScore (-1) [] [false, true] = 0 := by decide

example : overlapScore semiglobalTestScore (-1) [true, false] [false, true] = 2 := by decide

example (σ : Bool → Bool → ℤ) (xs ys : List Bool) :
    overlapScore σ (-1) xs ys ≤ localScore σ (-1) xs ys :=
  overlapScore_le_localScore σ (-1) xs ys

example (σ : Bool → Bool → ℤ) (xs ys : List Bool) :
    fittingScore σ (-1) xs ys ≤ localScore σ (-1) xs ys :=
  fittingScore_le_localScore σ (-1) xs ys

example (σ : Bool → Bool → ℤ) (xs ys : List Bool) :
    ∃ p ∈ overlapPairs xs ys,
      nwScore σ (-1) p.1 p.2 = overlapScore σ (-1) xs ys :=
  exists_nwScore_eq_overlapScore σ (-1) xs ys

example (σ : Bool → Bool → ℤ) (xs ys : List Bool) :
    ∃ l ∈ infixes ys, nwScore σ (-1) xs l = fittingScore σ (-1) xs ys :=
  exists_nwScore_eq_fittingScore σ (-1) xs ys

#print axioms overlapScore_le_localScore
#print axioms fittingScore_le_localScore
#print axioms exists_nwScore_eq_overlapScore
#print axioms exists_nwScore_eq_fittingScore

end Cslib.Algorithms.Lean
