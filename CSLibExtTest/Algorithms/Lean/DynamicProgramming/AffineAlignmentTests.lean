/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.AffineAlignment
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.AffineAlignment

/-!
# Affine-gap alignment tests

Closed checks on the Gotoh algorithm with match `2`, mismatch `-1`, gap open `-2`,
gap extend `-1`: an affine-scored alignment is evaluated by hand, the DP values on
small inputs are computed by `decide`, the linear-gap bridge is checked on an
example, and the theorems instantiate. Axiom audit follows.
-/

namespace Cslib.Algorithms.Lean

/-- Match `2`, mismatch `-1` scoring, used by the tests below. -/
def affineTestScore : Bool → Bool → ℤ := fun a b => if a = b then 2 else -1

-- Hand-evaluated: match `2`, an X-gap run of length 2 (`-2 + -1`), a Y-gap run
-- of length 1 (`-2`): total `2 - 3 - 2 = -3`.
example : affineScore affineTestScore (-2) (-1)
    [(some true, some true), (some false, none), (some false, none),
      (none, some true)] = -3 := by decide

example : gotohScore affineTestScore (-2) (-1) [true] [true] = 2 := by decide

example : gotohScore affineTestScore (-2) (-1) [true, false] [true, true] = 1 := by decide

-- A single gap run of length 2 costs `gapOpen + gapExtend = -3`. These are
-- continuation values: the `none` continuation of `[]` against `[true, true]`
-- is a pure gap run, even though it ends in a gap, not a match.
example : gotohContNone affineTestScore (-2) (-1) [] [true, true] = -3 := by decide

example : gotohContNone affineTestScore (-2) (-1) [true, true] [] = -3 := by decide

/-- The `none` continuation of `[a]` against `[]` is a gap: the next column may
be a gap even when the previous column was a match. -/
example : gotohContNone affineTestScore (-2) (-1) [true] [] = -2 := by decide

-- Linear-gap bridge: with `gapOpen = gapExtend = -1`, Gotoh is Needleman–Wunsch.
example : gotohScore affineTestScore (-1) (-1) [true, false] [true, true]
    = nwScore affineTestScore (-1) [true, false] [true, true] := by decide

example (σ : Bool → Bool → ℤ) (xs ys : List Bool) (A : Alignment Bool)
    (hA : IsAlignment A xs ys) :
    affineScore σ (-2) (-1) A ≤ gotohScore σ (-2) (-1) xs ys :=
  affineScore_le_gotohScore σ (-2) (-1) A xs ys hA

example (σ : Bool → Bool → ℤ) (xs ys : List Bool) :
    ∃ A, IsAlignment A xs ys ∧
      affineScore σ (-2) (-1) A = gotohScore σ (-2) (-1) xs ys :=
  exists_affineScore_eq_gotohScore σ (-2) (-1) xs ys

example (xs ys : List Bool) :
    gotohScore affineTestScore (-1) (-1) xs ys = nwScore affineTestScore (-1) xs ys :=
  gotohScore_eq_nwScore affineTestScore (-1) (-1) (-1) rfl rfl xs ys

#print axioms affineScore_le_gotohScore
#print axioms exists_affineScore_eq_gotohScore
#print axioms gotohScore_eq_nwScore
#print axioms gotohContNone_eq

end Cslib.Algorithms.Lean
