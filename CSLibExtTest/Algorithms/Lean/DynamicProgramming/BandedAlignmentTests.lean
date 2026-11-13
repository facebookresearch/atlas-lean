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

example (σ : Bool → Bool → ℤ) (xs ys : List Bool) (A : Alignment Bool) (s : ℤ)
    (hA : IsAlignment A xs ys) (hb : IsBanded 2 A)
    (h : bandedScore σ (-1) 2 xs ys = some s) :
    alignmentScore σ (-1) A ≤ s :=
  alignmentScore_le_bandedScore σ (-1) 2 hA hb h

example (σ : Bool → Bool → ℤ) (xs ys : List Bool) (s : ℤ)
    (h : bandedScore σ (-1) 2 xs ys = some s) :
    ∃ A, IsAlignment A xs ys ∧ IsBanded 2 A ∧ alignmentScore σ (-1) A = s :=
  exists_banded_eq_bandedScore σ (-1) 2 h

/-- The diagonal alignment of `[true]` vs `[true, false]` is banded at width `1`, so its
score is at most the banded score `1`. -/
example : alignmentScore bandedTestScore (-1) (diagAlign [true] [true, false]) ≤ 1 :=
  alignmentScore_le_bandedScore bandedTestScore (-1) 1 (isAlignment_diagAlign _ _)
    (isBanded_diagAlign 1 (by decide)) (by decide)

/-- The banded score `1` of `[true]` vs `[true, false]` at width `1` is attained. -/
example : ∃ A, IsAlignment A [true] [true, false] ∧ IsBanded 1 A ∧
    alignmentScore bandedTestScore (-1) A = 1 :=
  exists_banded_eq_bandedScore bandedTestScore (-1) 1 (by decide)

-- Consumer checks require both validity and the band condition at any universe.
universe u

example {α : Type u} (σ : α → α → ℤ) (gap : ℤ) (w : ℕ)
    {xs ys : List α} {A : Alignment α} {s : ℤ}
    (hA : IsAlignment A xs ys) (hb : IsBanded w A)
    (hs : bandedScore σ gap w xs ys = some s) :
    alignmentScore σ gap A ≤ s :=
  alignmentScore_le_bandedScore σ gap w hA hb hs

example {α : Type u} (σ : α → α → ℤ) (gap : ℤ) (w : ℕ)
    {xs ys : List α} {s : ℤ} (hs : bandedScore σ gap w xs ys = some s) :
    ∃ A, IsAlignment A xs ys ∧ IsBanded w A ∧ alignmentScore σ gap A = s :=
  exists_banded_eq_bandedScore σ gap w hs

-- The optimum can be negative; attainment must not replace it by zero.
example : ∃ A, IsAlignment A [true, false] [false, true] ∧ IsBanded 0 A ∧
    alignmentScore bandedTestScore (-1) A = -2 :=
  exists_banded_eq_bandedScore bandedTestScore (-1) 0 (by decide)

-- Empty rows have an attained score even when the element type is empty.
example : bandedScore (fun (_ _ : Empty) => (0 : ℤ)) (-1) 0 [] [] = some 0 := by
  decide

example : ∃ A : Alignment Empty, IsAlignment A [] [] ∧ IsBanded 0 A ∧
    alignmentScore (fun _ _ => (0 : ℤ)) (-1) A = 0 :=
  exists_banded_eq_bandedScore (fun _ _ => (0 : ℤ)) (-1) 0 (by decide)

-- Equal endpoint lengths do not make every alignment banded at width zero.
example : IsAlignment [(some true, none), (none, some false)] [true] [false] := by
  simp [IsAlignment]

example : ¬ IsBanded 0 [(some true, none), (none, some false)] := by
  unfold IsBanded
  decide

example : alignmentScore bandedTestScore 1
    [(some true, none), (none, some false)] = 2 ∧
    bandedScore bandedTestScore 1 0 [true] [false] = some (-1) := by
  decide

#print axioms alignmentScore_le_bandedScore
#print axioms exists_banded_eq_bandedScore
#print axioms bandedScore_le_nwScore
#print axioms bandedScore_eq_nwScore_of_banded_optimal
#print axioms bandedScore_none_of_length_diff_gt
#print axioms bandedScore_some_of_length_diff_le

end Cslib.Algorithms.Lean
