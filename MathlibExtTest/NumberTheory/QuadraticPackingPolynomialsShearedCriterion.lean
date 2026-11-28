/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticPackingPolynomialsShearedCriterion
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt.ShearedCriterionTest

/-- The sheared criterion's set condition holds for `m = n = k = 1` and `F = 0`:
the only staircase index below `1` is `0`, the first height there is `0`, and the
sheared polynomial takes the value `0` there. -/
private theorem setEq_one_one :
    let l : ℝ := Nat.gcd (1 - 1) 1
    let Phat : ℝ → ℝ → ℝ := fun x y => ((1 : ℕ) : ℝ) / 2 * x *
      (x - ((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) / l)) + x +
      ((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) / l) * y + 0
    (fun i : ℕ => Phat (i / (((1 : ℕ) : ℝ) / l)) (staircaseFirstHeight 1 1 i)) '' Set.Iio 1 =
      ((↑) : ℕ → ℝ) '' Set.Iio 1 := by
  dsimp only
  ext y
  simp only [Set.mem_image, Set.mem_Iio]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Nat.lt_one_iff.mp hi]
    exact ⟨0, by simp [staircaseFirstHeight_zero]⟩
  · rintro ⟨N, hN, rfl⟩
    rw [Nat.lt_one_iff.mp hN]
    refine ⟨0, by norm_num, ?_⟩
    simp [staircaseFirstHeight_zero]

/-- The slope-`1` instance of the sheared criterion: the sheared polynomial for
`m = n = k = 1` and `F = 0` is a quadratic packing polynomial on the sheared
sector, by the reverse direction of the criterion and the set condition above. -/
private theorem qpp_one_one : IsQuadraticPackingPolynomial
    ((fun p : ℝ × ℝ => (p.1 - (((1 : ℕ) : ℝ) - 1) / ((1 : ℕ) : ℝ) * p.2, p.2)) ''
      sectorLatticePoints (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)))
    (fun x y => ((1 : ℕ) : ℝ) / 2 * x *
      (x - ((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) / ((Nat.gcd (1 - 1) 1 : ℕ) : ℝ))) + x +
      ((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) / ((Nat.gcd (1 - 1) 1 : ℕ) : ℝ)) * y + 0) :=
  (isQuadraticPackingPolynomial_sheared_iff (m := 1) (n := 1) (k := 1) (F := 0)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by decide)).mpr setEq_one_one

/-- The forward direction of the criterion at the slope-`1` instance: the packing
polynomial above takes the values `0` at the first step of the zeroth staircase,
recovering the set condition. -/
example :
    let l : ℝ := Nat.gcd (1 - 1) 1
    let Phat : ℝ → ℝ → ℝ := fun x y => ((1 : ℕ) : ℝ) / 2 * x *
      (x - ((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) / l)) + x +
      ((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) / l) * y + 0
    (fun i : ℕ => Phat (i / (((1 : ℕ) : ℝ) / l)) (staircaseFirstHeight 1 1 i)) '' Set.Iio 1 =
      ((↑) : ℕ → ℝ) '' Set.Iio 1 :=
  (isQuadraticPackingPolynomial_sheared_iff (m := 1) (n := 1) (k := 1) (F := 0)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by decide)).mp qpp_one_one

private noncomputable def slopeTwelveSevenths (x y : ℝ) : ℝ :=
  6 * (x - y / 2) * (x - y / 2 - 3 / 2) + x + y + 2

-- Check the published example's constant and its step difference by direct evaluation.
example : slopeTwelveSevenths 0 0 = 2 ∧ slopeTwelveSevenths 1 2 - slopeTwelveSevenths 0 0 = 3 ∧
    ((Nat.gcd (7 - 1) 12 : ℝ) ^ 2 / 12) * (3 - 1) * (3 + 1) / 12 = 2 := by
  norm_num [slopeTwelveSevenths, show Nat.gcd (7 - 1) 12 = 6 by decide]

-- Test the shear convention on the original point (1, 2), which shears to (0, 2).
example : slopeTwelveSevenths (0 + (1 / 2) * 2) 2 = 6 * 0 * (0 - 3 / 2) + 0 + 3 / 2 * 2 + 2 := by
  norm_num [slopeTwelveSevenths]

example : slopeTwelveSevenths 0 0 = 2 := by
  have h : IsQuadraticPackingPolynomial (sectorLatticePoints (((12 : ℕ) : ℝ) / (7 : ℕ)))
      slopeTwelveSevenths := by
    apply (isQuadraticPackingPolynomial_shear_iff (1 / 2)).mp
    norm_num only [Nat.cast_ofNat]
    convert isQuadraticPackingPolynomial_sheared_example_twelve_sevenths using 1
    funext x y
    dsimp only [slopeTwelveSevenths]
    ring
  have hF := quadraticPackingPolynomial_constant_term (m := 7) (n := 12) (k := 3)
    (by decide) (by decide) (by decide) h (by decide)
    consecutiveStepDifference_example_twelve_sevenths
  norm_num [show Nat.gcd (7 - 1) 12 = 6 by decide] at hF
  exact hF

private noncomputable def slopeOne (x y : ℝ) : ℝ := 1 / 2 * x * (x - 1) + x + y

-- Check the k = 1 and n / l = 1 boundary independently as well.
example : slopeOne 0 0 = 0 ∧ slopeOne 0 1 - slopeOne 0 0 = 1 ∧
    ((Nat.gcd (1 - 1) 1 : ℝ) ^ 2 / 1) * (1 - 1) * (1 + 1) / 12 = 0 := by
  norm_num [slopeOne]

example : slopeOne 0 0 = 0 := by
  have h : IsQuadraticPackingPolynomial (sectorLatticePoints (((1 : ℕ) : ℝ) / (1 : ℕ)))
      slopeOne := by
    apply (isQuadraticPackingPolynomial_shear_iff 0).mp
    have hq := qpp_one_one
    norm_num [slopeOne] at hq ⊢
    exact hq
  have hk : consecutiveStepDifference 1 1 slopeOne = ((1 : ℕ) : ℝ) := by
    have hD := consecutiveStepDifference_of_sheared_form (m := 1) (n := 1) (by decide)
      (P := slopeOne) (f := fun x => 1 / 2 * x * (x - 1) + x) (c := 1)
      (by intro x y; norm_num [slopeOne])
    simpa using hD
  simpa using quadraticPackingPolynomial_constant_term (m := 1) (n := 1) (k := 1)
    (by decide) (by decide) (by decide) h (by decide) hk

end MetaMathlibExt.ShearedCriterionTest
