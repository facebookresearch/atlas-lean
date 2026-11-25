/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticPackingPolynomialsShearedCriterion
import Mathlib.Tactic.NormNum

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

end MetaMathlibExt.ShearedCriterionTest
