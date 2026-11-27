/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EllipticCurveNaiveHeightSpecialCoeff

open MetaMathlibExt

-- A nonintegral point on the curve with equal coefficients.
example : ¬ Height.mulHeight ![(1 / 4 : ℚ), 31 / 8, 1] < (3 : ℝ) ^ ((1 : ℝ) / 3) := by
  convert (naiveHeight_lower_bound_of_special_coeff 12 12 (by decide)).1
    rfl (1 / 4) (31 / 8) (by norm_num) using 1
  norm_num

-- Both exceptional signs really occur below the strict bound.
example (u v : ℚ) (hP : v ^ 2 = u ^ 3 + 8 * u - 8) :
    Height.mulHeight ![u, v, 1] < (2 : ℝ) ^ ((1 : ℝ) / 3) ↔
      u = 1 ∧ (v = 1 ∨ v = -1) := by
  constructor
  · intro hs
    apply (naiveHeight_lower_bound_of_special_coeff 8 (-8) (by decide)).2.1 rfl u v
    · simpa [sub_eq_add_neg] using hP
    · norm_num
      exact hs
  · rintro ⟨rfl, hv⟩
    calc
      Height.mulHeight ![1, v, 1] = Height.mulHeight (![v, 1] ∘ ![1, 0, 1]) :=
        congrArg Height.mulHeight (List.ofFn_inj.mp rfl)
      _ ≤ Height.mulHeight ![v, 1] := Height.mulHeight_comp_le _ _
      _ = 1 := by
        rw [← Height.mulHeight₁_eq_mulHeight]
        rcases hv with rfl | rfl <;> simp [Height.mulHeight₁_neg]
      _ < _ := Real.one_lt_rpow (by norm_num) (by norm_num)

-- For zero constant term and negative linear coefficient, only the origin lies below the bound.
example (u v : ℚ) (hP : v ^ 2 = u ^ 3 - 8 * u) :
    Height.mulHeight ![u, v, 1] < (2 : ℝ) ^ ((1 : ℝ) / 3) ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro hs
    apply (naiveHeight_lower_bound_of_special_coeff (-8) 0 (by decide)).2.2.1 rfl u v
    · push_cast
      linarith only [hP]
    · norm_num
      exact hs
  · rintro ⟨rfl, rfl⟩
    rw [Height.mulHeight_cons_zero, Height.mulHeight_cons_zero,
      Height.mulHeight_eq_one_of_subsingleton]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)

-- A nonintegral point with zero linear coefficient.
example : ¬ Height.mulHeight ![(1 / 4 : ℚ), -33 / 8, 1] < (17 / 3 : ℝ) ^ ((1 : ℝ) / 3) := by
  simpa using (naiveHeight_lower_bound_of_special_coeff 0 17 (by decide)).2.2.2
    rfl (1 / 4) (-33 / 8) (by norm_num)
