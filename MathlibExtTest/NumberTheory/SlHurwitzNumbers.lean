/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SlHurwitzNumbers

open MetaMathlibExt PowerSeries

variable (S C : PowerSeries ℚ)
    (hS : derivative S = C ^ 2) (hC : derivative C = -(S ^ 2))
    (hS0 : constantCoeff S = 0) (hC0 : constantCoeff C = 1)

-- At the first prime congruent to 7, the ordinary coefficient has degree 4.
example : ¬ 7 ∣ (coeff 4 S).den :=
  (sl_hurwitz_numbers_den_coprime S C hS hC hS0 hC0 7 (by decide)).1 rfl

-- At the first prime congruent to 4, the Laurent coefficient of degree 8
-- is the ordinary coefficient of degree 9 in the inverse of the unit factor.
example (T : PowerSeries ℚ) (hT : S = X * T) : ¬ 13 ∣ (coeff 9 T⁻¹).den := by
  have hshift : (PowerSeries.mk fun n => coeff (n + 1) S) = T := by
    ext n
    simp [hT]
  have h := (sl_hurwitz_numbers_den_coprime S C hS hC hS0 hC0 13 (by decide)).2 rfl
  rwa [hshift] at h

-- The first nonlinear coefficient of Sl has reduced denominator dividing 4!.
example : (coeff 4 S).den ∣ 24 := by
  obtain ⟨z, hz⟩ := factorial_mul_coeff_sl_isInt S C hS hC hS0 hC0 1
  change 24 * coeff 4 S = z at hz
  have h : coeff 4 S = Rat.divInt z 24 := by
    rw [Rat.divInt_eq_div, eq_div_iff (by norm_num)]
    simpa [mul_comm] using hz
  rw [h]
  exact_mod_cast Rat.den_dvd z 24
