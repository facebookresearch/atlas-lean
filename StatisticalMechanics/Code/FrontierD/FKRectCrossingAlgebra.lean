/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib



namespace StatMech.FrontierD




theorem crossing_vertical_ge_one_div_eight_mul_pow_six
    {q H V : Real} (hq : 1 ≤ q) (hV : 0 ≤ V)
    (hsum : 1 ≤ V + q ^ 2 * H)
    (hquadratic : H ^ 2 / (1 + q ^ 2) ≤ V) :
    1 / (8 * q ^ 6) ≤ V := by
  let Q : Real := q ^ 2
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    nlinarith
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hden : 0 < 1 + Q := by linarith
  have hquad : H ^ 2 ≤ V * (1 + Q) := by
    rw [div_le_iff₀ hden] at hquadratic
    simpa [Q, mul_comm] using hquadratic
  rw [show q ^ 6 = Q ^ 3 by simp [Q, ← pow_mul]]
  have hQ3 : 1 ≤ Q ^ 3 := one_le_pow₀ hQ
  have hden8 : 0 < 8 * Q ^ 3 := by positivity
  rw [div_le_iff₀ hden8]
  by_contra h
  rw [not_le] at h
  have hVsmall : 8 * V < 1 := by
    have hmul : V ≤ Q ^ 3 * V := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hQ3 hV
    nlinarith
  have hQH : (7 : Real) / 8 < Q * H := by
    have hsumQ : 1 ≤ V + Q * H := by simpa [Q] using hsum
    nlinarith
  have hQHsq : (49 : Real) / 64 < (Q * H) ^ 2 := by
    nlinarith [sq_nonneg (Q * H - 7 / 8)]
  have hleft : (Q * H) ^ 2 ≤ Q ^ 2 * (V * (1 + Q)) := by
    calc
      (Q * H) ^ 2 = Q ^ 2 * H ^ 2 := by ring
      _ ≤ Q ^ 2 * (V * (1 + Q)) :=
        mul_le_mul_of_nonneg_left hquad (sq_nonneg Q)
  have hQ2Q3 : Q ^ 2 ≤ Q ^ 3 := by
    calc
      Q ^ 2 ≤ Q ^ 2 * Q :=
        by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hQ (sq_nonneg Q)
      _ = Q ^ 3 := by ring
  have hright : Q ^ 2 * (V * (1 + Q)) ≤ 2 * (Q ^ 3 * V) := by
    calc
      Q ^ 2 * (V * (1 + Q)) =
          V * Q ^ 2 + V * Q ^ 3 := by ring
      _ ≤ V * Q ^ 3 + V * Q ^ 3 := by
        gcongr
      _ = 2 * (Q ^ 3 * V) := by ring
  have hupper : 2 * (Q ^ 3 * V) < 1 / 4 := by
    nlinarith
  linarith





theorem crossing_hard_ge_one_div_eight_mul_pow_two
    {q hard easy : Real} (hq : 1 ≤ q) (hhard : 0 ≤ hard)
    (hsum : 1 ≤ easy + q ^ 2 * hard)
    (hquadratic : easy ^ 2 / (1 + q ^ 2) ≤ hard) :
    1 / (8 * q ^ 2) ≤ hard := by
  let Q : Real := q ^ 2
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    nlinarith
  have hden : 0 < 1 + Q := by linarith
  have hquad : easy ^ 2 ≤ hard * (1 + Q) := by
    rw [div_le_iff₀ hden] at hquadratic
    simpa [Q] using hquadratic
  rw [show q ^ 2 = Q by rfl]
  have hden8 : 0 < 8 * Q := by positivity
  rw [div_le_iff₀ hden8]
  by_contra hsmall
  rw [not_le] at hsmall
  have hQhard : Q * hard < 1 / 8 := by nlinarith
  have heasy : 7 / 8 < easy := by
    have hsum' : 1 ≤ easy + Q * hard := by simpa [Q] using hsum
    nlinarith
  have heasySq : 49 / 64 < easy ^ 2 := by
    nlinarith [sq_nonneg (easy - 7 / 8)]
  have hcoeff : 1 + Q ≤ 2 * Q := by linarith
  have hupper : hard * (1 + Q) ≤ hard * (2 * Q) :=
    mul_le_mul_of_nonneg_left hcoeff hhard
  nlinarith




theorem crossing_hard_ge_of_square_seed_and_sixth_power
    {q square hard : Real} (hq : 1 ≤ q)
    (hseed : 1 / (1 + q) ≤ square)
    (hrsw : square ^ 6 / (16 * (1 + q)) ≤ hard) :
    1 / (16 * (1 + q) ^ 7) ≤ hard := by
  have hden : 0 < 1 + q := by linarith
  have hbase : 0 ≤ 1 / (1 + q) := by positivity
  have hsquare : 0 ≤ square := hbase.trans hseed
  calc
    1 / (16 * (1 + q) ^ 7) =
        (1 / (1 + q)) ^ 6 / (16 * (1 + q)) := by
          field_simp
    _ ≤ square ^ 6 / (16 * (1 + q)) := by
      gcongr
    _ ≤ hard := hrsw





theorem crossing_hard_ge_of_square_seed_and_sixth_power_qsq
    {q square hard : Real} (hq : 1 ≤ q)
    (hseed : 1 / (1 + q) ≤ square)
    (hrsw : square ^ 6 / (16 * (1 + q ^ 2)) ≤ hard) :
    (1 / (1 + q)) ^ 6 / (16 * (1 + q ^ 2)) ≤ hard := by
  have hbase : 0 ≤ 1 / (1 + q) := by positivity
  have hden : 0 ≤ 16 * (1 + q ^ 2) := by positivity
  calc
    (1 / (1 + q)) ^ 6 / (16 * (1 + q ^ 2)) ≤
        square ^ 6 / (16 * (1 + q ^ 2)) := by
      gcongr
    _ ≤ hard := hrsw

end StatMech.FrontierD
