/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.IsSquare
import MathlibExt.Combinatorics.Enumerative.Partition.ReciprocalEulerDissection

open MetaMathlibExt PowerSeries

local notation "𝔣" => qEulerProduct

-- The shifted term of the fourth-power identity starts with 4X.
example : coeff 1 (𝔣 2 ^ 14 * 𝔣 8 ^ 4 - 𝔣 1 ^ 4 * 𝔣 4 ^ 14) = 4 := by
  let F := 4 * 𝔣 1 ^ 4 * 𝔣 2 ^ 4 * 𝔣 4 ^ 2 * 𝔣 8 ^ 8
  have h : 𝔣 2 ^ 14 * 𝔣 8 ^ 4 - 𝔣 1 ^ 4 * 𝔣 4 ^ 14 = X ^ 1 * F := by
    rw [one_div_f1_pow_four_eight_twelve_two_dissection.1]
    dsimp [F]
    ring
  rw [h, coeff_X_pow_mul F 1 0, coeff_zero_eq_constantCoeff]
  simp (disch := decide) [F, constantCoeff_qEulerProduct, map_ofNat]

-- All coefficients of the eighth-power difference are divisible by eight.
example (n : ℕ) : (8 : ℤ) ∣ coeff n (𝔣 2 ^ 28 * 𝔣 8 ^ 8 - 𝔣 1 ^ 8 * 𝔣 4 ^ 28) := by
  let F := X * 𝔣 1 ^ 8 * 𝔣 2 ^ 4 * 𝔣 4 ^ 16 * 𝔣 8 ^ 8 +
    2 * X ^ 2 * 𝔣 1 ^ 8 * 𝔣 2 ^ 8 * 𝔣 4 ^ 4 * 𝔣 8 ^ 16
  use coeff n F
  rw [one_div_f1_pow_four_eight_twelve_two_dissection.2.1, ← coeff_ofNat_mul]
  congr 1
  dsimp [F]
  ring

-- After removing the terms of shifts zero, one and two, the cube starts with 64X³.
example : coeff 3 (𝔣 2 ^ 42 * 𝔣 8 ^ 12 -
    (𝔣 1 ^ 12 * 𝔣 4 ^ 42 + 12 * X * 𝔣 1 ^ 12 * 𝔣 2 ^ 4 * 𝔣 4 ^ 30 * 𝔣 8 ^ 8 +
      48 * X ^ 2 * 𝔣 1 ^ 12 * 𝔣 2 ^ 8 * 𝔣 4 ^ 18 * 𝔣 8 ^ 16)) = 64 := by
  let F := 64 * 𝔣 1 ^ 12 * 𝔣 2 ^ 12 * 𝔣 4 ^ 6 * 𝔣 8 ^ 24
  rw [one_div_f1_pow_four_eight_twelve_two_dissection.2.2, add_sub_cancel_left]
  have h : 64 * X ^ 3 * 𝔣 1 ^ 12 * 𝔣 2 ^ 12 * 𝔣 4 ^ 6 * 𝔣 8 ^ 24 = X ^ 3 * F := by
    dsimp [F]
    ring
  rw [h, coeff_X_pow_mul F 3 0, coeff_zero_eq_constantCoeff]
  simp (disch := decide) [F, constantCoeff_qEulerProduct, map_ofNat]

section ReciprocalSquare

private lemma pentagonal_constant : constantCoeff (pentagonalSeries ℤ) = 1 := by
  rw [← qEulerProduct_one]
  exact constantCoeff_qEulerProduct (le_refl 1)

private lemma pentagonal_coeff_one : coeff 1 (pentagonalSeries ℤ) = -1 := by
  rw [show 1 = pentagonal 1 by norm_num [pentagonal_def], coeff_pentagonalSeries_pentagonal,
    Int.negOnePow_one]
  rfl

private lemma pentagonal_coeff_two : coeff 2 (pentagonalSeries ℤ) = -1 := by
  rw [show 2 = pentagonal (-1) by norm_num [pentagonal_def], coeff_pentagonalSeries_pentagonal,
    Int.negOnePow_neg, Int.negOnePow_one]
  rfl

private lemma pentagonal_coeff_three : coeff 3 (pentagonalSeries ℤ) = 0 := by
  apply coeff_pentagonalSeries_eq_zero
  rintro ⟨j, hj⟩
  have h := two_mul_natCast_pentagonal j
  rw [hj] at h
  norm_num at h
  exact (show ¬ IsSquare (73 : ℤ) by norm_num) ⟨6 * j - 1, by nlinarith only [h]⟩

private lemma coeff_two_mul (F G : ℤ⟦X⟧) :
    coeff 2 (F * G) = constantCoeff F * coeff 2 G + coeff 1 F * coeff 1 G +
      coeff 2 F * constantCoeff G := by
  norm_num [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_zero_eq_constantCoeff]

private lemma coeff_three_mul (F G : ℤ⟦X⟧) :
    coeff 3 (F * G) = constantCoeff F * coeff 3 G + coeff 1 F * coeff 2 G +
      coeff 2 F * coeff 1 G + coeff 3 F * constantCoeff G := by
  norm_num [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_zero_eq_constantCoeff]

-- Compute both sides independently: a nonzero even coefficient and a cancelled odd coefficient.
example :
    coeff 2 (𝔣 2 ^ 5 * 𝔣 8 * 𝔣 16 ^ 2) = -5 ∧
    coeff 2 (𝔣 1 ^ 2 * 𝔣 8 ^ 6 + 2 * X * 𝔣 1 ^ 2 * 𝔣 4 ^ 2 * 𝔣 16 ^ 4) = -5 ∧
    coeff 3 (𝔣 2 ^ 5 * 𝔣 8 * 𝔣 16 ^ 2) = 0 ∧
    coeff 3 (𝔣 1 ^ 2 * 𝔣 8 ^ 6 + 2 * X * 𝔣 1 ^ 2 * 𝔣 4 ^ 2 * 𝔣 16 ^ 4) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [pow_succ, coeff_three_mul, coeff_two_mul, coeff_one_mul, coeff_X,
      qEulerProduct_eq_expand, coeff_expand, pentagonal_constant,
      pentagonal_coeff_one, pentagonal_coeff_two, pentagonal_coeff_three]

-- The first Euler product is also an independent check of the general substitution formula.
example : 𝔣 1 = expand 1 one_ne_zero (pentagonalSeries ℤ) := by
  rw [expand_one_apply, qEulerProduct_one]

-- Client check: the theorem gives equality in degree eight without convolution.
example : coeff 8 (𝔣 2 ^ 5 * 𝔣 8 * 𝔣 16 ^ 2) =
    coeff 8 (𝔣 1 ^ 2 * 𝔣 8 ^ 6 + 2 * X * 𝔣 1 ^ 2 * 𝔣 4 ^ 2 * 𝔣 16 ^ 4) :=
  congrArg (coeff 8) one_div_f1_sq_two_dissection

end ReciprocalSquare
