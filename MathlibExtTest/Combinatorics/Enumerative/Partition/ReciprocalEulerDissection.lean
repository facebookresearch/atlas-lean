/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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
