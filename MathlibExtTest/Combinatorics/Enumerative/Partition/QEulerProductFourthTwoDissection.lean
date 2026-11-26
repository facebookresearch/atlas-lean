/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProductFourthTwoDissection

open MetaMathlibExt PowerSeries

local notation "𝔣" => qEulerProduct

-- The difference between the two sides of the dissection starts with 4X.
example : coeff 1 (𝔣 4 ^ 12 - 𝔣 1 ^ 4 * 𝔣 2 ^ 2 * 𝔣 4 ^ 2 * 𝔣 8 ^ 4) = 4 := by
  let F := 4 * 𝔣 2 ^ 4 * 𝔣 8 ^ 8
  have h : 𝔣 4 ^ 12 - 𝔣 1 ^ 4 * 𝔣 2 ^ 2 * 𝔣 4 ^ 2 * 𝔣 8 ^ 4 = X ^ 1 * F := by
    rw [qEulerProduct_fourth_two_dissection]
    dsimp [F]
    ring
  rw [h, coeff_X_pow_mul F 1 0, coeff_zero_eq_constantCoeff]
  simp (disch := decide) [F, constantCoeff_qEulerProduct, map_ofNat]

-- Every coefficient of the difference is divisible by four.
example (n : ℕ) : (4 : ℤ) ∣
    coeff n (𝔣 4 ^ 12 - 𝔣 1 ^ 4 * 𝔣 2 ^ 2 * 𝔣 4 ^ 2 * 𝔣 8 ^ 4) := by
  let F := X * 𝔣 2 ^ 4 * 𝔣 8 ^ 8
  use coeff n F
  rw [qEulerProduct_fourth_two_dissection, ← coeff_ofNat_mul]
  congr 1
  dsimp [F]
  ring
