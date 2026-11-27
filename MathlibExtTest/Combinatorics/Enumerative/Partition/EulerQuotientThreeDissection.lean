/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.PowerSeries.Inverse
import MathlibExt.Combinatorics.Enumerative.Partition.EulerQuotientThreeDissection

open MetaMathlibExt PowerSeries

local notation "𝔣" => qEulerProduct

-- Restoring the three unit denominators recovers the quotient form of the dissection.
example :
    𝔣 1 ^ 2 * invOfUnit (𝔣 2) 1 =
      𝔣 9 ^ 2 * invOfUnit (𝔣 18) 1 -
        2 * X * 𝔣 3 * 𝔣 18 ^ 2 * invOfUnit (𝔣 6 * 𝔣 9) 1 := by
  have cancel (F : ℤ⟦X⟧) (hF : constantCoeff F = 1) : invOfUnit F 1 * F = 1 :=
    invOfUnit_mul _ _ hF
  have h2 := cancel (𝔣 2) (constantCoeff_qEulerProduct (by decide))
  have h18 := cancel (𝔣 18) (constantCoeff_qEulerProduct (by decide))
  have h69 := cancel (𝔣 6 * 𝔣 9) (by simp (disch := decide) [constantCoeff_qEulerProduct])
  have unit (F : ℤ⟦X⟧) (hF : constantCoeff F = 1) : IsUnit F :=
    isUnit_iff_constantCoeff.mpr (hF ▸ isUnit_one)
  have hden := unit (𝔣 2 * 𝔣 18 * (𝔣 6 * 𝔣 9))
    (by simp (disch := decide) [constantCoeff_qEulerProduct])
  apply hden.mul_left_inj.mp
  linear_combination qEulerProduct_sq_div_three_dissection +
    𝔣 1 ^ 2 * 𝔣 18 * 𝔣 6 * 𝔣 9 * h2 - 𝔣 2 * 𝔣 6 * 𝔣 9 ^ 3 * h18 +
    2 * X * 𝔣 2 * 𝔣 3 * 𝔣 18 ^ 3 * h69

-- The two nonzero index classes contribute a total of -2 in degree one.
example : coeff 1 (𝔣 1 ^ 2 * 𝔣 6 * 𝔣 9 * 𝔣 18 - 𝔣 2 * 𝔣 6 * 𝔣 9 ^ 3) = -2 := by
  let F := -2 * 𝔣 2 * 𝔣 3 * 𝔣 18 ^ 3
  have h : 𝔣 1 ^ 2 * 𝔣 6 * 𝔣 9 * 𝔣 18 - 𝔣 2 * 𝔣 6 * 𝔣 9 ^ 3 = X ^ 1 * F := by
    rw [qEulerProduct_sq_div_three_dissection]
    dsimp [F]
    ring
  rw [h, coeff_X_pow_mul F 1 0, coeff_zero_eq_constantCoeff]
  simp (disch := decide) [F, constantCoeff_qEulerProduct, map_ofNat]
