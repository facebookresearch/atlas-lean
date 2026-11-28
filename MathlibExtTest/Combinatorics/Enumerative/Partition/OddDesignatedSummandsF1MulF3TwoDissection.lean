/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.PowerSeries.Inverse
import MathlibExt.Combinatorics.Enumerative.Partition.OddDesignatedSummandsF1MulF3TwoDissection

namespace MathlibExtTest.Combinatorics.Enumerative.Partition.OddDesignatedSummandsF1MulF3TwoDissection

open MetaMathlibExt PowerSeries

local notation "𝔣" => qEulerProduct

-- Restoring the two unit denominators recovers Hirschhorn's quotient form of the dissection.
example :
    𝔣 1 * 𝔣 3 =
      𝔣 2 * 𝔣 8 ^ 2 * 𝔣 12 ^ 4 * invOfUnit (𝔣 4 ^ 2 * 𝔣 6 * 𝔣 24 ^ 2) 1 -
        X * 𝔣 4 ^ 4 * 𝔣 6 * 𝔣 24 ^ 2 * invOfUnit (𝔣 2 * 𝔣 8 ^ 2 * 𝔣 12 ^ 2) 1 := by
  have cancel (F : ℤ⟦X⟧) (hF : constantCoeff F = 1) : invOfUnit F 1 * F = 1 :=
    invOfUnit_mul _ _ hF
  have hD1 := cancel (𝔣 4 ^ 2 * 𝔣 6 * 𝔣 24 ^ 2)
    (by simp (disch := decide) [constantCoeff_qEulerProduct])
  have hD2 := cancel (𝔣 2 * 𝔣 8 ^ 2 * 𝔣 12 ^ 2)
    (by simp (disch := decide) [constantCoeff_qEulerProduct])
  have unit (F : ℤ⟦X⟧) (hF : constantCoeff F = 1) : IsUnit F :=
    isUnit_iff_constantCoeff.mpr (hF ▸ isUnit_one)
  have hden := unit ((𝔣 4 ^ 2 * 𝔣 6 * 𝔣 24 ^ 2) * (𝔣 2 * 𝔣 8 ^ 2 * 𝔣 12 ^ 2))
    (by simp (disch := decide) [constantCoeff_qEulerProduct])
  apply hden.mul_left_inj.mp
  linear_combination f1_mul_f3_two_dissection -
    (𝔣 2 * 𝔣 8 ^ 2 * 𝔣 12 ^ 4) * (𝔣 2 * 𝔣 8 ^ 2 * 𝔣 12 ^ 2) * hD1 +
    X * (𝔣 4 ^ 4 * 𝔣 6 * 𝔣 24 ^ 2) * (𝔣 4 ^ 2 * 𝔣 6 * 𝔣 24 ^ 2) * hD2

-- The even part has no linear term, so the difference has degree-one coefficient -1.
example : coeff 1 (𝔣 1 * 𝔣 3 * 𝔣 2 * 𝔣 4 ^ 2 * 𝔣 6 * 𝔣 8 ^ 2 * 𝔣 12 ^ 2 * 𝔣 24 ^ 2 -
    𝔣 2 ^ 2 * 𝔣 8 ^ 4 * 𝔣 12 ^ 6) = -1 := by
  let F := -(𝔣 4 ^ 6 * 𝔣 6 ^ 2 * 𝔣 24 ^ 4)
  have h : 𝔣 1 * 𝔣 3 * 𝔣 2 * 𝔣 4 ^ 2 * 𝔣 6 * 𝔣 8 ^ 2 * 𝔣 12 ^ 2 * 𝔣 24 ^ 2 -
      𝔣 2 ^ 2 * 𝔣 8 ^ 4 * 𝔣 12 ^ 6 = X ^ 1 * F := by
    rw [f1_mul_f3_two_dissection]
    dsimp [F]
    ring
  rw [h, coeff_X_pow_mul F 1 0, coeff_zero_eq_constantCoeff]
  simp (disch := decide) [F, constantCoeff_qEulerProduct]

end MathlibExtTest.Combinatorics.Enumerative.Partition.OddDesignatedSummandsF1MulF3TwoDissection
