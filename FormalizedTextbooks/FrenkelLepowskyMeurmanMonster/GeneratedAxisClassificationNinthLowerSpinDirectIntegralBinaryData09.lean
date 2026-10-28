/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorInputData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! Exact integral basis coordinates for one complete Ninth lower spatial matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- All twenty-four genuine lattice basis columns in their integral source coordinates. -/
def generatedNinthLowerSpinDirectIntegralMatrix09 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-5, -8, -7, -1, 3, -4, 8, 1, -8, -7, 8, -11,
      3, -8, 8, 8, -16, -11, -2, 2, -9, -3, 8, -9],
    ![1, 2, 1, 0, 0, 1, -2, 0, 2, 1, -2, 2,
      -1, 2, -2, -2, 3, 2, 1, -1, 2, 0, -2, 2],
    ![0, 1, 0, 0, -1, 0, -2, -1, 1, 1, -2, 2,
      -1, 1, -2, -2, 2, 2, 0, -1, 1, 0, -2, 1],
    ![2, 2, 2, 1, 0, 1, -1, 0, 2, 2, -1, 3,
      0, 2, -1, -1, 4, 2, 1, 0, 2, 1, -1, 3],
    ![0, 1, 1, 0, -1, 0, -3, -1, 1, 1, -2, 2,
      -1, 1, -2, -2, 3, 2, 0, 0, 2, 0, -2, 1],
    ![1, 2, 2, 0, 0, 1, -1, 1, 2, 2, -1, 3,
      0, 3, 0, 0, 3, 3, 1, 1, 3, 2, 0, 3],
    ![1, 2, 1, 0, -1, 1, -1, 0, 1, 2, -2, 2,
      0, 2, -2, -1, 4, 3, 0, 0, 2, 2, -1, 2],
    ![0, -1, 0, 0, 0, 0, 1, 0, 0, -1, 1, -1,
      0, -1, 1, 0, -1, -1, 0, 0, -1, -1, 0, -1],
    ![2, 2, 2, 1, 0, 1, -1, 0, 2, 2, 0, 3,
      -1, 1, -1, -1, 3, 2, 1, 0, 1, 0, -2, 2],
    ![2, 2, 2, 0, 0, 1, -1, 0, 2, 2, -1, 2,
      0, 2, -1, -2, 3, 1, 0, -1, 1, 1, -2, 2],
    ![1, 1, 2, 0, -1, 1, -1, 0, 1, 1, -1, 2,
      0, 1, -1, -1, 3, 2, 0, 0, 1, 1, -1, 2],
    ![-1, -1, -1, 0, 0, 0, 0, 0, -1, 0, 0, -1,
      0, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, -1],
    ![0, 1, 1, 0, -1, 0, -2, 0, 1, 1, -2, 2,
      -1, 1, -2, -2, 2, 2, 0, 0, 2, 0, -2, 1],
    ![-1, -1, -1, 0, -1, 0, 1, 0, -1, -1, 0, -1,
      0, -1, 0, 1, -1, 0, 0, 0, -1, 0, 1, -1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, -1, 0, -1,
      0, 0, 1, 0, -1, -1, 0, 0, 0, 0, 1, 0],
    ![0, 0, -1, 0, 0, 0, 0, -1, 0, -1, 1, -1,
      0, -1, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1],
    ![1, 1, 1, 0, -1, 1, -1, -1, 2, 1, -2, 1,
      -1, 1, -2, -2, 3, 2, 0, -1, 1, 0, -2, 1],
    ![-1, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1,
      0, -1, 0, 0, -2, -1, -1, 0, -1, -1, 0, -1],
    ![-1, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1,
      0, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0,
      0, 0, 1, 1, -1, 0, 1, 1, 0, 0, 1, 0],
    ![0, 0, 0, -1, 0, 0, 1, 0, -1, 0, 1, -1,
      1, 0, 1, 1, -1, -1, -1, 0, -1, 1, 1, 0],
    ![-1, -1, 0, 0, 0, -1, 0, 0, -1, -1, 1, 0,
      0, -1, 1, 1, -1, -1, 0, 1, 0, 0, 1, -1],
    ![1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0,
      1, 0, 1, 1, -1, -1, 0, 0, -1, 0, 0, 0],
    ![1, 1, 1, 0, 0, 1, -1, 0, 1, 1, -1, 1,
      0, 1, -1, -1, 2, 1, 0, -1, 1, 0, -1, 1]
  ]

set_option maxHeartbeats 8000000 in
-- Check the complete integral basis identity for every physical source column.
/-- This is the exact published integral basis acted on by the entire spatial numerator. -/
theorem generatedNinth_lower_spin_direct_integral_basis_09 :
    Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 9) *
      leechBasisMatrix =
      (generatedNinthLowerSpinTensorSpatialDenominator 9 : ℤ) •
        (leechBasisMatrix * generatedNinthLowerSpinDirectIntegralMatrix09) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
