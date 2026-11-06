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
def generatedNinthLowerSpinDirectIntegralMatrix07 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![28, 13, 16, 21, 11, 5, 12, 6, 22, 19, 13, 19,
      22, 12, 12, 10, 14, 5, 4, 6, 14, 14, -3, 21],
    ![-5, -2, -3, -5, -2, -1, -2, -2, -4, -3, -2, -4,
      -4, -2, -2, -2, -2, -1, -1, -1, -3, -2, 1, -4],
    ![-4, -2, -2, -3, -1, -1, -2, -1, -3, -3, -2, -3,
      -4, -2, -2, -2, -2, -1, 0, -1, -2, -3, 0, -3],
    ![-6, -3, -4, -4, -2, -1, -2, -1, -4, -4, -3, -4,
      -5, -2, -2, -2, -3, 0, 0, -1, -3, -3, 1, -4],
    ![-6, -3, -3, -4, -2, -1, -3, -1, -5, -4, -3, -4,
      -5, -3, -3, -2, -3, -1, -1, -1, -3, -3, 0, -5],
    ![-5, -2, -3, -4, -2, -1, -2, -1, -4, -3, -2, -3,
      -4, -2, -2, -2, -3, -1, -1, -1, -3, -2, 0, -4],
    ![-6, -3, -3, -4, -3, -1, -2, -1, -5, -4, -3, -4,
      -5, -3, -3, -2, -3, -1, -1, -1, -3, -3, 0, -5],
    ![2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      2, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 2],
    ![-5, -2, -3, -4, -2, -1, -2, -1, -4, -3, -2, -3,
      -4, -2, -2, -1, -3, -1, -1, -1, -3, -2, 1, -3],
    ![-5, -2, -3, -4, -2, -1, -2, -1, -4, -3, -2, -3,
      -4, -2, -2, -2, -3, -1, -1, -1, -3, -3, 1, -4],
    ![-5, -2, -3, -3, -2, 0, -2, 0, -4, -4, -2, -3,
      -4, -2, -2, -1, -3, 0, 0, -1, -2, -3, 1, -3],
    ![1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1,
      1, 0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0],
    ![-5, -3, -3, -4, -2, -1, -3, -2, -5, -3, -2, -4,
      -4, -3, -3, -2, -2, -2, -1, -1, -3, -3, 0, -4],
    ![2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 0, 1,
      2, 2, 1, 1, 1, 1, 1, 0, 2, 1, 0, 2],
    ![2, 1, 1, 1, 1, 0, 1, 0, 2, 1, 1, 1,
      2, 1, 2, 0, 1, 0, 0, 0, 1, 1, 0, 1],
    ![2, 1, 1, 1, 1, 0, 1, 0, 2, 1, 1, 1,
      2, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1],
    ![-5, -2, -3, -4, -2, -1, -2, -1, -4, -4, -3, -4,
      -3, -2, -2, -2, -2, -1, -1, -2, -2, -2, 1, -4],
    ![2, 1, 1, 2, 1, 0, 0, 0, 1, 1, 1, 1,
      1, 0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 1],
    ![3, 1, 2, 2, 1, 1, 1, 0, 2, 2, 2, 2,
      2, 1, 1, 1, 2, 0, 1, 1, 1, 1, 0, 2],
    ![2, 1, 1, 1, 1, 0, 1, 0, 1, 2, 1, 1,
      2, 1, 1, 1, 1, 0, 0, 1, 1, 2, 0, 2],
    ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 2,
      1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    ![2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2],
    ![2, 1, 1, 2, 1, 0, 1, 1, 2, 2, 1, 2,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2],
    ![-4, -2, -2, -3, -2, -1, -2, -1, -3, -3, -2, -3,
      -3, -2, -2, -2, -2, -1, -1, -1, -2, -2, 0, -3]
  ]

set_option maxHeartbeats 8000000 in
-- Check the complete integral basis identity for every physical source column.
/-- This is the exact published integral basis acted on by the entire spatial numerator. -/
theorem generatedNinth_lower_spin_direct_integral_basis_07 :
    Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 7) *
      leechBasisMatrix =
      (generatedNinthLowerSpinTensorSpatialDenominator 7 : ℤ) •
        (leechBasisMatrix * generatedNinthLowerSpinDirectIntegralMatrix07) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
