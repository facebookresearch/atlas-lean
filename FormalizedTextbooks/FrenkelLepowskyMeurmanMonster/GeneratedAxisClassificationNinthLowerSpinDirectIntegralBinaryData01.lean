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
def generatedNinthLowerSpinDirectIntegralMatrix01 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![57, 28, 28, 29, 28, 29, 25, 14, 29, 29, 26, 12,
      29, 15, 10, 11, 28, -1, 12, -2, -2, 14, -2, 34],
    ![-12, -6, -6, -6, -6, -6, -5, -3, -6, -6, -5, -2,
      -6, -3, -2, -2, -5, 1, -2, 1, 1, -2, 1, -7],
    ![-10, -5, -5, -5, -4, -5, -5, -2, -5, -5, -5, -2,
      -5, -2, -2, -2, -5, 0, -2, 0, 1, -3, 0, -6],
    ![-12, -6, -6, -7, -6, -6, -5, -3, -6, -6, -6, -3,
      -6, -3, -2, -3, -6, 0, -3, 0, 0, -3, 0, -7],
    ![-12, -6, -5, -6, -6, -6, -6, -3, -6, -6, -5, -2,
      -6, -3, -2, -2, -6, 0, -2, 1, 1, -3, 0, -7],
    ![-10, -5, -5, -5, -5, -6, -4, -3, -5, -5, -4, -2,
      -5, -3, -1, -2, -5, 0, -2, 1, 0, -2, 0, -6],
    ![-12, -6, -6, -6, -6, -6, -5, -3, -6, -6, -6, -3,
      -6, -3, -2, -2, -6, 0, -3, 0, 0, -3, 0, -8],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 3],
    ![-10, -5, -5, -5, -5, -5, -4, -2, -6, -5, -4, -2,
      -5, -3, -2, -1, -5, 0, -2, 1, 0, -2, 1, -5],
    ![-10, -5, -5, -5, -5, -5, -4, -2, -5, -6, -4, -2,
      -5, -3, -1, -2, -5, 0, -2, 0, 0, -3, 1, -6],
    ![-10, -5, -5, -5, -5, -5, -5, -3, -5, -5, -5, -2,
      -5, -3, -2, -2, -5, 0, -2, 0, 0, -3, 0, -6],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 0,
      2, 1, 1, 1, 2, 0, 1, 0, 0, 1, 0, 2],
    ![-10, -5, -5, -5, -5, -5, -5, -3, -5, -5, -4, -2,
      -6, -3, -2, -2, -5, 0, -2, 0, 0, -3, 0, -6],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 0, 0,
      2, 1, 0, 0, 2, 0, 0, -1, 0, 1, -1, 2],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 1, 1, 0, 2, 0, 1, 0, 0, 1, 0, 2],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 1, 0, 1, 2, 0, 1, 0, 0, 1, 0, 2],
    ![-10, -4, -5, -5, -5, -5, -4, -2, -5, -5, -5, -2,
      -5, -2, -2, -2, -5, 1, -2, 0, 1, -2, 1, -6],
    ![4, 2, 2, 2, 2, 2, 0, 0, 2, 2, 2, 1,
      2, 1, 0, 0, 2, -1, 1, -1, 0, 0, -1, 2],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 1, 1, 1, 2, 0, 0, 0, 0, 1, 0, 2],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 1, 1, 1, 2, 0, 1, 0, 0, 2, 0, 3],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 1, 1, 1, 2, 0, 1, 0, -1, 1, 0, 2],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 1, 1, 1, 2, 0, 1, 1, 0, 1, 0, 3],
    ![4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1,
      2, 1, 1, 1, 2, 0, 1, 0, 0, 1, 0, 3],
    ![-8, -4, -4, -4, -4, -4, -4, -2, -4, -4, -4, -2,
      -4, -2, -2, -2, -4, 0, -2, 0, 0, -2, 0, -5]
  ]

set_option maxHeartbeats 8000000 in
-- Check the complete integral basis identity for every physical source column.
/-- This is the exact published integral basis acted on by the entire spatial numerator. -/
theorem generatedNinth_lower_spin_direct_integral_basis_01 :
    Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 1) *
      leechBasisMatrix =
      (generatedNinthLowerSpinTensorSpatialDenominator 1 : ℤ) •
        (leechBasisMatrix * generatedNinthLowerSpinDirectIntegralMatrix01) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
