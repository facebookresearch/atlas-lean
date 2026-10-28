/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData04

/-! Complete orthogonality and integral inverse certificates for one literal spatial matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The entire inverse lattice-coordinate matrix has integral entries. -/
def generatedNinthLowerSpinDirectIntegralInverse04 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![30, 17, 16, 13, 13, 17, 13, 8, 18, 17, 14, 10,
      17, 13, 8, 8, 12, 2, 6, -9, 1, 17, 1, 20],
    ![-5, -2, -3, -2, -2, -3, -2, -1, -3, -3, -2, -1,
      -3, -2, -1, -1, -2, 0, -1, 2, 0, -3, 0, -3],
    ![-5, -3, -2, -2, -2, -3, -2, -1, -3, -3, -2, -1,
      -3, -2, -1, -1, -2, 0, -1, 2, 0, -3, 0, -3],
    ![-7, -4, -4, -3, -3, -4, -3, -2, -5, -4, -3, -3,
      -4, -3, -2, -2, -3, -1, -2, 2, -1, -4, 0, -5],
    ![-7, -4, -3, -3, -3, -4, -4, -2, -4, -4, -3, -2,
      -4, -3, -2, -2, -3, -1, -1, 2, 0, -4, -1, -5],
    ![-5, -3, -3, -2, -2, -2, -2, -1, -3, -3, -2, -2,
      -3, -2, -1, -1, -2, 0, 0, 2, 0, -3, 0, -3],
    ![-6, -4, -3, -3, -3, -3, -2, -2, -3, -3, -3, -2,
      -3, -2, -1, -1, -2, 0, -1, 2, 0, -3, 0, -4],
    ![2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0,
      1, 0, 0, 0, 1, 0, 0, -1, 0, 1, 0, 1],
    ![-5, -3, -3, -2, -2, -3, -2, -1, -4, -3, -2, -2,
      -3, -3, -2, -1, -2, -1, -1, 2, -1, -3, 0, -3],
    ![-5, -3, -3, -2, -2, -3, -2, -1, -3, -2, -2, -1,
      -3, -2, -1, -1, -2, 0, -1, 2, 0, -3, 0, -3],
    ![-6, -4, -3, -2, -3, -3, -3, -2, -4, -3, -3, -2,
      -3, -3, -2, -1, -2, 0, -1, 2, 0, -3, 0, -4],
    ![2, 1, 1, 0, 1, 1, 1, 0, 2, 1, 1, 0,
      1, 1, 1, 0, 1, 0, 1, -1, 0, 1, 0, 1],
    ![-4, -3, -2, -2, -2, -3, -2, -2, -2, -3, -2, -2,
      -2, -3, -1, -2, -1, -1, -1, 1, 0, -3, -1, -3],
    ![2, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0,
      1, 1, 0, 0, 1, 0, 0, -1, 0, 1, 0, 1],
    ![2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 0, 0, 0, 0, -1, 0, 1, 0, 1],
    ![2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1],
    ![-5, -2, -3, -2, -2, -3, -2, -1, -3, -3, -3, -2,
      -3, -2, -2, -2, -2, 0, -1, 1, 0, -3, 0, -4],
    ![2, 1, 2, 1, 0, 1, 0, 0, 1, 1, 1, 1,
      1, 0, 0, 0, 1, 0, 0, -1, 0, 1, -1, 1],
    ![2, 1, 1, 0, 1, 1, 1, 0, 2, 1, 1, 1,
      1, 1, 1, 0, 1, 0, 0, -1, 0, 1, 0, 1],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 1, 1, 1, 2, 0, 1, 0, 0, 2, 0, 3],
    ![2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1,
      2, 2, 1, 2, 1, 1, 1, 0, 1, 2, 1, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1,
      1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 2],
    ![-4, -2, -2, -2, -2, -2, -2, -1, -2, -2, -2, -1,
      -2, -1, -1, -1, -2, 0, -1, 1, 0, -2, 0, -2]
  ]

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_left_04 :
    (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 4)).transpose *
      Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 4) =
      ((generatedNinthLowerSpinTensorSpatialDenominator 4 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 4 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_right_04 :
    Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 4) *
      (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 4)).transpose =
      ((generatedNinthLowerSpinTensorSpatialDenominator 4 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 4 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check that the whole lattice coordinate inverse is genuinely integral and exact.
/-- The certified lattice coordinate action has the complete integer inverse. -/
theorem generatedNinth_lower_spin_direct_isometry_inverse_04 :
    generatedNinthLowerSpinDirectIntegralMatrix04 *
      generatedNinthLowerSpinDirectIntegralInverse04 = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
