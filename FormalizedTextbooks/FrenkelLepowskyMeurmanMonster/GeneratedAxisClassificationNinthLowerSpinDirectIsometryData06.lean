/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData06

/-! Complete orthogonality and integral inverse certificates for one literal spatial matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The entire inverse lattice-coordinate matrix has integral entries. -/
def generatedNinthLowerSpinDirectIntegralInverse06 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![24, 11, 11, 7, 12, 5, 9, -2, 21, 6, 10, 6,
      2, -1, 2, -11, 12, -6, 7, -7, -1, -3, -9, 12],
    ![-5, -2, -2, -1, -3, -2, -2, 0, -5, -1, -2, -1,
      -1, -1, -1, 2, -2, 1, -2, 2, 0, 1, 1, -3],
    ![-4, -2, -1, -1, -2, 0, -2, 1, -4, -1, -2, -1,
      -1, 0, -1, 2, -2, 1, -1, 1, 0, 0, 1, -2],
    ![-4, -2, -2, -1, -2, 0, -1, 1, -4, 0, -2, -1,
      0, 1, 0, 3, -2, 2, -1, 2, 0, 1, 2, -1],
    ![-5, -2, -2, -1, -2, -1, -2, 1, -4, -1, -2, 0,
      0, 1, 0, 3, -3, 2, -1, 2, 1, 1, 2, -2],
    ![-4, -2, -2, -1, -2, -1, -1, 0, -4, -1, -1, -1,
      0, 0, 0, 2, -2, 1, -1, 2, 0, 1, 2, -2],
    ![-6, -3, -3, -2, -3, -1, -2, 0, -5, -2, -3, -2,
      -1, 0, -1, 2, -3, 1, -2, 1, 0, 0, 2, -4],
    ![2, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0,
      1, 0, 1, -1, 1, -1, 0, -1, 0, 0, 0, 1],
    ![-4, -2, -2, -1, -2, -1, -1, 1, -4, -1, -1, -1,
      0, 0, 0, 3, -2, 1, -1, 2, 0, 1, 2, -1],
    ![-4, -2, -2, -1, -2, -1, -2, 0, -4, -1, -1, -1,
      0, 0, 0, 2, -2, 0, -1, 1, 0, 0, 2, -2],
    ![-4, -2, -2, -2, -2, 0, -2, 0, -3, -1, -1, -1,
      0, 1, 0, 2, -2, 1, -1, 1, 0, 0, 2, -2],
    ![1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0,
      0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0],
    ![-4, -2, -2, -1, -2, -1, -2, 0, -4, -2, -2, -2,
      0, -1, -1, 1, -2, 0, -2, 0, 0, 0, 1, -3],
    ![2, 1, 1, 0, 1, 1, 1, 0, 2, 1, 0, 0,
      0, 1, 0, -1, 1, 0, 0, -1, 0, 0, -1, 1],
    ![2, 1, 1, 1, 1, 0, 1, 0, 2, 1, 1, 1,
      0, 0, 1, -1, 1, 0, 1, 0, 0, 0, -1, 1],
    ![2, 1, 1, 1, 1, 0, 1, 0, 2, 1, 1, 1,
      0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 1],
    ![-4, -1, -2, -1, -2, -1, -1, 1, -3, -1, -2, -1,
      0, 1, 0, 2, -2, 2, -1, 1, 1, 1, 2, -2],
    ![2, 1, 1, 1, 1, 1, 0, 0, 2, 0, 1, 1,
      0, 0, 0, -1, 1, 0, 1, -1, 0, -1, -1, 1],
    ![1, 0, 1, 0, 0, 0, 0, -1, 1, 0, 0, 0,
      0, -1, 0, -1, 1, -1, 0, -1, 0, 0, -1, 0],
    ![2, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0,
      0, -1, 0, -1, 1, -1, 0, 0, 0, 0, -1, 1],
    ![1, 0, 0, 0, 1, 0, 0, -1, 1, 0, 1, 0,
      0, 0, 0, -1, 1, -1, 1, 0, 0, -1, 0, 0],
    ![2, 1, 1, 0, 1, 1, 1, 0, 2, 1, 1, 1,
      1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 2],
    ![2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2],
    ![-4, -2, -2, -1, -2, -1, -2, 0, -3, -1, -2, -1,
      -1, 0, -1, 1, -2, 1, -1, 1, 0, 0, 1, -2]
  ]

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_left_06 :
    (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 6)).transpose *
      Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 6) =
      ((generatedNinthLowerSpinTensorSpatialDenominator 6 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 6 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_right_06 :
    Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 6) *
      (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 6)).transpose =
      ((generatedNinthLowerSpinTensorSpatialDenominator 6 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 6 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check that the whole lattice coordinate inverse is genuinely integral and exact.
/-- The certified lattice coordinate action has the complete integer inverse. -/
theorem generatedNinth_lower_spin_direct_isometry_inverse_06 :
    generatedNinthLowerSpinDirectIntegralMatrix06 *
      generatedNinthLowerSpinDirectIntegralInverse06 = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
