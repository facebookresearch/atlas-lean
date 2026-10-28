/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData05

/-! Complete orthogonality and integral inverse certificates for one literal spatial matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The entire inverse lattice-coordinate matrix has integral entries. -/
def generatedNinthLowerSpinDirectIntegralInverse05 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![34, 16, 17, 14, 16, 19, 14, 7, 16, 14, 14, 3,
      16, 6, -3, -4, 17, -4, 5, -5, -3, 6, -2, 11],
    ![-6, -3, -3, -2, -3, -3, -2, -1, -3, -2, -2, 0,
      -3, -1, 1, 2, -2, 2, 0, 2, 1, 0, 1, -1],
    ![-6, -3, -2, -2, -3, -3, -3, -1, -3, -2, -3, 0,
      -3, -1, 0, 1, -3, 1, -1, 1, 1, -1, 0, -2],
    ![-7, -3, -3, -2, -4, -4, -3, -1, -3, -3, -3, 0,
      -3, -1, 1, 1, -4, 1, -1, 1, 1, -1, 0, -2],
    ![-7, -3, -3, -3, -3, -4, -3, -1, -3, -3, -3, 0,
      -3, -1, 1, 1, -4, 1, -1, 1, 1, -1, 0, -2],
    ![-6, -3, -3, -3, -3, -4, -2, -2, -3, -3, -2, -1,
      -3, -2, 1, 0, -3, 0, -1, 1, 0, -1, 0, -2],
    ![-8, -4, -4, -4, -4, -4, -3, -2, -4, -4, -4, -2,
      -4, -2, 0, 0, -4, 0, -2, 0, 0, -2, 0, -4],
    ![2, 1, 0, 1, 2, 1, 1, 1, 1, 1, 1, 0,
      1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1],
    ![-6, -3, -3, -2, -3, -4, -2, -1, -3, -2, -2, 0,
      -2, -1, 1, 2, -3, 1, -1, 2, 1, 0, 1, -1],
    ![-6, -3, -3, -3, -3, -3, -2, -1, -3, -2, -2, -1,
      -3, -1, 1, 1, -3, 1, -1, 1, 0, -1, 1, -2],
    ![-7, -3, -4, -3, -3, -4, -4, -2, -3, -3, -3, -1,
      -3, -1, 0, 0, -4, 0, -1, 0, 1, -2, 0, -3],
    ![2, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0,
      1, 0, 0, -1, 1, -1, 0, -1, -1, 0, 0, 0],
    ![-7, -4, -4, -3, -3, -4, -3, -2, -3, -3, -3, -1,
      -4, -2, 0, 0, -3, 1, -1, 1, 0, -2, 0, -3],
    ![2, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0,
      1, 1, -1, -1, 1, -1, 0, -1, 0, 0, -1, 0],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 1, 1, 0, 2, 0, 1, 0, 0, 1, 0, 2],
    ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 1, 0, 1, 2, 0, 1, 0, 0, 1, 0, 2],
    ![-5, -2, -3, -2, -2, -3, -2, -1, -2, -2, -2, 0,
      -2, 0, 1, 1, -2, 1, 0, 1, 1, -1, 1, -1],
    ![2, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0,
      1, 0, -1, -1, 1, 0, 0, -1, 0, 0, -1, 0],
    ![2, 1, 1, 1, 1, 2, 1, 1, 0, 1, 1, 0,
      0, 0, -1, 0, 1, 0, 0, 0, -1, 0, 0, 0],
    ![2, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0,
      1, 0, 0, 0, 2, 0, 1, 1, 0, 1, 0, 1],
    ![2, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, -1,
      1, 0, 0, -1, 1, -1, 0, -1, 0, 0, 0, 0],
    ![2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![2, 1, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1,
      1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1],
    ![-4, -2, -2, -2, -2, -2, -2, -1, -2, -2, -2, -1,
      -2, -1, 0, 0, -2, 0, -1, 0, 0, -1, 0, -1]
  ]

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_left_05 :
    (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 5)).transpose *
      Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 5) =
      ((generatedNinthLowerSpinTensorSpatialDenominator 5 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 5 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_right_05 :
    Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 5) *
      (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 5)).transpose =
      ((generatedNinthLowerSpinTensorSpatialDenominator 5 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 5 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check that the whole lattice coordinate inverse is genuinely integral and exact.
/-- The certified lattice coordinate action has the complete integer inverse. -/
theorem generatedNinth_lower_spin_direct_isometry_inverse_05 :
    generatedNinthLowerSpinDirectIntegralMatrix05 *
      generatedNinthLowerSpinDirectIntegralInverse05 = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
