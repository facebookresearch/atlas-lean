/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData08

/-! Complete orthogonality and integral inverse certificates for one literal spatial matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The entire inverse lattice-coordinate matrix has integral entries. -/
def generatedNinthLowerSpinDirectIntegralInverse08 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![30, 14, 14, 6, 15, 21, 14, 6, 20, 22, 16, 5,
      9, 15, 7, 7, 15, 5, 6, 1, -1, 7, 1, 20],
    ![-6, -2, -3, -1, -3, -4, -3, -1, -5, -4, -3, -1,
      -2, -3, -2, -1, -3, -1, -1, 0, 0, -1, 0, -4],
    ![-5, -2, -2, -1, -2, -4, -3, -1, -4, -4, -3, -1,
      -2, -3, -2, -2, -3, -2, -2, -1, 0, -2, -1, -4],
    ![-6, -3, -3, -1, -3, -5, -3, -2, -4, -5, -4, -2,
      -2, -4, -2, -3, -3, -2, -2, -1, 0, -2, -1, -5],
    ![-6, -3, -2, -1, -3, -4, -3, -1, -4, -5, -3, -1,
      -1, -3, -1, -1, -3, -1, -1, 0, 1, -1, 0, -4],
    ![-6, -3, -3, -1, -3, -4, -2, -1, -4, -4, -3, -1,
      -2, -3, -1, -1, -3, 0, -1, 1, 0, -1, 0, -4],
    ![-6, -3, -3, -1, -3, -4, -2, -1, -4, -5, -3, -1,
      -2, -3, -1, -1, -3, -1, -1, 0, 0, -2, 0, -4],
    ![2, 1, 1, 0, 1, 2, 1, 1, 2, 2, 1, 1,
      1, 2, 1, 1, 1, 1, 1, 0, 0, 1, 1, 2],
    ![-6, -3, -3, -1, -3, -4, -3, -1, -4, -4, -3, -1,
      -2, -3, -2, -1, -3, -1, -1, 0, 0, -1, 0, -4],
    ![-6, -3, -3, -1, -3, -4, -3, -1, -4, -4, -3, -1,
      -2, -3, -1, -1, -3, -1, -1, 0, 0, -2, 0, -4],
    ![-6, -3, -3, -2, -3, -4, -3, -2, -3, -5, -3, -1,
      -2, -3, -1, -2, -3, -1, -1, -1, 0, -2, 0, -4],
    ![3, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1,
      1, 1, 1, 1, 2, 1, 1, 1, 0, 1, 0, 2],
    ![-4, -2, -2, 0, -2, -2, -2, 0, -3, -3, -2, 0,
      -1, -2, -1, 0, -2, 0, 0, 0, 0, -1, 0, -2],
    ![2, 1, 1, 0, 1, 1, 1, 0, 2, 1, 0, 0,
      0, 1, 0, -1, 1, 0, 0, -1, 0, 0, -1, 1],
    ![2, 1, 1, 0, 1, 1, 1, 0, 1, 2, 1, 0,
      1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1],
    ![2, 1, 1, 0, 1, 1, 1, 0, 1, 2, 1, 0,
      1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1],
    ![-5, -2, -2, -1, -3, -4, -2, -1, -3, -3, -3, 0,
      -1, -2, -1, -1, -2, 0, -1, 0, 1, 0, 0, -3],
    ![2, 1, 1, 0, 1, 2, 0, 0, 1, 1, 1, 0,
      1, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1],
    ![3, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1,
      1, 2, 1, 1, 1, 0, 1, 0, 0, 0, 0, 2],
    ![2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1,
      0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 2],
    ![1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0,
      0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1],
    ![2, 1, 1, 0, 1, 1, 1, 0, 2, 1, 1, 0,
      1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1],
    ![2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    ![-4, -2, -2, -1, -2, -3, -2, -1, -3, -3, -2, -1,
      -1, -2, -1, -1, -2, -1, -1, 0, 0, -1, 0, -2]
  ]

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_left_08 :
    (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 8)).transpose *
      Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 8) =
      ((generatedNinthLowerSpinTensorSpatialDenominator 8 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 8 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_right_08 :
    Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 8) *
      (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 8)).transpose =
      ((generatedNinthLowerSpinTensorSpatialDenominator 8 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 8 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check that the whole lattice coordinate inverse is genuinely integral and exact.
/-- The certified lattice coordinate action has the complete integer inverse. -/
theorem generatedNinth_lower_spin_direct_isometry_inverse_08 :
    generatedNinthLowerSpinDirectIntegralMatrix08 *
      generatedNinthLowerSpinDirectIntegralInverse08 = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
