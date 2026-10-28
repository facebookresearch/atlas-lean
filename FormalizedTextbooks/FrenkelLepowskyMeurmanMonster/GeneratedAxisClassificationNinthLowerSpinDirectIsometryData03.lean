/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData03

/-! Complete orthogonality and integral inverse certificates for one literal spatial matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The entire inverse lattice-coordinate matrix has integral entries. -/
def generatedNinthLowerSpinDirectIntegralInverse03 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 1, 0, 0, -3, -1, 1, 0, 0, 1,
      -3, -1, -5, -5, 0, -2, 1, -1, -2, -3, -3, -5],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1,
      1, 0, 1, 1, 0, 0, -1, 0, 0, 1, 1, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0,
      0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, -1,
      1, 0, 1, 1, 0, 0, -1, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0,
      0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
      1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, -2, -1, 0, 0, 0, 0,
      0, 0, -1, -1, 0, -1, 0, -1, 0, -1, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -2, -1, -1, -1, 0, 0, 0, 0, -1, -1, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  ]

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_left_03 :
    (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 3)).transpose *
      Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 3) =
      ((generatedNinthLowerSpinTensorSpatialDenominator 3 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 3 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_right_03 :
    Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 3) *
      (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 3)).transpose =
      ((generatedNinthLowerSpinTensorSpatialDenominator 3 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 3 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check that the whole lattice coordinate inverse is genuinely integral and exact.
/-- The certified lattice coordinate action has the complete integer inverse. -/
theorem generatedNinth_lower_spin_direct_isometry_inverse_03 :
    generatedNinthLowerSpinDirectIntegralMatrix03 *
      generatedNinthLowerSpinDirectIntegralInverse03 = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
