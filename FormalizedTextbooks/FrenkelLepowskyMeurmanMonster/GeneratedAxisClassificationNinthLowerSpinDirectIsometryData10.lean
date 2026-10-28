/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData10

/-! Complete orthogonality and integral inverse certificates for one literal spatial matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The entire inverse lattice-coordinate matrix has integral entries. -/
def generatedNinthLowerSpinDirectIntegralInverse10 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-1, -1, -2, 4, 0, -1, -7, -8, 2, 4, 12, 8,
      -3, 0, 4, 0, -10, -5, 7, 2, 2, -6, -6, -3],
    ![0, 0, 1, -1, 0, 0, 1, 2, 0, -1, -2, -1,
      0, 0, 0, 0, 2, 1, -1, 0, 0, 1, 1, 1],
    ![0, 0, 0, -1, 0, 0, 1, 1, 0, -1, -3, -2,
      0, 0, -1, -1, 1, 0, -2, -1, -1, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 1, 1, 0, -1, -3, -2,
      1, 0, -1, 0, 2, 1, -2, -1, 0, 1, 1, 0],
    ![0, 0, 1, -1, 0, 0, 2, 2, -1, -1, -3, -2,
      1, 0, 0, 0, 2, 1, -2, 0, 0, 2, 2, 1],
    ![0, 0, 1, 0, 0, 0, 1, 2, -1, -1, -2, -1,
      0, -1, -1, 0, 2, 1, -1, 0, 0, 1, 1, 0],
    ![1, 0, 1, 0, 0, 1, 2, 2, 0, 0, -2, -1,
      1, 0, -1, 1, 2, 1, -1, 0, -1, 1, 1, 1],
    ![0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, -1, 0, 0, 2, 2, 0, -1, -2, -1,
      0, 0, 0, 0, 2, 2, -1, 0, 0, 2, 2, 1],
    ![2, 1, 1, 0, 0, 1, 2, 1, 1, 0, -1, -1,
      1, 0, -1, 0, 3, 1, -1, -1, -1, 1, 0, 1],
    ![0, 0, 0, -1, 0, 0, 1, 1, 0, -1, -3, -2,
      1, 0, -1, -1, 2, 1, -1, -1, 0, 1, 1, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, -1, 1, 1, 1,
      0, 0, 0, 1, -1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 1, 1, -1, 0, -2, -1,
      0, 0, -1, 0, 2, 1, -1, 0, -1, 1, 1, 1],
    ![-1, -1, -1, 0, 0, -1, -1, -1, 0, 0, 0, 0,
      0, 0, 0, 0, -2, -1, 0, 0, 0, -1, -1, -1],
    ![0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      0, 0, 0, 0, -1, -1, 0, -1, 0, -1, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 1, 0, -1, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 1, 1, -1, -1, -2, -2,
      1, 0, -1, 0, 1, 0, -2, -1, -1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0,
      0, 0, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0],
    ![1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 2, 1,
      0, 1, 1, 1, 0, 0, 2, 1, 0, -1, 0, 1],
    ![-1, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 2,
      -1, 0, 1, 0, -1, 0, 1, 1, 1, 0, 0, 0],
    ![1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0],
    ![1, 1, 0, 1, 0, 0, 0, -1, 1, 1, 1, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![-1, 0, 0, -1, -1, 0, 0, 1, -1, -1, -2, -1,
      0, 0, -1, 0, 1, 1, -1, 0, 0, 1, 1, 0]
  ]

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_left_10 :
    (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 10)).transpose *
      Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 10) =
      ((generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check the entire rational orthogonality identity on all twenty-four coordinates.
/-- The complete literal spatial numerator is orthogonal at its exact denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_right_10 :
    Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 10) *
      (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator 10)).transpose =
      ((generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator 10 : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check that the whole lattice coordinate inverse is genuinely integral and exact.
/-- The certified lattice coordinate action has the complete integer inverse. -/
theorem generatedNinth_lower_spin_direct_isometry_inverse_10 :
    generatedNinthLowerSpinDirectIntegralMatrix10 *
      generatedNinthLowerSpinDirectIntegralInverse10 = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
