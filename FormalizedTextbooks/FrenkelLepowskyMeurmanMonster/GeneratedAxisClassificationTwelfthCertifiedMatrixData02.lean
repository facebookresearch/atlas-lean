/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBasisData

/-! Complete physical and integral certificates for Twelfth compact matrix 2. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedNumerator02 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0],
    ![0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0],
    ![-1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0,
      -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0,
      1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1,
      0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1],
    ![-1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0],
    ![0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0],
    ![-1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0,
      1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegral02 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-3, -2, -3, 1, -2, -4, 13, 11, -3, -1, -5, -2,
      16, 6, 10, 7, -5, 4, -4, 4, 7, 12, 10, 2],
    ![0, 0, 0, 0, 0, 1, -3, -2, 1, 0, 1, 1,
      -4, -1, -2, -1, 1, 0, 2, 0, -1, -3, -2, 0],
    ![1, 1, 1, 1, 0, 1, -2, -1, 1, 0, 1, 1,
      -3, -1, -2, -1, 1, 0, 1, -1, -1, -2, -2, 0],
    ![0, 0, 0, -1, 0, 0, -3, -3, 0, 0, 1, 0,
      -4, -2, -3, -2, 1, -1, 0, -1, -2, -3, -2, -1],
    ![1, 0, 1, 0, 1, 1, -2, -2, 1, 0, 1, 0,
      -4, -2, -2, -2, 1, -1, 1, -1, -2, -3, -3, -1],
    ![0, 0, 0, -1, 1, 0, -2, -2, 0, 0, 1, 0,
      -3, -1, -1, -1, 1, -1, 1, 0, -1, -2, -1, 0],
    ![1, 1, 1, 0, 0, 1, -2, -2, 0, 0, 1, 0,
      -3, -2, -2, -1, 1, -1, 0, -1, -2, -2, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      2, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0],
    ![0, 0, 0, -1, 0, 0, -3, -3, 1, 0, 1, 0,
      -3, -1, -2, -2, 1, -1, 1, -1, -1, -2, -2, -1],
    ![1, 1, 1, 0, 0, 1, -2, -2, 1, 1, 2, 2,
      -2, 0, -1, 0, 1, 0, 1, 0, -1, -1, -1, 1],
    ![1, 0, 1, 0, 1, 1, -2, -2, 1, 0, 1, 0,
      -2, -1, -1, -1, 1, -1, 1, -1, -1, -2, -1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, -1, 0, -1, -1,
      1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, -3, -2, 0, 0, 1, 0,
      -3, -1, -2, -1, 0, -1, 1, -1, -2, -3, -2, -1],
    ![0, 0, 0, 0, 0, 0, 1, 1, -1, 0, -1, -1,
      1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1,
      1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 1, 0, -1, 0,
      1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0],
    ![0, 0, 1, -1, 0, 1, -3, -2, 0, 0, 0, 0,
      -3, -1, -2, -2, 1, -1, 0, -1, -1, -2, -2, -1],
    ![0, -1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0,
      1, 0, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1,
      1, 1, 1, 1, -1, 1, 0, 1, 1, 1, 1, 1],
    ![-2, -1, -2, -1, -1, -1, 0, 0, -1, -1, -1, -1,
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0,
      2, 1, 2, 2, 0, 1, 0, 1, 1, 2, 2, 1],
    ![0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 0, 0,
      1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0],
    ![0, 0, 0, 0, -1, -1, 1, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0, 0,
      -2, -1, -2, -1, 0, -1, 0, -1, -1, -2, -2, -1]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegralInverse02 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![5, 4, 0, 3, 0, 5, 3, 0, 4, 3, -10, -12,
      -2, 9, -8, 1, -1, 1, -5, -10, -5, -4, -9, 1],
    ![-1, -1, 0, -1, 0, -1, 0, 0, -1, -1, 2, 2,
      1, -2, 2, 0, 0, -1, 1, 2, 1, 1, 2, 0],
    ![1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 3, 2,
      2, -1, 2, 0, 1, -1, 1, 1, 1, 1, 2, 1],
    ![-2, -1, 0, -1, 0, -1, -1, 1, -1, -1, 2, 3,
      0, -1, 2, 0, 0, 1, 2, 3, 2, 1, 3, 0],
    ![-1, -1, 0, 0, 0, -1, -1, 0, -1, 0, 2, 3,
      0, -2, 1, 0, 0, 0, 1, 2, 1, 1, 1, 0],
    ![-2, -1, -1, -1, 0, -2, -1, 0, -1, -1, 1, 2,
      -1, -2, 1, -1, 0, 0, 1, 2, 1, 0, 1, -1],
    ![-1, -1, 0, -1, 1, -1, -1, 0, -1, -1, 2, 2,
      0, -2, 2, -1, 0, -1, 1, 2, 1, 0, 2, 0],
    ![0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, -1,
      0, 0, -1, 0, 0, 0, -1, -1, -1, 0, -1, -1],
    ![-2, -1, -1, -1, -1, -2, -1, -1, -1, -1, 2, 2,
      0, -2, 1, 0, 0, 0, 1, 2, 1, 1, 2, -1],
    ![-1, -1, 0, -1, 0, -1, 0, 0, 0, -1, 2, 2,
      1, -1, 3, 0, 0, 0, 1, 2, 1, 1, 2, 0],
    ![-1, -1, 0, 0, 0, -1, -1, 0, 0, -1, 1, 2,
      0, -2, 1, -1, 0, 0, 1, 1, 1, 0, 1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, -1,
      -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, -1, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 2, 2,
      1, -2, 1, 0, 0, -1, 0, 1, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 1, -1, 0, 0, 0, -1, -1,
      0, 1, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 1, 0, 0, -1, -1,
      0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, -1,
      0, 0, -1, 0, 0, 0, -1, -1, 0, 0, -1, 0],
    ![-2, -1, 0, -1, -1, -1, -1, 0, -2, -1, 1, 2,
      0, -2, 1, 0, 0, 0, 0, 2, 1, 1, 2, -1],
    ![2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 0,
      1, 1, 0, 1, 0, 0, 0, -1, 0, 0, -1, 1],
    ![2, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, -1,
      1, 1, 0, 0, 0, -1, -1, -1, -1, 0, -1, 1],
    ![0, 1, -1, 0, 0, 0, 0, 0, 0, 0, -1, -1,
      0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, -1,
      -1, 0, 0, -1, 0, 0, 0, -1, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0,
      -1, 1, -1, 0, 0, 1, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2,
      0, -1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0]
  ]

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal left identity. -/
theorem generatedTwelfth_certified_matrix_02_orthogonal_left :
    generatedTwelfthCertifiedNumerator02.transpose *
      generatedTwelfthCertifiedNumerator02 =
      (4 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal right identity. -/
theorem generatedTwelfth_certified_matrix_02_orthogonal_right :
    generatedTwelfthCertifiedNumerator02 *
      generatedTwelfthCertifiedNumerator02.transpose =
      (4 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the basis identity. -/
theorem generatedTwelfth_certified_matrix_02_basis :
    generatedTwelfthCertifiedNumerator02 *
      leechBasisMatrix =
      (2 : ℤ) • (leechBasisMatrix *
      generatedTwelfthCertifiedIntegral02) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the integral inverse identity. -/
theorem generatedTwelfth_certified_matrix_02_integral_inverse :
    generatedTwelfthCertifiedIntegral02 *
      generatedTwelfthCertifiedIntegralInverse02 =
      1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
