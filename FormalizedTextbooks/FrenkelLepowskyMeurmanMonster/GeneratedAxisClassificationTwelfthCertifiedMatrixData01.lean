/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBasisData

/-! Complete physical and integral certificates for Twelfth compact matrix 1. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedNumerator01 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0],
    ![-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
      0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0,
      -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0,
      1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0,
      1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0,
      1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![-1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![-1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
      0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0],
    ![0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegral01 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-2, -3, 0, 2, 13, -18, 0, -1, 0, -1, -2, 2,
      3, 1, 10, -5, -3, -9, 0, 8, 15, -7, -1, 0],
    ![0, 1, 0, 0, -3, 4, 0, 1, 0, 0, 0, 0,
      -1, 0, -2, 1, 1, 3, 1, -1, -2, 2, 1, 0],
    ![0, 0, -1, -1, -3, 3, 0, -1, 0, 0, 1, -1,
      -1, -1, -2, 1, 0, 1, 0, -2, -4, 0, 0, -1],
    ![1, 1, 0, 0, -3, 4, 0, 0, 1, 0, 1, 0,
      0, 0, -2, 1, 1, 2, 0, -2, -3, 1, 0, 0],
    ![0, 0, 0, -1, -3, 4, 0, 0, -1, 0, 0, -1,
      -1, -1, -3, 1, 0, 1, -1, -2, -4, 1, 0, -1],
    ![1, 1, 1, 0, -2, 4, 0, 1, 0, 1, 0, 0,
      0, 1, -2, 1, 1, 2, 0, -1, -2, 2, 0, 1],
    ![1, 1, 0, 0, -3, 4, 0, 0, 0, 1, 1, 0,
      0, 0, -2, 2, 1, 2, 0, -2, -3, 2, 0, 1],
    ![0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, -1, 0, 1, 1, 0, 0, 0],
    ![1, 1, 1, 0, -2, 3, 0, 0, 0, 0, 1, 0,
      -1, -1, -2, 0, 1, 1, 0, -1, -3, 1, 0, 0],
    ![1, 1, 0, 0, -2, 3, 0, 0, 1, 1, 0, 0,
      -1, 0, -2, 0, 1, 2, 0, -2, -3, 1, -1, 0],
    ![0, 0, 0, -1, -2, 3, 0, 0, 0, 0, 1, 0,
      -1, 0, -1, 1, 0, 1, 0, -1, -3, 1, 0, 0],
    ![0, 0, 0, 0, 1, -1, 0, 0, -1, 0, -1, -1,
      1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, -2, 3, 0, 1, -1, 0, 0, -1,
      -1, -1, -2, 1, 0, 1, 0, -1, -3, 1, 0, 0],
    ![0, 0, 0, 0, 1, -1, 0, 0, 1, 0, 1, 1,
      1, 1, 2, 1, 0, 0, 1, 1, 2, 0, 1, 1],
    ![0, 0, 0, 0, 1, -1, 0, 0, 1, 0, -1, 0,
      1, 1, 1, -1, 0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 1, -1, 1, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0],
    ![0, 0, 0, -1, -2, 3, 0, 0, 0, 0, 0, -1,
      0, 0, -1, 1, 1, 2, 0, -1, -2, 2, 1, 0],
    ![-2, -2, -1, -1, 0, -2, -1, -1, -1, -1, -1, -1,
      -1, -1, 0, -1, -2, -2, -1, 0, 0, -2, -1, -2],
    ![0, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 0, 1, -1, 0, 0],
    ![0, 0, 1, 1, 1, -1, 0, 1, 0, 0, 0, 1,
      0, 0, 1, 0, 0, 0, 1, 2, 2, 0, 0, 1],
    ![0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 0, 1,
      0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, -1, 0, 0, 0, -1, 0, 0,
      0, 0, 0, -1, 0, -1, 0, 0, 1, -1, 0, 0],
    ![0, 0, 0, 0, 0, -2, 0, -1, 0, 0, 0, 0,
      0, -1, 0, -1, 0, -1, -1, 0, 0, -1, -1, -1],
    ![0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 1, 0, -1, -2, 1, 0, 0]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegralInverse01 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-3, -4, 2, -1, -3, -3, 2, 0, -15, 0, -19, -14,
      -13, -15, -20, -6, 0, -6, -17, -3, -10, -2, -16, -7],
    ![0, 1, 0, 0, 0, 0, -1, 0, 3, 0, 4, 4,
      2, 3, 4, 1, -1, 1, 3, 1, 2, 0, 3, 1],
    ![0, 0, -1, -1, 0, 1, -1, -1, 3, 0, 3, 2,
      2, 3, 3, 1, 0, 1, 3, 0, 1, 0, 3, 1],
    ![1, 1, -1, 1, 0, 1, 0, 0, 4, 0, 4, 3,
      3, 3, 4, 2, 0, 2, 4, 0, 2, 0, 3, 2],
    ![0, 0, -1, 0, 1, 0, -1, 0, 3, 0, 4, 3,
      2, 3, 4, 1, 0, 1, 4, 1, 2, 0, 3, 1],
    ![1, 1, 0, 1, 1, 0, 0, 0, 3, 0, 4, 3,
      2, 2, 4, 1, 0, 1, 3, 1, 2, 0, 2, 1],
    ![1, 1, 0, 0, 1, 1, 0, 0, 3, 0, 5, 3,
      3, 3, 5, 2, 0, 1, 4, 1, 2, 1, 4, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -2, -2,
      0, -1, -2, -1, 0, -1, -2, -1, -1, 0, -1, -1],
    ![1, 1, 0, 1, 1, 1, 0, 1, 3, 1, 3, 3,
      3, 4, 4, 2, 0, 2, 3, 1, 2, 1, 3, 2],
    ![1, 1, 0, 0, 1, 1, 0, 0, 3, 0, 3, 2,
      3, 3, 4, 1, 0, 1, 3, 0, 2, 0, 3, 1],
    ![0, 0, -1, 0, 0, 1, 0, 0, 2, -1, 3, 1,
      2, 2, 3, 1, 0, 1, 3, 0, 1, 0, 3, 0],
    ![0, 0, 0, 0, 1, -1, 0, 0, -1, 0, -1, -1,
      -1, -1, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 1, 0, -1, 0, 2, -1, 3, 2,
      2, 2, 4, 0, 0, 0, 3, 1, 2, 0, 3, 1],
    ![0, 0, 0, 0, -1, 1, 0, 0, -1, 0, -1, -1,
      -1, -1, -2, 0, 0, 0, -1, -1, -1, 0, -1, 0],
    ![0, 0, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1,
      -1, -2, -2, -1, 0, -1, -2, -1, -1, -1, -2, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 0,
      -1, 0, -2, 0, 0, 0, -1, 0, -1, 0, -1, 0],
    ![2, 2, 0, 1, 1, 1, 0, 0, 3, 1, 4, 3,
      3, 3, 3, 1, 1, 1, 3, 0, 2, 1, 3, 2],
    ![-2, -2, -1, -1, -1, -1, -1, -1, -2, -1, -2, -2,
      -2, -2, -2, -1, 0, -1, -1, 0, -1, -1, -1, -2],
    ![0, 0, 1, -1, 0, 0, 0, 0, -1, 0, -1, -1,
      -1, -1, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0],
    ![0, 0, 1, 1, 0, 0, 0, 1, -1, 0, -1, 0,
      -1, -1, -1, 0, 0, 0, -1, 1, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, -1,
      -1, -1, -1, 0, 0, 0, -1, 0, -1, 0, -1, -1],
    ![0, 0, 0, 0, 0, 0, 1, 1, -1, 0, -1, -1,
      -1, -1, -1, 0, 0, 0, -1, 0, -1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1,
      0, 0, -1, 0, 0, 0, -1, -1, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2,
      2, 2, 3, 1, 0, 1, 2, 1, 2, 1, 2, 1]
  ]

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal left identity. -/
theorem generatedTwelfth_certified_matrix_01_orthogonal_left :
    generatedTwelfthCertifiedNumerator01.transpose *
      generatedTwelfthCertifiedNumerator01 =
      (4 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal right identity. -/
theorem generatedTwelfth_certified_matrix_01_orthogonal_right :
    generatedTwelfthCertifiedNumerator01 *
      generatedTwelfthCertifiedNumerator01.transpose =
      (4 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the basis identity. -/
theorem generatedTwelfth_certified_matrix_01_basis :
    generatedTwelfthCertifiedNumerator01 *
      leechBasisMatrix =
      (2 : ℤ) • (leechBasisMatrix *
      generatedTwelfthCertifiedIntegral01) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the integral inverse identity. -/
theorem generatedTwelfth_certified_matrix_01_integral_inverse :
    generatedTwelfthCertifiedIntegral01 *
      generatedTwelfthCertifiedIntegralInverse01 =
      1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
