/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBasisData

/-! Complete physical and integral certificates for Twelfth compact matrix 11. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedNumerator11 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegral11 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 3, 3, 3, 4, -28, 3, -10,
      0, -12, 5, -11, 0, -9, 5, -11, 0, -14, 4, 0],
    ![0, 1, 0, 0, 0, 0, -1, 0, -1, 6, -1, 2,
      0, 3, -2, 2, 0, 2, -1, 2, 0, 3, -1, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, -1, 5, -1, 2,
      0, 2, -1, 2, 0, 2, -1, 2, 0, 3, -1, 0],
    ![0, 0, 0, 1, 0, -1, 0, 0, -1, 6, 0, 3,
      0, 2, -1, 3, 0, 2, -1, 3, 0, 3, -1, 0],
    ![0, 0, 0, 0, 0, 0, -1, -1, -1, 6, 0, 2,
      1, 3, -1, 3, 0, 2, -1, 2, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, -1, -1, -1, 0, 5, 0, 2,
      0, 2, -1, 2, 0, 1, -1, 2, 0, 2, -1, 0],
    ![0, 0, 0, 0, 0, -1, 0, -1, 0, 6, -1, 2,
      0, 3, -1, 2, 0, 2, -1, 2, 0, 3, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1,
      0, -1, 1, -1, 0, -1, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, -1, -1, 5, 0, 2,
      0, 2, -1, 2, 0, 1, -1, 2, 0, 2, -1, 0],
    ![0, 0, 0, 0, 0, -1, -1, -1, 0, 5, -1, 2,
      0, 2, -1, 1, 0, 1, -1, 1, 0, 2, -2, 0],
    ![0, 0, 0, 0, 0, -1, 0, -1, 0, 5, 0, 2,
      0, 2, 0, 2, 0, 2, -1, 2, 0, 3, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1,
      0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 1, 0],
    ![0, 0, 0, 0, 1, -1, -1, -1, -1, 5, -1, 1,
      0, 2, -1, 1, 0, 1, -1, 2, 0, 2, -1, 0],
    ![0, 0, 0, 0, 0, 0, 2, 1, 0, -2, 0, -1,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, -2, 0, -1,
      0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 1, 0, -2, 0, -1,
      0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 5, -1, 1,
      0, 2, -1, 2, 1, 2, -1, 2, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1,
      0, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1,
      0, -1, 0, -1, 0, -1, 1, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1,
      0, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0,
      0, 0, 1, -1, 0, 0, 1, -1, 1, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0,
      0, -1, 1, 0, 0, -1, 1, 0, 0, -1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0,
      0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2,
      0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegralInverse11 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 3, 3, 3, 4, -28, 3, -10,
      0, -12, 5, -11, 0, -9, 5, -11, 0, -14, 4, 0],
    ![0, 1, 0, 0, 0, 0, -1, 0, -1, 6, -1, 2,
      0, 3, -2, 2, 0, 2, -1, 2, 0, 3, -1, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, -1, 5, -1, 2,
      0, 2, -1, 2, 0, 2, -1, 2, 0, 3, -1, 0],
    ![0, 0, 0, 1, 0, -1, 0, 0, -1, 6, 0, 3,
      0, 2, -1, 3, 0, 2, -1, 3, 0, 3, -1, 0],
    ![0, 0, 0, 0, 0, 0, -1, -1, -1, 6, 0, 2,
      1, 3, -1, 3, 0, 2, -1, 2, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, -1, -1, -1, 0, 5, 0, 2,
      0, 2, -1, 2, 0, 1, -1, 2, 0, 2, -1, 0],
    ![0, 0, 0, 0, 0, -1, 0, -1, 0, 6, -1, 2,
      0, 3, -1, 2, 0, 2, -1, 2, 0, 3, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1,
      0, -1, 1, -1, 0, -1, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, -1, -1, 5, 0, 2,
      0, 2, -1, 2, 0, 1, -1, 2, 0, 2, -1, 0],
    ![0, 0, 0, 0, 0, -1, -1, -1, 0, 5, -1, 2,
      0, 2, -1, 1, 0, 1, -1, 1, 0, 2, -2, 0],
    ![0, 0, 0, 0, 0, -1, 0, -1, 0, 5, 0, 2,
      0, 2, 0, 2, 0, 2, -1, 2, 0, 3, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1,
      0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 1, 0],
    ![0, 0, 0, 0, 1, -1, -1, -1, -1, 5, -1, 1,
      0, 2, -1, 1, 0, 1, -1, 2, 0, 2, -1, 0],
    ![0, 0, 0, 0, 0, 0, 2, 1, 0, -2, 0, -1,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, -2, 0, -1,
      0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 1, 0, -2, 0, -1,
      0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 5, -1, 1,
      0, 2, -1, 2, 1, 2, -1, 2, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1,
      0, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1,
      0, -1, 0, -1, 0, -1, 1, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1,
      0, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0,
      0, 0, 1, -1, 0, 0, 1, -1, 1, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0,
      0, -1, 1, 0, 0, -1, 1, 0, 0, -1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0,
      0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2,
      0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1]
  ]

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal left identity. -/
theorem generatedTwelfth_certified_matrix_11_orthogonal_left :
    generatedTwelfthCertifiedNumerator11.transpose *
      generatedTwelfthCertifiedNumerator11 =
      (1 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal right identity. -/
theorem generatedTwelfth_certified_matrix_11_orthogonal_right :
    generatedTwelfthCertifiedNumerator11 *
      generatedTwelfthCertifiedNumerator11.transpose =
      (1 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the basis identity. -/
theorem generatedTwelfth_certified_matrix_11_basis :
    generatedTwelfthCertifiedNumerator11 *
      leechBasisMatrix =
      (1 : ℤ) • (leechBasisMatrix *
      generatedTwelfthCertifiedIntegral11) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the integral inverse identity. -/
theorem generatedTwelfth_certified_matrix_11_integral_inverse :
    generatedTwelfthCertifiedIntegral11 *
      generatedTwelfthCertifiedIntegralInverse11 =
      1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
