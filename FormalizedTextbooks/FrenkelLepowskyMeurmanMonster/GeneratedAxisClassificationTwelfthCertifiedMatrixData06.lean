/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBasisData

/-! Complete physical and integral certificates for Twelfth compact matrix 6. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedNumerator06 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegral06 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 1, -2, 0, 1, 0, -2,
      0, -2, -2, 1, 0, 1, 0, 1, 0, 1, -3, 8],
    ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, -2],
    ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1,
      0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegralInverse06 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 1, -2, 0, 1, 0, -2,
      0, -2, -2, 1, 0, 1, 0, 1, 0, 1, -3, 8],
    ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, -2],
    ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1,
      0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]
  ]

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal left identity. -/
theorem generatedTwelfth_certified_matrix_06_orthogonal_left :
    generatedTwelfthCertifiedNumerator06.transpose *
      generatedTwelfthCertifiedNumerator06 =
      (1 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal right identity. -/
theorem generatedTwelfth_certified_matrix_06_orthogonal_right :
    generatedTwelfthCertifiedNumerator06 *
      generatedTwelfthCertifiedNumerator06.transpose =
      (1 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the basis identity. -/
theorem generatedTwelfth_certified_matrix_06_basis :
    generatedTwelfthCertifiedNumerator06 *
      leechBasisMatrix =
      (1 : ℤ) • (leechBasisMatrix *
      generatedTwelfthCertifiedIntegral06) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the integral inverse identity. -/
theorem generatedTwelfth_certified_matrix_06_integral_inverse :
    generatedTwelfthCertifiedIntegral06 *
      generatedTwelfthCertifiedIntegralInverse06 =
      1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
