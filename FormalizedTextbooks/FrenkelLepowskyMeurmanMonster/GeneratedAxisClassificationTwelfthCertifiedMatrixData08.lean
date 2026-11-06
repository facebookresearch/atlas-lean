/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBasisData

/-! Complete physical and integral certificates for Twelfth compact matrix 8. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedNumerator08 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegral08 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0,
      3, 3, 3, 3, 0, 3, 0, 3, 1, 5, -13, 0],
    ![0, 1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0,
      0, 0, -1, -1, 0, -1, 0, -1, 0, -1, 3, 0],
    ![0, 0, 1, 0, 0, 0, -1, 0, 0, -1, 0, 0,
      0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 2, 0],
    ![0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0,
      -1, -1, -1, -1, 0, -1, 0, -1, 0, -2, 2, 0],
    ![0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, -1, 0, -1, 3, 0],
    ![0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0,
      -1, 0, -1, -1, 0, -1, 0, 0, 0, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      -1, -1, -1, -1, 0, -1, 0, -1, -1, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0,
      0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      -1, -1, -1, -1, 0, -1, 0, -1, -1, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0,
      -1, -1, 0, -1, 0, 0, 0, -1, 0, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1, -1, -1, 0, 0, 0, 0, 0, -1, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      2, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegralInverse08 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0,
      3, 3, 3, 3, 0, 3, 0, 3, 1, 5, -13, 0],
    ![0, 1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0,
      0, 0, -1, -1, 0, -1, 0, -1, 0, -1, 3, 0],
    ![0, 0, 1, 0, 0, 0, -1, 0, 0, -1, 0, 0,
      0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 2, 0],
    ![0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0,
      -1, -1, -1, -1, 0, -1, 0, -1, 0, -2, 2, 0],
    ![0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, -1, 0, -1, 3, 0],
    ![0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0,
      -1, 0, -1, -1, 0, -1, 0, 0, 0, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      -1, -1, -1, -1, 0, -1, 0, -1, -1, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0,
      0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      -1, -1, -1, -1, 0, -1, 0, -1, -1, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0,
      -1, -1, 0, -1, 0, 0, 0, -1, 0, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1, -1, -1, 0, 0, 0, 0, 0, -1, -1, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      2, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1]
  ]

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal left identity. -/
theorem generatedTwelfth_certified_matrix_08_orthogonal_left :
    generatedTwelfthCertifiedNumerator08.transpose *
      generatedTwelfthCertifiedNumerator08 =
      (1 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal right identity. -/
theorem generatedTwelfth_certified_matrix_08_orthogonal_right :
    generatedTwelfthCertifiedNumerator08 *
      generatedTwelfthCertifiedNumerator08.transpose =
      (1 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the basis identity. -/
theorem generatedTwelfth_certified_matrix_08_basis :
    generatedTwelfthCertifiedNumerator08 *
      leechBasisMatrix =
      (1 : ℤ) • (leechBasisMatrix *
      generatedTwelfthCertifiedIntegral08) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the integral inverse identity. -/
theorem generatedTwelfth_certified_matrix_08_integral_inverse :
    generatedTwelfthCertifiedIntegral08 *
      generatedTwelfthCertifiedIntegralInverse08 =
      1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
