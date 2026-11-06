/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBasisData

/-! Complete physical and integral certificates for Twelfth compact matrix 10. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedNumerator10 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegral10 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0,
      4, 4, -12, 5, 0, 3, 0, 3, 0, 5, 3, 0],
    ![0, 1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0,
      -1, -1, 2, -2, 0, -1, 0, -1, 0, -1, -1, 0],
    ![0, 0, 1, 0, 0, 0, -1, 0, 0, -1, 0, 0,
      -1, -1, 2, -2, 0, -1, 0, -1, 0, -1, -1, 0],
    ![0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0,
      -1, -1, 2, -1, 0, -1, 0, -1, 0, -2, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0,
      -1, -1, 3, -1, 0, 0, 0, -1, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, -1, 3, 0, 0, -1, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      0, -1, 3, -1, 0, -1, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1,
      0, 1, -1, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0,
      -1, 0, 2, -1, 0, -1, 0, 0, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      0, 0, 2, -1, 0, -1, 0, -1, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0, 0, 2, 0, 0, 0, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1, -1, 2, -1, 0, 0, 0, 0, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1, -1, 2, -1, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      2, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegralInverse10 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0,
      4, 4, -12, 5, 0, 3, 0, 3, 0, 5, 3, 0],
    ![0, 1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0,
      -1, -1, 2, -2, 0, -1, 0, -1, 0, -1, -1, 0],
    ![0, 0, 1, 0, 0, 0, -1, 0, 0, -1, 0, 0,
      -1, -1, 2, -2, 0, -1, 0, -1, 0, -1, -1, 0],
    ![0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0,
      -1, -1, 2, -1, 0, -1, 0, -1, 0, -2, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0,
      -1, -1, 3, -1, 0, 0, 0, -1, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, -1, 3, 0, 0, -1, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      0, -1, 3, -1, 0, -1, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1,
      0, 1, -1, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0,
      -1, 0, 2, -1, 0, -1, 0, 0, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
      0, 0, 2, -1, 0, -1, 0, -1, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0, 0, 2, 0, 0, 0, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1, -1, 2, -1, 0, 0, 0, 0, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1, -1, 2, -1, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      2, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  ]

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal left identity. -/
theorem generatedTwelfth_certified_matrix_10_orthogonal_left :
    generatedTwelfthCertifiedNumerator10.transpose *
      generatedTwelfthCertifiedNumerator10 =
      (1 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal right identity. -/
theorem generatedTwelfth_certified_matrix_10_orthogonal_right :
    generatedTwelfthCertifiedNumerator10 *
      generatedTwelfthCertifiedNumerator10.transpose =
      (1 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the basis identity. -/
theorem generatedTwelfth_certified_matrix_10_basis :
    generatedTwelfthCertifiedNumerator10 *
      leechBasisMatrix =
      (1 : ℤ) • (leechBasisMatrix *
      generatedTwelfthCertifiedIntegral10) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the integral inverse identity. -/
theorem generatedTwelfth_certified_matrix_10_integral_inverse :
    generatedTwelfthCertifiedIntegral10 *
      generatedTwelfthCertifiedIntegralInverse10 =
      1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
