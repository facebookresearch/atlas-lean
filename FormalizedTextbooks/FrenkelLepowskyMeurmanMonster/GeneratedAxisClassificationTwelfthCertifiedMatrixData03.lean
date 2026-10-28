/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBasisData

/-! Complete physical and integral certificates for Twelfth compact matrix 3. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedNumerator03 : Matrix (Fin 24) (Fin 24) ℤ :=
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
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
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
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegral03 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1,
      1, -1, -1, -1, 0, 1, 1, 1, 1, 1, 1, -4],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
      0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1],
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
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  ]

/-- The complete original matrix, retaining every coordinate. -/
def generatedTwelfthCertifiedIntegralInverse03 : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1,
      1, -1, -1, -1, 0, 1, 1, 1, 1, 1, 1, -4],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
      0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0,
      0, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1],
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
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  ]

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal left identity. -/
theorem generatedTwelfth_certified_matrix_03_orthogonal_left :
    generatedTwelfthCertifiedNumerator03.transpose *
      generatedTwelfthCertifiedNumerator03 =
      (1 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the orthogonal right identity. -/
theorem generatedTwelfth_certified_matrix_03_orthogonal_right :
    generatedTwelfthCertifiedNumerator03 *
      generatedTwelfthCertifiedNumerator03.transpose =
      (1 : ℤ) • 1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the basis identity. -/
theorem generatedTwelfth_certified_matrix_03_basis :
    generatedTwelfthCertifiedNumerator03 *
      leechBasisMatrix =
      (1 : ℤ) • (leechBasisMatrix *
      generatedTwelfthCertifiedIntegral03) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all complete coordinate entries beyond the default finite certificate limit.
/-- Exact full coordinate certificate for the integral inverse identity. -/
theorem generatedTwelfth_certified_matrix_03_integral_inverse :
    generatedTwelfthCertifiedIntegral03 *
      generatedTwelfthCertifiedIntegralInverse03 =
      1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
