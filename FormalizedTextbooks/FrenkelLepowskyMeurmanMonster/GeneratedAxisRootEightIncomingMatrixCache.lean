/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortInteger

/-! An exact full integer cache of the original incoming matrix sums. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- All twenty-four by twenty-four original incoming matrix numerators. -/
def generatedRootEightIncomingMatrixCachedNumerator : Fin 24 → Fin 24 → ℤ :=
![
![80, 8, 8, 16, 0, 0, 0, 0, -8, 0, 0, 8, 0, 0, 0, 0, 0, 0, 8, -8, -8, 0, -8, 0],
![8, 96, 0, 8, 8, 8, -8, -8, 0, 8, -8, 0, -8, -8, -8, -8, 8, -8, 0, 0, 0, -8, 0, -8],
![8, 0, 96, 8, -8, -8, 8, 8, 0, 8, -8, 0, 8, 8, 8, 8, 8, -8, 0, 0, 0, -8, 0, -8],
![16, 8, 8, 80, 0, 0, 0, 0, -8, 0, 0, 8, 0, 0, 0, 0, 0, 0, 8, -8, -8, 0, -8, 0],
![0, 8, -8, 0, 80, 0, 0, 0, 8, 0, 0, 8, 0, -16, 0, 0, 0, 0, 8, 8, -8, 0, 8, 0],
![0, 8, -8, 0, 0, 80, 0, 0, -8, 0, 0, -8, 0, 0, 0, -16, 0, 0, -8, -8, -8, 0, 8, 0],
![0, -8, 8, 0, 0, 0, 80, 0, 8, 0, 0, 8, 16, 0, 0, 0, 0, 0, -8, -8, -8, 0, 8, 0],
![0, -8, 8, 0, 0, 0, 0, 80, -8, 0, 0, -8, 0, 0, 16, 0, 0, 0, 8, 8, -8, 0, 8, 0],
![-8, 0, 0, -8, 8, -8, 8, -8, 96, -8, 8, 0, 8, -8, -8, 8, 8, -8, 0, 0, 0, -8, 0, -8],
![0, 8, 8, 0, 0, 0, 0, 0, -8, 80, -16, 8, 0, 0, 0, 0, 0, 0, -8, 8, 8, 0, 8, 0],
![0, -8, -8, 0, 0, 0, 0, 0, 8, -16, 80, -8, 0, 0, 0, 0, 0, 0, 8, -8, -8, 0, -8, 0],
![8, 0, 0, 8, 8, -8, 8, -8, 0, 8, -8, 96, 8, -8, -8, 8, -8, 8, 0, 0, 0, 8, 0, 8],
![0, -8, 8, 0, 0, 0, 16, 0, 8, 0, 0, 8, 80, 0, 0, 0, 0, 0, -8, -8, -8, 0, 8, 0],
![0, -8, 8, 0, -16, 0, 0, 0, -8, 0, 0, -8, 0, 80, 0, 0, 0, 0, -8, -8, 8, 0, -8, 0],
![0, -8, 8, 0, 0, 0, 0, 16, -8, 0, 0, -8, 0, 0, 80, 0, 0, 0, 8, 8, -8, 0, 8, 0],
![0, -8, 8, 0, 0, -16, 0, 0, 8, 0, 0, 8, 0, 0, 0, 80, 0, 0, 8, 8, 8, 0, -8, 0],
![0, 8, 8, 0, 0, 0, 0, 0, 8, 0, 0, -8, 0, 0, 0, 0, 80, -16, 8, -8, 8, 0, 8, 0],
![0, -8, -8, 0, 0, 0, 0, 0, -8, 0, 0, 8, 0, 0, 0, 0, -16, 80, -8, 8, -8, 0, -8, 0],
![8, 0, 0, 8, 8, -8, -8, 8, 0, -8, 8, 0, -8, -8, 8, 8, 8, -8, 96, 0, 0, 8, 0, 8],
![-8, 0, 0, -8, 8, -8, -8, 8, 0, 8, -8, 0, -8, -8, 8, 8, -8, 8, 0, 96, 0, -8, 0, -8],
![-8, 0, 0, -8, -8, -8, -8, -8, 0, 8, -8, 0, -8, 8, -8, 8, 8, -8, 0, 0, 96, 8, 0, 8],
![0, -8, -8, 0, 0, 0, 0, 0, -8, 0, 0, 8, 0, 0, 0, 0, 0, 0, 8, -8, 8, 80, 8, 16],
![-8, 0, 0, -8, 8, 8, 8, 8, 0, 8, -8, 0, 8, -8, 8, -8, 8, -8, 0, 0, 0, 8, 96, 8],
![0, -8, -8, 0, 0, 0, 0, 0, -8, 0, 0, 8, 0, 0, 0, 0, 0, 0, 8, -8, 8, 16, 8, 80]
]

set_option maxHeartbeats 8000000 in
-- Verify every complete twenty-four-column original matrix sum.
/-- The finite cache equals the full original integer matrix formula at every coordinate. -/
theorem generatedRootEight_incoming_matrix_numerator_cache : ∀ i j : Fin 24,
    generatedRootEightIncomingMatrixNumerator i j =
      generatedRootEightIncomingMatrixCachedNumerator i j := by
  decide +kernel

/-- Every actual incoming matrix coordinate has its proved cached integer numerator. -/
theorem generatedRootEight_incoming_positive_matrix_cached (i j : Fin 24) :
    (griessConwayEncode generatedRootEightIncomingPositiveDestination).1 i j =
      (generatedRootEightIncomingMatrixCachedNumerator i j : ℝ) / 256 := by
  rw [generatedRootEight_incoming_positive_matrix_integer,
    generatedRootEight_incoming_matrix_numerator_cache]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
