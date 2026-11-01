/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMatrixData

/-! The genuine simultaneous local lift has the explicit denominator-two spatial matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every coordinate of the original spatial lift is its checked integer numerator over two. -/
theorem generatedSeventhXiPlaneFiber_matrix_coordinate (i j : Fin 24) :
    leechIsomMatrix generatedSeventhXiPlaneFiber.val.2 i j =
      (generatedSeventhXiPlaneMatrixNumerator i j : ℝ) / 2 := by
  rw [generatedSeventhXiPlaneFiber_spatial]
  change (golayPermutationIsometry generatedSeventhXiPlanePermutation).val
      (co1XiEquiv ((golayPermutationIsometry generatedSeventhXiPlanePermutation).val.symm
        (Pi.single j 1))) i = _
  rw [generatedSeventh_permutation_inverse_single]
  change co1XiEquiv (Pi.single (generatedSeventhXiPlanePermutation.val.symm j) 1)
    (generatedSeventhXiPlanePermutation.val.symm i) = _
  rw [co1XiEquiv_apply]
  simp [Matrix.mulVec_single, co1XiMatrix, co1XiMatrixQ,
    generatedSeventhXiPlanePermutation_inverse, generatedSeventhXiPlaneMatrixNumerator]


/-- The entire genuine spatial matrix is the explicit numerator divided by two. -/
theorem generatedSeventhXiPlaneFiber_matrix :
    leechIsomMatrix generatedSeventhXiPlaneFiber.val.2 =
      (1 / 2 : ℝ) • generatedSeventhXiPlaneMatrixNumerator.map (Int.castRingHom ℝ) := by
  ext i j
  rw [generatedSeventhXiPlaneFiber_matrix_coordinate]
  change (generatedSeventhXiPlaneMatrixNumerator i j : ℝ) / 2 =
    (1 / 2 : ℝ) * generatedSeventhXiPlaneMatrixNumerator.map (Int.castRingHom ℝ) i j
  rw [show generatedSeventhXiPlaneMatrixNumerator.map (Int.castRingHom ℝ) i j =
    (generatedSeventhXiPlaneMatrixNumerator i j : ℝ) from rfl]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
