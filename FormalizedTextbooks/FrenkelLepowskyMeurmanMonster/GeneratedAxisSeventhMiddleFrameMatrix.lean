/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhMiddleFrameSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhMiddleMatrixFiber

/-! The genuine middle physical matrix is determined by its original norm-eight frame vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual original spatial word sends the coordinate frame to its checked middle vector. -/
theorem generatedSeventh_middle_frame_embedding :
    generatedSeventhLocalFiber.val.2.val
      (leechCoordinateEmbedding (leechCoordinateFrameLattice 0).val) =
        leechCoordinateEmbedding (generatedSeventhFrameVectorData 7 0) := by
  have h := leechIntegralAction_embedding generatedSeventhLocalFiber.val.2
    (leechCoordinateFrameLattice 0)
  rw [generatedSeventh_frame_vector_action] at h
  exact h.symm

/-- The actual middle matrix is the fixed scalar matrix plus its genuine norm-eight outer matrix. -/
theorem generatedSeventh_middle_matrix_frame :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).1 =
      (1 / 4 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
        (1 / 4 : ℝ) • Matrix.vecMulVec
          (leechCoordinateEmbedding (generatedSeventhFrameVectorData 7 0))
          (leechCoordinateEmbedding (generatedSeventhFrameVectorData 7 0)) := by
  rw [generatedFourth_local_matrix]
  change conwayMatrixAction generatedSeventhLocalFiber.val.2
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0))).1 = _
  rw [generatedNormEightLine_odd_matrix, map_add, map_smul, map_smul, conwayMatrixAction_one]
  change (1 / 4 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
    (1 / 4 : ℝ) • conwayMatrixAction generatedSeventhLocalFiber.val.2
      (Matrix.vecMulVec (leechCoordinateEmbedding (leechCoordinateFrameLattice 0).val)
        (leechCoordinateEmbedding (leechCoordinateFrameLattice 0).val)) = _
  rw [conwayMatrixAction_vecMulVec, generatedSeventh_middle_frame_embedding]

/-- The genuine correcting sign-permutation isometry preserves the full original middle matrix. -/
theorem generatedSeventh_middle_permutation_matrix_fixed (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedSeventhTrianglePermutationSubgroup) :
    conwayMatrixAction
      (golaySignIsometry (generatedSeventhMiddlePermutationSign p) * golayPermutationIsometry p)
      (griessConwayEncode
        (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).1 =
      (griessConwayEncode
        (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).1 := by
  rw [generatedSeventh_middle_matrix_frame, map_add, map_smul, map_smul,
    conwayMatrixAction_one, conwayMatrixAction_vecMulVec,
    generatedSeventh_middle_permutation_frame_fixed p hp]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
