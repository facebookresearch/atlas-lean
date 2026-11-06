/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFrameAction

/-! Original forward and inverse spatial matrices follow from the frame certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original forward matrix entry is certified by an actual lattice frame vector. -/
theorem generatedNinth_forward_matrix_coordinate (i j : Fin 24) :
    leechIsomMatrix generatedNinthLocalFiber.val.2 i j =
      (generatedNinthFrameVectorData 9 j i : ℝ) / 8 := by
  have h := congrArg leechCoordinateEmbedding (generatedNinth_frame_vector_action j)
  rw [leechIntegralAction_embedding] at h
  change generatedNinthLocalFiber.val.2.val
    (leechCoordinateEmbedding (leechCoordinateFrameVector j)) =
      leechCoordinateEmbedding (generatedNinthFrameVectorData 9 j) at h
  have hf : leechCoordinateEmbedding (leechCoordinateFrameVector j) =
      (8 / Real.sqrt 8 : ℝ) • Pi.single j 1 := by
    funext k
    by_cases hk : k = j <;>
      simp [leechCoordinateEmbedding, leechCoordinateFrameVector, hk]
  rw [hf, map_smul] at h
  have hi := congrFun h i
  change (8 / Real.sqrt 8 : ℝ) * leechIsomMatrix generatedNinthLocalFiber.val.2 i j =
    (generatedNinthFrameVectorData 9 j i : ℝ) / Real.sqrt 8 at hi
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  field_simp [hs] at hi
  linarith

/-- Orthogonality gives the genuine inverse matrix with the transposed certified entries. -/
theorem generatedNinth_inverse_matrix_coordinate (i j : Fin 24) :
    leechIsomMatrix (generatedNinthLocalFiber.val.2⁻¹) i j =
      (generatedNinthFrameVectorData 9 i j : ℝ) / 8 := by
  change generatedNinthLocalFiber.val.2.val.symm (Pi.single j 1) i = _
  rw [leechIsom_inverse_coordinate]
  exact generatedNinth_forward_matrix_coordinate j i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
