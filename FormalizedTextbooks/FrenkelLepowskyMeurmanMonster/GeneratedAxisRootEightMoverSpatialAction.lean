/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverSpatialData

/-! The complete positive original mover matrix follows on every genuine integral coordinate frame. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every original positive mover prefix acts on all twenty-four genuine frame columns. -/
theorem generatedRootEight_mover_spatial_prefix (n : ℕ) (hn : n < 10) (j : Fin 24) :
    (leechIntegralAction (leechNormSixHS100PointMoverPrefix n)
      (leechCoordinateFrameLattice j)).val = generatedRootEightMoverSpatialStages ⟨n, hn⟩ j := by
  induction n with
  | zero =>
      change (leechIntegralAction 1 (leechCoordinateFrameLattice j)).val = _
      rw [map_one]
      exact (generatedRootEight_mover_spatial_initial j).symm
  | succ n ih =>
      have h9 : n < 9 := by omega
      have h10 : n < 10 := by omega
      let s : Fin 9 := ⟨n, h9⟩
      rw [leechNormSixHS100PointMoverPrefix, dite_eq_left h9]
      change (leechIntegralAction
        (leechNormSixHS100PointMoverStep s * leechNormSixHS100PointMoverPrefix n)
        (leechCoordinateFrameLattice j)).val = _
      rw [map_mul, LinearEquiv.mul_apply]
      have h := leechNormSixHS100PointMover_step_action s
        (leechIntegralAction (leechNormSixHS100PointMoverPrefix n) (leechCoordinateFrameLattice j))
      rw [ih h10] at h
      have hd := generatedRootEight_mover_spatial_steps s j
      have he := h.trans hd
      have hindex : s.succ = (⟨n + 1, hn⟩ : Fin 10) := rfl
      rw [hindex] at he
      have hm : leechNormSixHS100PointMoverStepScale s = 1 ∨
          leechNormSixHS100PointMoverStepScale s = 2 := by
        unfold leechNormSixHS100PointMoverStepScale
        split_ifs <;> simp
      funext i
      have hi := congrFun he i
      rcases hm with hm | hm <;> rw [hm] at hi <;>
        simp only [Pi.smul_apply, nsmul_eq_mul] at hi <;> omega

/-- The whole positive original mover carries every coordinate frame to its certified last stage. -/
theorem generatedRootEight_mover_spatial_frame (j : Fin 24) :
    (leechIntegralAction leechNormSixHS100PointMover (leechCoordinateFrameLattice j)).val =
      generatedRootEightMoverSpatialStages 9 j :=
  generatedRootEight_mover_spatial_prefix 9 (by decide) j

set_option maxHeartbeats 8000000 in
-- Bind every real matrix entry to the complete actual original mover word.
/-- Every positive mover matrix coordinate has its exact integer numerator over eight. -/
theorem generatedRootEight_mover_spatial_matrix (i j : Fin 24) :
    leechIsomMatrix leechNormSixHS100PointMover i j =
      (generatedRootEightMoverSpatialNumerator i j : ℝ) / 8 := by
  have h := congrArg leechCoordinateEmbedding (generatedRootEight_mover_spatial_frame j)
  rw [leechIntegralAction_embedding] at h
  have hf : leechCoordinateEmbedding (leechCoordinateFrameLattice j).val =
      (8 / Real.sqrt 8 : ℝ) • Pi.single j 1 := by
    funext l
    by_cases hl : l = j <;>
      simp [leechCoordinateEmbedding, leechCoordinateFrameLattice, leechCoordinateFrameVector, hl]
  rw [hf, map_smul] at h
  have hi := congrFun h i
  change (8 / Real.sqrt 8 : ℝ) * leechIsomMatrix leechNormSixHS100PointMover i j =
      (generatedRootEightMoverSpatialNumerator i j : ℝ) / Real.sqrt 8 at hi
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  field_simp [hs] at hi
  linarith

/-- Every original physical unit follows the entire actual positive mover matrix. -/
theorem generatedRootEight_mover_spatial_unit (j i : Fin 24) :
    leechNormSixHS100PointMover.val (Pi.single j 1) i =
      (generatedRootEightMoverSpatialNumerator i j : ℝ) / 8 :=
  generatedRootEight_mover_spatial_matrix i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
