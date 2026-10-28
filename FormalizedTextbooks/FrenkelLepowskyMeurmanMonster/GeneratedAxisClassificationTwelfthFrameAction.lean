/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthFrameData

/-! All certified physical frame columns come from the genuine original spatial word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
-- Comparing the full seven-stage original spatial word needs a deeper elaboration stack.
set_option maxRecDepth 10000

private theorem stage_action (s : Fin 7) (j : Fin 24) (u : leechIntegral)
    (hu : u.val = generatedTwelfthFrameData s.castSucc j) :
    (leechIntegralAction (generatedAxisGlobalFifthShortNormalizationSpatial 9 s) u).val =
      generatedTwelfthFrameData s.succ j := by
  let v := leechIntegralAction
    (golaySignIsometry
      (sourceGeneratedSignCode (generatedAxisGlobalFifthShortNormalizationSigns 9 s)) *
      golayPermutationIsometry (generatedAxisGlobalFifthShortNormalizationPermutation 9 s)) u
  have hv : v.val = golayIntegerSign
      (sourceGeneratedSignCode (generatedAxisGlobalFifthShortNormalizationSigns 9 s)).val
      (golayIntegerPermute (generatedAxisGlobalFifthShortNormalizationPermutation 9 s).val
        (generatedTwelfthFrameData s.castSucc j)) := by
    dsimp [v]
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation, hu]
  have hs := generatedTwelfth_frame_step s j
  rw [← hv] at hs
  rw [generatedAxisGlobalFifthShortNormalizationSpatial, map_mul, LinearEquiv.mul_apply]
  change (leechIntegralAction
    (if generatedAxisGlobalFifthShortNormalizationXi 9 s then co1XiIsometry else 1) v).val = _
  cases hx : generatedAxisGlobalFifthShortNormalizationXi 9 s with
  | false =>
    simp only [hx, Bool.false_eq_true, ↓reduceIte, map_one] at hs ⊢
    exact hs
  | true =>
    simp only [hx, ↓reduceIte] at hs ⊢
    have h := co1Xi_integral_double v
    rw [hs] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.smul_apply, nsmul_eq_mul] at hi
    omega

private theorem prefix_action (n : ℕ) (hn : n < 8) (j : Fin 24) :
    (leechIntegralAction
      (generatedAxisGlobalWordChain (fun s => generatedAxisGlobalFifthShortNormalizationSpatial
        9 ⟨s % 7, Nat.mod_lt _ (by decide)⟩) n) (leechCoordinateFrameLattice j)).val =
      generatedTwelfthFrameData ⟨n, hn⟩ j := by
  induction n with
  | zero =>
    rw [generatedAxisGlobalWordChain, map_one]
    change leechCoordinateFrameVector j = generatedTwelfthFrameData 0 j
    exact (generatedTwelfth_frame_initial j).symm
  | succ n ih =>
    rw [generatedAxisGlobalWordChain, map_mul, LinearEquiv.mul_apply]
    have hp := stage_action ⟨n, by omega⟩ j _ (ih (by omega))
    have he : (⟨n, by omega⟩ : Fin 7).succ = (⟨n + 1, hn⟩ : Fin 8) := by
      apply Fin.ext
      rfl
    rw [he] at hp
    simpa only [Nat.mod_eq_of_lt (show n < 7 by omega)] using hp

/-- Every physical coordinate frame has its certified genuine spatial image. -/
theorem generatedTwelfth_frame_action (j : Fin 24) :
    (leechIntegralAction (generatedAxisGlobalFifthShortSpatialWord 9)
      (leechCoordinateFrameLattice j)).val = generatedTwelfthFrameData 7 j := by
  exact prefix_action 7 (by decide) j

set_option maxHeartbeats 8000000 in
-- Unfolding the complete original seven-stage spatial word requires this budget.
/-- The actual forward spatial matrix has precisely the integer frame entries. -/
theorem generatedTwelfth_forward_matrix_coordinate (i j : Fin 24) :
    leechIsomMatrix (generatedAxisGlobalFifthShortSpatialWord 9) i j =
      (generatedTwelfthFrameData 7 j i : ℝ) / 8 := by
  have h := congrArg leechCoordinateEmbedding (generatedTwelfth_frame_action j)
  rw [leechIntegralAction_embedding] at h
  have hf : leechCoordinateEmbedding (leechCoordinateFrameLattice j).val =
      (8 / Real.sqrt 8 : ℝ) • Pi.single j 1 := by
    funext l
    by_cases hl : l = j <;>
      simp [leechCoordinateEmbedding, leechCoordinateFrameLattice, leechCoordinateFrameVector, hl]
  rw [hf, map_smul] at h
  have hi := congrFun h i
  change (8 / Real.sqrt 8 : ℝ) * leechIsomMatrix
    (generatedAxisGlobalFifthShortSpatialWord 9) i j =
      (generatedTwelfthFrameData 7 j i : ℝ) / Real.sqrt 8 at hi
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  field_simp [hs] at hi
  linarith

set_option maxHeartbeats 8000000 in
-- The inverse coordinate comparison retains the same complete original source word.
/-- The genuine inverse spatial matrix has the transposed certified frame entries. -/
theorem generatedTwelfth_inverse_matrix_coordinate (i j : Fin 24) :
    leechIsomMatrix (generatedAxisGlobalFifthShortSpatialWord 9)⁻¹ i j =
      (generatedTwelfthFrameData 7 i j : ℝ) / 8 := by
  change (generatedAxisGlobalFifthShortSpatialWord 9).val.symm (Pi.single j 1) i = _
  rw [leechIsom_inverse_coordinate]
  exact generatedTwelfth_forward_matrix_coordinate j i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
