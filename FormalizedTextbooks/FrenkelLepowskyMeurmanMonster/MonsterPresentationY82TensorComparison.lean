/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full matrix and spin-tensor source-word comparison for the actual y82 candidate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82ZRow

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both spin parity halves agree, so the entire genuine tensor constituent agrees. -/
theorem monsterSourceY82_tensor_match (x : GriessSpace) :
    (griessConwayEncode (rhoLocal monsterSourceY82Local x)).2.2 =
      (griessConwayEncode
        ((sExtra * rhoLocal (inclQ (sourceQCode 82 0)) * sExtra⁻¹) x)).2.2 := by
  funext t i
  simp only [griessConwayEncode]
  rw [monsterSourceY82_blocks_Y_match, monsterSourceY82_blocks_Z_match]

/-- The genuine lattice sign fixes every actual diagonal matrix coordinate. -/
theorem monsterSourceY82_diagonal (x : GriessSpace) (i : Fin 24) :
    (trialityBlocksEquiv (rhoLocal monsterSourceY82Local x)).1 i =
      (trialityBlocksEquiv x).1 i := by
  have h := localGriessRepresentation_encode monsterSourceY82Fiber x
  have hm := congrArg (fun b : ConwayRawSpace => b.1) h
  change (griessConwayEncode (rhoLocal monsterSourceY82Local x)).1 =
    conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode 82))
      (griessConwayEncode x).1 at hm
  have hi := congrFun (congrFun hm i) i
  rw [sourceGeneratedSign_matrix_apply, CharTwo.add_self_eq_zero, qSign_zero, one_mul] at hi
  simpa only [griessConwayEncode, dite_true] using hi

/-- Actual triality fixes the diagonal part of the dictionary. -/
theorem monsterY82_triality_diagonal (x : GriessSpace) :
    (trialityBlocksEquiv (sExtra x)).1 = (trialityBlocksEquiv x).1 := by
  simp only [sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, trialityBlockAction, LinearEquiv.prodCongr_apply]
  rfl

/-- Inverse triality fixes the same actual diagonal part. -/
theorem monsterY82_triality_inverse_diagonal (x : GriessSpace) :
    (trialityBlocksEquiv (sExtra⁻¹ x)).1 = (trialityBlocksEquiv x).1 := by
  have h := monsterY82_triality_diagonal (sExtra.symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The literal source y82 word fixes every actual diagonal coordinate. -/
theorem monsterY82_sourceWord_diagonal (x : GriessSpace) (i : Fin 24) :
    (trialityBlocksEquiv
      ((sExtra * rhoLocal (inclQ (sourceQCode 82 0)) * sExtra⁻¹) x)).1 i =
        (trialityBlocksEquiv x).1 i := by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, monsterY82_triality_diagonal,
    sourceQCode_blocks_diagonal, monsterY82_triality_inverse_diagonal]

/-- The complete physical matrix constituent agrees with the literal source word. -/
theorem monsterSourceY82_matrix_match (x : GriessSpace) :
    (griessConwayEncode (rhoLocal monsterSourceY82Local x)).1 =
      (griessConwayEncode
        ((sExtra * rhoLocal (inclQ (sourceQCode 82 0)) * sExtra⁻¹) x)).1 := by
  funext i j
  by_cases hij : i = j
  · subst j
    simp only [griessConwayEncode, dite_true, monsterSourceY82_diagonal,
      monsterY82_sourceWord_diagonal]
  · simp only [griessConwayEncode, hij, dite_false]
    exact monsterSourceY82_blocks_ABC_match x 0 (griessPairIndex i j hij)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
