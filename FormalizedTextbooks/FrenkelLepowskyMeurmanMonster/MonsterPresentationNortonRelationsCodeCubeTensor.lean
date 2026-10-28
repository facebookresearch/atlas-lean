/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual tensor identity for the cube of Norton's initial point times source triality. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodePhases

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual point-times-triality word for the adjacent first-line relation. -/
noncomputable def monsterNortonInitialStep : ↥G :=
  sourceGeneratedCode 1024 0 * monsterSourceTriality

/-- Its actual X row is the signed following Y row. -/
theorem monsterNortonInitialStep_X (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (monsterNortonInitialStep.val x)).2.2.2 0
      (finProdFinEquiv (d,i)) =
    monsterNortonInitialXSign d i * (trialityBlocksEquiv x).2.2.2 1
      (finProdFinEquiv (d,i)) := by
  change (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode 1024 0)) (sExtra⁻¹ x))).2.2.2 0
    (finProdFinEquiv (d,i)) = _
  rw [monsterSourceCode_blocks_X, monsterTriality_inverse_XYZ_blocks]
  rfl

/-- Its actual Y row is the signed translated following Z row. -/
theorem monsterNortonInitialStep_Y (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (monsterNortonInitialStep.val x)).2.2.2 1
      (finProdFinEquiv (d,i)) =
    monsterNortonInitialYSign d i * (trialityBlocksEquiv x).2.2.2 2
      (finProdFinEquiv (monsterNortonInitialCodeSum d,i)) := by
  change (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode 1024 0)) (sExtra⁻¹ x))).2.2.2 1
    (finProdFinEquiv (d,i)) = _
  rw [monsterNortonInitial_sourceCode_blocks_Y, monsterTriality_inverse_XYZ_blocks]
  rfl

/-- Its actual Z row is the signed translated following X row. -/
theorem monsterNortonInitialStep_Z (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (monsterNortonInitialStep.val x)).2.2.2 2
      (finProdFinEquiv (d,i)) =
    monsterNortonInitialZSign d * (trialityBlocksEquiv x).2.2.2 0
      (finProdFinEquiv (monsterNortonInitialCodeSum d,i)) := by
  change (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode 1024 0)) (sExtra⁻¹ x))).2.2.2 2
    (finProdFinEquiv (d,i)) = _
  rw [monsterNortonInitial_sourceCode_blocks_Z, monsterTriality_inverse_XYZ_blocks]
  rfl

private theorem phase_triple (a b c x : ℝ) (ha : a = b * c)
    (hb : b * b = 1) (hc : c * c = 1) : a * (b * (c * x)) = x := by
  rw [ha]
  calc
    _ = (b * b) * (c * c) * x := by ring
    _ = x := by rw [hb, hc, one_mul, one_mul]

/-- The genuine cubic word fixes every XYZ dictionary coordinate. -/
theorem monsterNortonInitialStep_cube_XYZ (x : GriessSpace)
    (a : Fin 3) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv ((monsterNortonInitialStep ^ 3).val x)).2.2.2 a
      (finProdFinEquiv (d,i)) =
      (trialityBlocksEquiv x).2.2.2 a (finProdFinEquiv (d,i)) := by
  change (trialityBlocksEquiv (monsterNortonInitialStep.val
    (monsterNortonInitialStep.val (monsterNortonInitialStep.val x)))).2.2.2 a _ = _
  have hc : a = 0 ∨ a = 1 ∨ a = 2 := by revert a; decide +kernel
  rcases hc with rfl | rfl | rfl
  · rw [monsterNortonInitialStep_X, monsterNortonInitialStep_Y, monsterNortonInitialStep_Z,
      monsterNortonInitialCodeSum_twice, monsterNortonInitialZSign_sum]
    exact phase_triple _ _ _ _ (monsterNortonInitialXSign_eq d i)
      (monsterNortonInitialYSign_square d i) (monsterNortonInitialZSign_square d)
  · rw [monsterNortonInitialStep_Y, monsterNortonInitialStep_Z, monsterNortonInitialStep_X,
      monsterNortonInitialCodeSum_twice, monsterNortonInitialZSign_sum]
    calc
      _ = monsterNortonInitialXSign d i * (monsterNortonInitialYSign d i *
        (monsterNortonInitialZSign d *
          (trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (d,i)))) := by ring
      _ = _ := phase_triple _ _ _ _ (monsterNortonInitialXSign_eq d i)
        (monsterNortonInitialYSign_square d i) (monsterNortonInitialZSign_square d)
  · rw [monsterNortonInitialStep_Z, monsterNortonInitialStep_X, monsterNortonInitialStep_Y,
      monsterNortonInitialCodeSum_twice, monsterNortonInitialXSign_sum,
      monsterNortonInitialYSign_sum]
    calc
      _ = monsterNortonInitialXSign d i * (monsterNortonInitialYSign d i *
        (monsterNortonInitialZSign d *
          (trialityBlocksEquiv x).2.2.2 2 (finProdFinEquiv (d,i)))) := by ring
      _ = _ := phase_triple _ _ _ _ (monsterNortonInitialXSign_eq d i)
        (monsterNortonInitialYSign_square d i) (monsterNortonInitialZSign_square d)

/-- Consequently the actual cubic word fixes the entire encoded tensor constituent. -/
theorem monsterNortonInitialStep_cube_tensor (x : GriessSpace) :
    (griessConwayEncode ((monsterNortonInitialStep ^ 3).val x)).2.2 =
      (griessConwayEncode x).2.2 := by
  funext t i
  simp only [griessConwayEncode]
  rw [monsterNortonInitialStep_cube_XYZ, monsterNortonInitialStep_cube_XYZ]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
