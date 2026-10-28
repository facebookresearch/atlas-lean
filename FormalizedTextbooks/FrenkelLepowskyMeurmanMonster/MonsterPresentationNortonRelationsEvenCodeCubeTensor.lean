/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual tensor identity for the cube of any even source code with quarter parity zero times
    source triality. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCodePhases
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationTrialitySource

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
variable (a : Fin 2048)

/-- The actual point-times-triality word for the general source-code relation. -/
noncomputable def monsterNortonEvenStep : ↥G :=
  sourceGeneratedCode ⟨a.val, by omega⟩ 0 * monsterSourceTriality

/-- Its actual X row is the signed following Y row. -/
theorem monsterNortonEvenStep_X (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv ((monsterNortonEvenStep a).val x)).2.2.2 0
      (finProdFinEquiv (d,i)) =
    (monsterNortonEvenXSign a) d i * (trialityBlocksEquiv x).2.2.2 1
      (finProdFinEquiv (d,i)) := by
  rw [monsterNortonEvenStep, Subgroup.coe_mul, LinearEquiv.mul_apply]
  change (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0))
    (sExtra⁻¹ x))).2.2.2 0 (finProdFinEquiv (d,i)) = _
  rw [monsterSourceCode_blocks_X, monsterTriality_inverse_XYZ_blocks]
  rfl

/-- Its actual Y row is the signed translated following Z row. -/
theorem monsterNortonEvenStep_Y
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (x : GriessSpace)
      (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv ((monsterNortonEvenStep a).val x)).2.2.2 1
      (finProdFinEquiv (d,i)) =
    (monsterNortonEvenYSign a) d i * (trialityBlocksEquiv x).2.2.2 2
      (finProdFinEquiv ((monsterNortonEvenCodeSum a) d,i)) := by
  rw [monsterNortonEvenStep, Subgroup.coe_mul, LinearEquiv.mul_apply]
  change (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0))
    (sExtra⁻¹ x))).2.2.2 1 (finProdFinEquiv (d,i)) = _
  rw [(monsterNortonEven_sourceCode_blocks_Y a ha), monsterTriality_inverse_XYZ_blocks]
  rfl

/-- Its actual Z row is the signed translated following X row. -/
theorem monsterNortonEvenStep_Z
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (x : GriessSpace)
      (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv ((monsterNortonEvenStep a).val x)).2.2.2 2
      (finProdFinEquiv (d,i)) =
    (monsterNortonEvenZSign a) d * (trialityBlocksEquiv x).2.2.2 0
      (finProdFinEquiv ((monsterNortonEvenCodeSum a) d,i)) := by
  rw [monsterNortonEvenStep, Subgroup.coe_mul, LinearEquiv.mul_apply]
  change (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0))
    (sExtra⁻¹ x))).2.2.2 2 (finProdFinEquiv (d,i)) = _
  rw [(monsterNortonEven_sourceCode_blocks_Z a ha), monsterTriality_inverse_XYZ_blocks]
  rfl

private theorem phase_triple (a b c x : ℝ) (ha : a = b * c)
    (hb : b * b = 1) (hc : c * c = 1) : a * (b * (c * x)) = x := by
  rw [ha]
  calc
    _ = (b * b) * (c * c) * x := by ring
    _ = x := by rw [hb, hc, one_mul, one_mul]

/-- The genuine cubic word fixes every XYZ dictionary coordinate. -/
theorem monsterNortonEvenStep_cube_XYZ
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (x : GriessSpace)
    (s : Fin 3) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (((monsterNortonEvenStep a) ^ 3).val x)).2.2.2 s
      (finProdFinEquiv (d,i)) =
      (trialityBlocksEquiv x).2.2.2 s (finProdFinEquiv (d,i)) := by
  change (trialityBlocksEquiv ((monsterNortonEvenStep a).val
    ((monsterNortonEvenStep a).val ((monsterNortonEvenStep a).val x)))).2.2.2 s _ = _
  have hc : s = 0 ∨ s = 1 ∨ s = 2 := by revert s; decide +kernel
  rcases hc with rfl | rfl | rfl
  · rw [(monsterNortonEvenStep_X a), (monsterNortonEvenStep_Y a ha), (monsterNortonEvenStep_Z a ha),
      (monsterNortonEvenCodeSum_twice a), (monsterNortonEvenZSign_sum a ha)]
    exact phase_triple _ _ _ _ ((monsterNortonEvenXSign_eq a ha) d i)
      ((monsterNortonEvenYSign_square a) d i) ((monsterNortonEvenZSign_square a ha) d)
  · rw [(monsterNortonEvenStep_Y a ha), (monsterNortonEvenStep_Z a ha), (monsterNortonEvenStep_X a),
      (monsterNortonEvenCodeSum_twice a), (monsterNortonEvenZSign_sum a ha)]
    calc
      _ = (monsterNortonEvenXSign a) d i * ((monsterNortonEvenYSign a) d i *
        ((monsterNortonEvenZSign a) d *
          (trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (d,i)))) := by ring
      _ = _ := phase_triple _ _ _ _ ((monsterNortonEvenXSign_eq a ha) d i)
        ((monsterNortonEvenYSign_square a) d i) ((monsterNortonEvenZSign_square a ha) d)
  · rw [(monsterNortonEvenStep_Z a ha), (monsterNortonEvenStep_X a), (monsterNortonEvenStep_Y a ha),
      (monsterNortonEvenCodeSum_twice a), (monsterNortonEvenXSign_sum a ha),
      (monsterNortonEvenYSign_sum a ha)]
    calc
      _ = (monsterNortonEvenXSign a) d i * ((monsterNortonEvenYSign a) d i *
        ((monsterNortonEvenZSign a) d *
          (trialityBlocksEquiv x).2.2.2 2 (finProdFinEquiv (d,i)))) := by ring
      _ = _ := phase_triple _ _ _ _ ((monsterNortonEvenXSign_eq a ha) d i)
        ((monsterNortonEvenYSign_square a) d i) ((monsterNortonEvenZSign_square a ha) d)

/-- Consequently the actual cubic word fixes the entire encoded tensor constituent. -/
theorem monsterNortonEvenStep_cube_tensor
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (x : GriessSpace) :
    (griessConwayEncode (((monsterNortonEvenStep a) ^ 3).val x)).2.2 =
      (griessConwayEncode x).2.2 := by
  funext t i
  simp only [griessConwayEncode]
  rw [(monsterNortonEvenStep_cube_XYZ a ha), (monsterNortonEvenStep_cube_XYZ a ha)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
