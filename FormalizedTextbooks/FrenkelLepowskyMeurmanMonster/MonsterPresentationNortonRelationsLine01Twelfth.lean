/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete next V state in the literal first Norton line-pair word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01Eleventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhVSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQScaledCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem source_lift (d : Fin 2048) (i : Fin 24) :
    monsterNortonShortLiftLinear (Pi.single (Sum.inr (Sum.inr (d, i))) 1) =
      trialityXYZBasis 0 (finProdFinEquiv (d, i)) := by
  rw [monsterNortonSourceX_pure_short, monsterNortonShortLiftLinear_apply]
  rfl

private theorem v_x82 :
    y555NortonV.val (trialityXYZBasis 0 (finProdFinEquiv ((82 : Fin 2048), (1 : Fin 24)))) =
      (-1 : ℝ) • trialityXYZBasis 0 (finProdFinEquiv ((82 : Fin 2048), (1 : Fin 24))) := by
  have hp : monsterNortonSourceXQPhase y555NortonVQ 82 1 = 1 := by
    decide +kernel
  rw [y555NortonV, monsterNortonQ_source_X, hp]
  rfl

/-- The full twelfth actual Griess state in a single short unit and one rank-one tensor. -/
noncomputable def monsterNortonLine01TwelfthVector : GriessSpace :=
  (-1 / 2 : ℝ) • trialityXYZBasis 0 (finProdFinEquiv ((82 : Fin 2048), (1 : Fin 24))) +
    (1 / (8 * Real.sqrt 2) : ℝ) •
      monsterNortonTensorRankOne (monsterNortonUFiber.val.2.val (Pi.single 0 1))
        (nortonUIntegerEmbed monsterNortonLine01EleventhVSpinVector)

/-- Literal Norton V takes the entire proved eleventh state to this entire twelfth state. -/
theorem monsterNortonLine01Twelfth_actual :
    y555NortonV.val monsterNortonLine01EleventhVector = monsterNortonLine01TwelfthVector := by
  rw [monsterNortonLine01EleventhVector, map_add, map_smul, source_lift, map_smul, v_x82,
    monsterNortonLine01EleventhTensorVector, map_smul]
  have ht : y555NortonV.val
      (monsterNortonTensorRankOne (monsterNortonUFiber.val.2.val (Pi.single 0 1))
        (nortonUIntegerEmbed monsterNortonLine01EleventhSpinVector)) =
      monsterNortonTensorRankOne (monsterNortonUFiber.val.2.val (Pi.single 0 1))
        (nortonUIntegerEmbed monsterNortonLine01EleventhVSpinVector) := by
    change (qIntoGenerated y555NortonVQ).val
      (monsterNortonTensorLift (conwayTensorCoordinates _)) = _
    rw [monsterNortonQ_integer_rank_one, monsterNortonLine01EleventhVSpin_actual]
    rfl
  rw [ht, smul_smul]
  norm_num [monsterNortonLine01TwelfthVector]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
