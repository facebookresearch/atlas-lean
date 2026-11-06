/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete inverse-U transport of the twelfth actual Norton word state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01Twelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhVSpinInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem inverse_leech_cancel (f : localFiberSubgroup) (b : Fin 24 → ℝ) :
    (f.val.2⁻¹).val (f.val.2.val b) = b := f.val.2.val.symm_apply_apply b

private theorem inverse_rank_one (v : NortonUIntegerVector) (b : Fin 24 → ℝ) :
    (y555NortonActualU⁻¹).val (monsterNortonTensorRankOne b (nortonUIntegerEmbed v)) =
      monsterNortonTensorRankOne ((monsterNortonUFiber.val.2⁻¹).val b)
        ((monsterNortonUFiber.val.1⁻¹).val (nortonUIntegerEmbed v)) := by
  rw [← monsterNortonULocal_generated, ← map_inv]
  change localGriessRepresentation (monsterNortonUFiber⁻¹)
    (monsterNortonTensorLift (conwayTensorCoordinates _)) = _
  exact monsterNortonLocal_tensor_product_actual _ _ _

private theorem short_scale (c : ℝ) (X : GriessShortIndex → ℝ) :
    griessConwayDecode (0, (c • X, 0)) = c • griessConwayDecode (0, (X, 0)) :=
  monsterNortonShortLiftLinear.map_smul c X

private theorem inverse_x82 :
    (y555NortonActualU⁻¹).val
      (trialityXYZBasis 0 (finProdFinEquiv ((82 : Fin 2048), (1 : Fin 24)))) =
        (-1 : ℝ) • trialityXYZBasis 0
          (finProdFinEquiv ((1038 : Fin 2048), (0 : Fin 24))) := by
  have hc : monsterNortonLine01ShortInputCode 50 = 82 := by decide +kernel
  have hi : monsterNortonLine01ShortPhysicalColumn 1 = 1 := by decide +kernel
  have ho : monsterNortonLine01ShortInverseOutput 50 1 =
      Sum.inr (Sum.inr ((1038 : Fin 2048), (0 : Fin 24))) := by decide +kernel
  have hp : monsterNortonLine01ShortInversePhase 50 1 = 1 := by decide +kernel
  have h := monsterNortonLine01ShortInverse_actual 50 1
  rw [hc, hi, ho, hp] at h
  rw [h, monsterNortonSourceX_pure_short]
  exact short_scale (-1) _

/-- The entire thirteenth vector in one source X unit and the two surviving spin deltas. -/
noncomputable def monsterNortonLine01ThirteenthVector : GriessSpace :=
  (1 / 2 : ℝ) • trialityXYZBasis 0 (finProdFinEquiv ((1038 : Fin 2048), (0 : Fin 24))) +
    (-1 / (2 * Real.sqrt 2) : ℝ) • monsterNortonTensorRankOne (Pi.single 0 1)
      (nortonUIntegerEmbed monsterNortonLine01ThirteenthSpinVector)

/-- The whole actual inverse Norton U action has the verified thirteenth-state formula. -/
theorem monsterNortonLine01Thirteenth_actual :
    (y555NortonActualU⁻¹).val monsterNortonLine01TwelfthVector =
      monsterNortonLine01ThirteenthVector := by
  rw [monsterNortonLine01TwelfthVector, map_add, map_smul, inverse_x82, map_smul,
    inverse_rank_one, inverse_leech_cancel, monsterNortonLine01EleventhVSpin_inverse_embed,
    map_smul, smul_smul, smul_smul]
  have h1 : (-1 / 2 : ℝ) * -1 = 1 / 2 := by norm_num
  have h2 : (1 / (8 * Real.sqrt 2) : ℝ) * -4 = -1 / (2 * Real.sqrt 2) := by ring
  rw [h1, h2]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
