/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The first actual V and U steps for the pair-short line-square test. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQShortDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Evaluate the full central coefficient and all 24 binary coordinates through the true U cache.
/-- The actual source U sends this preferred pair lift to the indicated preferred octad lift. -/
theorem monsterNortonLine01PairU_Q_image :
    spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ monsterNortonLine01PairShortInput) =
        monsterNortonShortQ monsterNortonLine01PairUShortOutput := by
  rw [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq]
  unfold monsterNortonShortQ
  rw [monsterNortonLine01PairShortIntegral_actual, monsterNortonLine01PairUShortIntegral_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · funext i
    revert i
    decide +kernel
  · decide +kernel

private def rawShortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] ConwayRawSpace where
  toFun X := (0, (X, 0))
  map_add' X Y := by simp only [Prod.mk_add_mk, zero_add]
  map_smul' c X := by simp only [RingHom.id_apply, Prod.smul_mk, smul_zero]

private noncomputable def shortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp rawShortLift

private theorem short_scale (c : ℝ) (X : GriessShortIndex → ℝ) :
    griessConwayDecode (0, (c • X, 0)) = c • griessConwayDecode (0, (X, 0)) :=
  shortLift.map_smul c X

private theorem v_phase :
    qBeta (toAdd y555NortonVQ.base)
        (toAdd (monsterNortonShortQ monsterNortonLine01PairShortInput).base) +
      qBeta (toAdd (monsterNortonShortQ monsterNortonLine01PairShortInput).base)
        (toAdd y555NortonVQ.base) = 1 := by
  unfold monsterNortonShortQ
  rw [monsterNortonLine01PairShortIntegral_actual]
  decide +kernel

/-- Literal V acts on this entire pair-short unit by its true negative sign. -/
theorem monsterNortonLine01PairV_actual :
    y555NortonV.val (monsterNortonPureShort monsterNortonLine01PairShortInput) =
      (-1 : ℝ) • monsterNortonPureShort monsterNortonLine01PairShortInput := by
  rw [y555NortonV, monsterNortonPureShort]
  change localGriessRepresentation (localFiberIncl y555NortonVQ)
    (griessConwayDecode (0, (Pi.single monsterNortonLine01PairShortInput 1, 0))) = _
  have hc : spinConjugation (localFiberIncl y555NortonVQ).val.1
      (monsterNortonShortQ monsterNortonLine01PairShortInput) =
        qCentral 1 * monsterNortonShortQ monsterNortonLine01PairShortInput := by
    change spinConjugation (spinHolomorphIncl y555NortonVQ) _ = _
    rw [spinConjugation_incl, q_conjugation_central_phase, v_phase]
  have hd := monsterNortonGriessShortBasis_of_Q_image (localFiberIncl y555NortonVQ)
    monsterNortonLine01PairShortInput monsterNortonLine01PairShortInput 1 hc
  change _ = griessConwayDecode
    (0, ((-1 : ℝ) • Pi.single monsterNortonLine01PairShortInput 1, 0)) at hd
  exact hd.trans (short_scale (-1) (Pi.single monsterNortonLine01PairShortInput 1))

/-- The full actual U action takes the pair-short unit to its phase-correct octad-short unit. -/
theorem monsterNortonLine01PairU_actual :
    y555NortonActualU.val (monsterNortonPureShort monsterNortonLine01PairShortInput) =
      monsterNortonPureShort monsterNortonLine01PairUShortOutput := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (griessConwayDecode (0, (Pi.single monsterNortonLine01PairShortInput 1, 0))) =
      griessConwayDecode (0, (Pi.single monsterNortonLine01PairUShortOutput 1, 0))
  have h := monsterNortonGriessShortBasis_of_Q_image monsterNortonUFiber
    monsterNortonLine01PairShortInput monsterNortonLine01PairUShortOutput 0
    (by rw [show qCentral 0 = (1 : Q) from rfl, one_mul]; exact monsterNortonLine01PairU_Q_image)
  simpa only [qSign_zero, one_smul] using h

/-- The first two literal operators produce the entire negative octad-short vector. -/
theorem monsterNortonLine01PairVU_actual :
    y555NortonActualU.val
      (y555NortonV.val (monsterNortonPureShort monsterNortonLine01PairShortInput)) =
        (-1 : ℝ) • monsterNortonPureShort monsterNortonLine01PairUShortOutput := by
  rw [monsterNortonLine01PairV_actual, map_smul, monsterNortonLine01PairU_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
