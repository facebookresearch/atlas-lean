/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Norton V phases on the complete inverse-U pair and octad packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIdentity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsVBinaryCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Central phases of literal V on all original inverse-image short labels. -/
def monsterNortonLine01PairInverseVPhase : Fin 64 → ZMod 2 :=
  ![
    1, 0, 1, 1, 1, 1, 0, 1,
    1, 1, 0, 1, 0, 1, 0, 0,
    1, 1, 0, 1, 0, 1, 0, 0,
    0, 1, 0, 0, 0, 0, 1, 0,
    0, 0, 1, 0, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 1, 0, 1,
    1, 0, 1, 1, 1, 1, 0, 1,
    1, 1, 0, 1, 0, 1, 0, 0]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Evaluate the actual polar form after the proved binary-mask and physical-coordinate transports.
/-- Every tabulated V sign is the full actual Q conjugation phase of that shortest vector. -/
theorem monsterNortonLine01PairInverseVPhase_actual (e : Fin 64) :
    qBeta (toAdd y555NortonVQ.base)
        (toAdd (monsterNortonShortQ (monsterNortonLine01PairInverseShortOutput e)).base) +
      qBeta (toAdd (monsterNortonShortQ (monsterNortonLine01PairInverseShortOutput e)).base)
        (toAdd y555NortonVQ.base) = monsterNortonLine01PairInverseVPhase e := by
  rw [monsterNortonVBinaryCoordinates_actual]
  unfold monsterNortonShortQ
  rw [monsterNortonLine01PairInverseShortIntegral_actual]
  fin_cases e <;> decide +kernel

private def rawShortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] ConwayRawSpace where
  toFun X := (0, (X, 0))
  map_add' X Y := by simp only [Prod.mk_add_mk, zero_add]
  map_smul' c X := by simp only [RingHom.id_apply, Prod.smul_mk, smul_zero]

private noncomputable def shortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp rawShortLift

/-- Literal V has the checked entire-vector signed image on each inverse-U short unit. -/
theorem monsterNortonLine01PairInverseV_unit (e : Fin 64) :
    y555NortonV.val (monsterNortonPureShort (monsterNortonLine01PairInverseShortOutput e)) =
      qSign (monsterNortonLine01PairInverseVPhase e) •
        monsterNortonPureShort (monsterNortonLine01PairInverseShortOutput e) := by
  rw [y555NortonV, monsterNortonPureShort]
  change localGriessRepresentation (localFiberIncl y555NortonVQ)
    (griessConwayDecode (0, (Pi.single (monsterNortonLine01PairInverseShortOutput e) 1, 0))) = _
  have hc : spinConjugation (localFiberIncl y555NortonVQ).val.1
      (monsterNortonShortQ (monsterNortonLine01PairInverseShortOutput e)) =
        qCentral (monsterNortonLine01PairInverseVPhase e) *
          monsterNortonShortQ (monsterNortonLine01PairInverseShortOutput e) := by
    change spinConjugation (spinHolomorphIncl y555NortonVQ) _ = _
    rw [spinConjugation_incl, q_conjugation_central_phase,
      monsterNortonLine01PairInverseVPhase_actual]
  have hd := monsterNortonGriessShortBasis_of_Q_image (localFiberIncl y555NortonVQ)
    (monsterNortonLine01PairInverseShortOutput e) (monsterNortonLine01PairInverseShortOutput e)
      (monsterNortonLine01PairInverseVPhase e) hc
  exact hd.trans (shortLift.map_smul (qSign (monsterNortonLine01PairInverseVPhase e))
    (Pi.single (monsterNortonLine01PairInverseShortOutput e) 1))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
