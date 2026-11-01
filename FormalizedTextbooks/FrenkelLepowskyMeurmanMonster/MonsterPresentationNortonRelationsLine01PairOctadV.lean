/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal Norton V on the entire first inverse-triality octad packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseOctad
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseShortInput
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadShortExpansion
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsVBinaryCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairShortBinaryData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The exact V phases on the original reached octad sign coordinates. -/
def monsterNortonLine01PairOctadVPhase : Fin 64 → ZMod 2 :=
  ![
    0, 0, 0, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 1, 1, 1, 0,
    1, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, 1, 0, 1, 1, 1,
    1, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, 1, 0, 1, 1, 1,
    1, 1, 1, 0, 1, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the actual bilinear central phase on all reached original octad signs.
/-- Literal V has these full phases on every unit in the reached octad1281 packet. -/
theorem monsterNortonLine01PairOctadV_phase (e : Fin 64) :
    qBeta (toAdd y555NortonVQ.base)
        (toAdd (monsterNortonShortQ (monsterNortonLine01PairInverseShortInput e)).base) +
      qBeta (toAdd (monsterNortonShortQ (monsterNortonLine01PairInverseShortInput e)).base)
        (toAdd y555NortonVQ.base) = monsterNortonLine01PairOctadVPhase e := by
  rw [monsterNortonVBinaryCoordinates_actual, monsterNortonLine01PairInputBinaryMasks_actual]
  fin_cases e <;> decide +kernel

private def rawShortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] ConwayRawSpace where
  toFun X := (0, (X, 0))
  map_add' X Y := by simp only [Prod.mk_add_mk, zero_add]
  map_smul' c X := by simp only [RingHom.id_apply, Prod.smul_mk, smul_zero]

private noncomputable def shortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp rawShortLift

/-- V has the entire actual signed Griess-unit image at each reached octad coordinate. -/
theorem monsterNortonLine01PairOctadV_unit (e : Fin 64) :
    y555NortonV.val (monsterNortonPureShort (monsterNortonLine01PairInverseShortInput e)) =
      qSign (monsterNortonLine01PairOctadVPhase e) •
        monsterNortonPureShort (monsterNortonLine01PairInverseShortInput e) := by
  rw [y555NortonV, monsterNortonPureShort]
  change localGriessRepresentation (localFiberIncl y555NortonVQ)
    (griessConwayDecode (0, (Pi.single (monsterNortonLine01PairInverseShortInput e) 1, 0))) = _
  have hc : spinConjugation (localFiberIncl y555NortonVQ).val.1
      (monsterNortonShortQ (monsterNortonLine01PairInverseShortInput e)) =
        qCentral (monsterNortonLine01PairOctadVPhase e) *
          monsterNortonShortQ (monsterNortonLine01PairInverseShortInput e) := by
    change spinConjugation (spinHolomorphIncl y555NortonVQ) _ = _
    rw [spinConjugation_incl, q_conjugation_central_phase, monsterNortonLine01PairOctadV_phase]
  have hd := monsterNortonGriessShortBasis_of_Q_image (localFiberIncl y555NortonVQ)
    (monsterNortonLine01PairInverseShortInput e) (monsterNortonLine01PairInverseShortInput e)
      (monsterNortonLine01PairOctadVPhase e) hc
  exact hd.trans (shortLift.map_smul (qSign (monsterNortonLine01PairOctadVPhase e))
    (Pi.single (monsterNortonLine01PairInverseShortInput e) 1))

/-- The entire signed fourth state, with every actual V phase retained. -/
noncomputable def monsterNortonLine01PairAfterVUExtraInverseV : GriessSpace :=
  ∑ e, (((monsterNortonLine01PairOctadInverseNumerator e : ℝ) / 8) *
    qSign (monsterNortonLine01PairOctadVPhase e)) •
      monsterNortonPureShort (monsterNortonLine01PairInverseShortInput e)

/-- The fourth literal operator has this full phase-correct original octad packet. -/
theorem monsterNortonLine01PairOctadV_packet :
    y555NortonV.val monsterNortonLine01PairAfterVUExtraInverse =
      monsterNortonLine01PairAfterVUExtraInverseV := by
  rw [monsterNortonLine01PairAfterVUExtraInverse,
    monsterNortonOctadShortVector_expansion, map_smul, map_sum, Finset.smul_sum]
  simp only [map_smul]
  unfold monsterNortonLine01PairAfterVUExtraInverseV
  apply Finset.sum_congr rfl
  intro e _
  rw [smul_smul, monsterNortonLine01PairOctadInverse_coefficient]
  have h := congrArg (fun x : GriessSpace =>
    ((monsterNortonLine01PairOctadInverseNumerator e : ℝ) / 8) • x)
      (monsterNortonLine01PairOctadV_unit e)
  rw [smul_smul] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
