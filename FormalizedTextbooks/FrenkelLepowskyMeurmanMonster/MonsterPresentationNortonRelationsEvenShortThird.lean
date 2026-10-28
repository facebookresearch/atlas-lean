/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Entire first three literal line-word states on the twenty-three preferred short units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFirstU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadShortExpansion
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSourceCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- True initial V phases, including the four positive exceptional inputs. -/
def monsterNortonEvenShortInitialVPhase : Fin 23 → ZMod 2 :=
  ![1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]

/-- Each displayed phase is the actual Q commutator phase in the source dictionary. -/
theorem monsterNortonEvenShortInitialVPhase_actual (k : Fin 23) :
    qBeta (toAdd y555NortonVQ.base) (toAdd (monsterNortonShortQ
      (monsterNortonEvenShortBasis k)).base) +
    qBeta (toAdd (monsterNortonShortQ (monsterNortonEvenShortBasis k)).base)
      (toAdd y555NortonVQ.base) = monsterNortonEvenShortInitialVPhase k := by
  unfold monsterNortonShortQ
  rw [monsterNortonEvenShortIntegral_actual]
  revert k
  decide +kernel

private noncomputable def shortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp
    ((LinearMap.inr ℝ _ _).comp (LinearMap.inl ℝ _ _))

private theorem short_smul (r : GriessShortIndex) (c : ℝ) :
    griessConwayDecode (0, (c • Pi.single r 1, 0)) =
      c • griessConwayDecode (0, (Pi.single r 1, 0)) :=
  shortLift.map_smul c (Pi.single r 1)

/-- Literal V acts on the entire original basis unit by its checked central phase. -/
theorem monsterNortonEvenShortInitialV_actual (k : Fin 23) :
    y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis k)) =
      qSign (monsterNortonEvenShortInitialVPhase k) •
        monsterNortonPureShort (monsterNortonEvenShortBasis k) := by
  have h := monsterNortonGriessShortBasis_of_Q_image (localFiberIncl y555NortonVQ)
    (monsterNortonEvenShortBasis k) (monsterNortonEvenShortBasis k)
    (monsterNortonEvenShortInitialVPhase k) (by
      change spinConjugation (spinHolomorphIncl y555NortonVQ) _ = _
      rw [spinConjugation_incl, q_conjugation_central_phase,
        monsterNortonEvenShortInitialVPhase_actual])
  rw [short_smul] at h
  exact h

/-- Inverse source triality sends the whole odd-short unit to its genuine Z tensor vector. -/
theorem monsterNortonOddShort_extra_inverse (d : Fin 2048) (j : Fin 24) :
    sExtra.symm (monsterNortonPureShort (Sum.inr (Sum.inr (d, j)))) =
      trialityXYZBasis 2 (finProdFinEquiv (d, j)) := by
  apply sExtra.injective
  rw [LinearEquiv.apply_symm_apply, sExtra_XYZ_basis,
    show trialityCycle 2 = 0 by decide, monsterNortonSourceX_pure_short]

/-- The complete inverse-triality packet: a Z vector or sixty-four actual octad coefficients. -/
noncomputable def monsterNortonEvenShortThirdPacket (k : Fin 23) : GriessSpace :=
  if monsterNortonEvenShortFirstUIsOdd k then
    trialityXYZBasis 2 (finProdFinEquiv (monsterNortonEvenShortFirstUOddCode k,
      monsterNortonEvenShortFirstUOddPosition k))
  else
    monsterNortonOctadShortVector
      (monsterNortonOctadIndex (monsterNortonEvenShortFirstUOctadCodes k)
        (monsterNortonEvenShortFirstUOctad_weight k))
      (fun r => (monsterNortonOctadInverseCoefficient r
        (monsterNortonEvenShortFirstUOctadSign k) : ℝ) / 8)

/-- Inverse triality sends every actual reached U unit to the complete stated packet. -/
theorem monsterNortonEvenShortThirdPacket_actual (k : Fin 23) :
    sExtra.symm (monsterNortonPureShort (monsterNortonEvenShortFirstUOutput k)) =
      monsterNortonEvenShortThirdPacket k := by
  unfold monsterNortonEvenShortFirstUOutput monsterNortonEvenShortThirdPacket
  by_cases h : monsterNortonEvenShortFirstUIsOdd k = true
  · simp only [ite_eq_left h]
    exact monsterNortonOddShort_extra_inverse _ _
  · simp only [ite_eq_right h]
    unfold monsterNortonPureShort
    rw [← monsterNortonOctadShortVector_single _ _ 1,
      monsterNortonOctadShortVector_extra_inverse]
    congr 1
    funext r
    rw [monsterNortonOctadTriality_inverse_single, mul_one]

/-- The entire three-step literal V, U, inverse-triality image of every preferred basis unit. -/
theorem monsterNortonEvenShortFirstThree_actual (k : Fin 23) :
    sExtra.symm (y555NortonActualU.val (y555NortonV.val
      (monsterNortonPureShort (monsterNortonEvenShortBasis k)))) =
      qSign (monsterNortonEvenShortInitialVPhase k) • monsterNortonEvenShortThirdPacket k := by
  rw [monsterNortonEvenShortInitialV_actual, map_smul,
    monsterNortonEvenShortFirstU_actual, map_smul, monsterNortonEvenShortThirdPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
