/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Entire inverse-sixth line-word packets for the ten remaining original octad inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsRemainingOctadUCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFourth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortPositiveTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem short_scaled (r : GriessShortIndex) (c : ℝ) :
    griessConwayDecode (0, (c • Pi.single r 1, 0)) = c • monsterNortonPureShort r := by
  have h : ((0, (c • Pi.single r 1, 0)) : ConwayRawSpace) =
      c • (0, (Pi.single r 1, 0)) := by
    simp only [Prod.smul_mk, smul_zero]
  change griessConwayDecodeLinear (0, (c • Pi.single r 1, 0)) =
    c • griessConwayDecodeLinear (0, (Pi.single r 1, 0))
  rw [h, map_smul]

private theorem u_short (k : Fin 10) (e : Fin 64) :
    y555NortonActualU.val (monsterNortonPureShort (monsterNortonRemainingOctadUInput k e)) =
      qSign (monsterNortonRemainingOctadUPhase k e) •
        monsterNortonPureShort (monsterNortonRemainingOctadUOutput k e) := by
  have h := monsterNortonRemainingOctadU_actual k e
  rw [short_scaled] at h
  exact h

/-- The full coefficient retains both V phases, the inverse Fourier sign, and the actual U sign. -/
noncomputable def monsterNortonRemainingOctadInverseSixthCoefficient
    (k : Fin 10) (e : Fin 64) : ℝ :=
  (((monsterNortonOctadInverseCoefficient e 0 : ℝ) / 8 *
    qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput k e))) *
    qSign (monsterNortonRemainingOctadUPhase k e)) *
      qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUOutput k e))

/-- The complete inverse-sixth packet includes the reached octad Fourier and odd tensor outputs. -/
noncomputable def monsterNortonRemainingOctadInverseSixthPacket (k : Fin 10) : GriessSpace :=
  qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput k 0)) •
    ∑ e : Fin 64, monsterNortonRemainingOctadInverseSixthCoefficient k e •
      monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput k e)

/-- Six actual literal inverse operators give this whole packet for every remaining input octad. -/
theorem monsterNortonRemainingOctadInverseFirstSix_actual (k : Fin 10) :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonRemainingOctadUInput k 0))))))) =
      monsterNortonRemainingOctadInverseSixthPacket k := by
  have hextra : sExtra.symm (monsterNortonPureShort (monsterNortonRemainingOctadUInput k 0)) =
      ∑ e : Fin 64, ((monsterNortonOctadInverseCoefficient e 0 : ℝ) / 8) •
        monsterNortonPureShort (monsterNortonRemainingOctadUInput k e) := by
    unfold monsterNortonRemainingOctadUInput
    conv_lhs => unfold monsterNortonPureShort
    rw [← monsterNortonOctadShortVector_single _ _ 1,
      monsterNortonOctadShortVector_extra_inverse, monsterNortonOctadShortVector_expansion]
    simp only [monsterNortonOctadTriality_inverse_single, mul_one]
  rw [monsterNortonV_pure_short, map_smul, map_smul, map_smul, map_smul, map_smul, hextra]
  simp only [map_sum, map_smul, monsterNortonV_pure_short, u_short,
    monsterNortonShortExtraPacket_actual, smul_smul]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
