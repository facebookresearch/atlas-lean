/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole inverse-sixth line-word image on the original code-three preferred octad unit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadThreeU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFourth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortPositiveTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every coefficient keeps the original inverse Fourier row and both actual V polar phases. -/
noncomputable def monsterNortonOctadThreeInverseSixthCoefficient (e : Fin 64) : ℝ :=
  ((monsterNortonOctadInverseCoefficient e 0 : ℝ) / 8 *
    qSign (monsterNortonVShortPhase (monsterNortonOctadThreeUInput e))) *
      qSign (monsterNortonVShortPhase (monsterNortonOctadThreeUOutput e))

/-- The complete inverse-sixth packet, including all matrix and octad Fourier contributions. -/
noncomputable def monsterNortonOctadThreeInverseSixthPacket : GriessSpace :=
  qSign (monsterNortonVShortPhase (monsterNortonOctadThreeUInput 0)) •
    ∑ e : Fin 64, monsterNortonOctadThreeInverseSixthCoefficient e •
      monsterNortonShortExtraPacket (monsterNortonOctadThreeUOutput e)

/-- The six literal inverse operators equal this entire phase-complete physical packet. -/
theorem monsterNortonOctadThreeInverseFirstSix_actual :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonOctadThreeUInput 0))))))) =
      monsterNortonOctadThreeInverseSixthPacket := by
  have hextra : sExtra.symm (monsterNortonPureShort (monsterNortonOctadThreeUInput 0)) =
      ∑ e : Fin 64, ((monsterNortonOctadInverseCoefficient e 0 : ℝ) / 8) •
        monsterNortonPureShort (monsterNortonOctadThreeUInput e) := by
    unfold monsterNortonOctadThreeUInput
    conv_lhs => unfold monsterNortonPureShort
    rw [← monsterNortonOctadShortVector_single _ _ 1,
      monsterNortonOctadShortVector_extra_inverse, monsterNortonOctadShortVector_expansion]
    simp only [monsterNortonOctadTriality_inverse_single, mul_one]
  rw [monsterNortonV_pure_short, map_smul, map_smul, map_smul, map_smul, map_smul, hextra]
  simp only [map_sum, map_smul, monsterNortonV_pure_short,
    monsterNortonOctadThreeU_actual, monsterNortonShortExtraPacket_actual, smul_smul]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
