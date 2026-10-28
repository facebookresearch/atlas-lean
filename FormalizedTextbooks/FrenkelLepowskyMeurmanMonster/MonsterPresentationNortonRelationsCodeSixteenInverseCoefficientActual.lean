/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual whole inverse-sixth packet has exactly its finite full-phase integer coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenInverseCoefficientCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 3 e) =
      monsterNortonCodeSixteenInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 3 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeSixteenInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUOutput 3 e) =
      monsterNortonCodeSixteenInverseVSourcePhase (monsterNortonRemainingOctadUOutputQ 3 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeSixteenInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUOutputQ_actual]

/-- The cached coefficient is the entire actual inverse-sixth scalar, including the outer V. -/
theorem monsterNortonCodeSixteenInverseCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 3 0)) *
      monsterNortonRemainingOctadInverseSixthCoefficient 3 e =
        (monsterNortonCodeSixteenInverseCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeSixteenInverseCoefficient_cache]
  unfold monsterNortonRemainingOctadInverseSixthCoefficient
    monsterNortonCodeSixteenInverseCoefficient
  rw [input_phase, input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete source inverse packet with every actual scalar in its integer cache. -/
noncomputable def monsterNortonCodeSixteenInverseActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeSixteenInverseCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 3 e)

/-- The entire actual inverse-sixth packet equals this complete sixty-four-term signed expansion. -/
theorem monsterNortonCodeSixteenInverseActualPacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 3 =
        monsterNortonCodeSixteenInverseActualPacket := by
  unfold monsterNortonRemainingOctadInverseSixthPacket monsterNortonCodeSixteenInverseActualPacket
  rw [Finset.smul_sum]
  simp_rw [smul_smul, monsterNortonCodeSixteenInverseCoefficient_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
