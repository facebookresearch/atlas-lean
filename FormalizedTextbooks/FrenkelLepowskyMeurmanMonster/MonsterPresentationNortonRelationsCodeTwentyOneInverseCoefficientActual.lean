/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual whole inverse-sixth packet has exactly its finite full-phase integer coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneInverseCoefficientCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 8 e) =
      monsterNortonCodeTwentyOneInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 8 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeTwentyOneInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUOutput 8 e) =
      monsterNortonCodeTwentyOneInverseVSourcePhase (monsterNortonRemainingOctadUOutputQ 8 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeTwentyOneInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUOutputQ_actual]

/-- The cached coefficient is the entire actual inverse-sixth scalar, including the outer V. -/
theorem monsterNortonCodeTwentyOneInverseCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 8 0)) *
      monsterNortonRemainingOctadInverseSixthCoefficient 8 e =
        (monsterNortonCodeTwentyOneInverseCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeTwentyOneInverseCoefficient_cache]
  unfold monsterNortonRemainingOctadInverseSixthCoefficient
    monsterNortonCodeTwentyOneInverseCoefficient
  rw [input_phase, input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete source inverse packet with every actual scalar in its integer cache. -/
noncomputable def monsterNortonCodeTwentyOneInverseActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeTwentyOneInverseCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 8 e)

/-- The entire actual inverse-sixth packet equals this complete sixty-four-term signed expansion. -/
theorem monsterNortonCodeTwentyOneInverseActualPacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 8 =
        monsterNortonCodeTwentyOneInverseActualPacket := by
  unfold monsterNortonRemainingOctadInverseSixthPacket monsterNortonCodeTwentyOneInverseActualPacket
  rw [Finset.smul_sum]
  simp_rw [smul_smul, monsterNortonCodeTwentyOneInverseCoefficient_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
