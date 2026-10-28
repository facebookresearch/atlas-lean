/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual whole inverse-sixth packet has exactly its finite full-phase integer coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoInverseCoefficientCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 9 e) =
      monsterNortonCodeTwentyTwoVSourcePhase (monsterNortonRemainingOctadUInputQ 9 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeTwentyTwoVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUOutput 9 e) =
      monsterNortonCodeTwentyTwoVSourcePhase (monsterNortonRemainingOctadUOutputQ 9 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeTwentyTwoVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUOutputQ_actual]

/-- The cached coefficient is the entire actual inverse-sixth scalar, including the outer V. -/
theorem monsterNortonCodeTwentyTwoInverseCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 9 0)) *
      monsterNortonRemainingOctadInverseSixthCoefficient 9 e =
        (monsterNortonCodeTwentyTwoInverseCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeTwentyTwoInverseCoefficient_cache]
  unfold monsterNortonRemainingOctadInverseSixthCoefficient
    monsterNortonCodeTwentyTwoInverseCoefficient
  rw [input_phase, input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete source inverse packet with every actual scalar in its integer cache. -/
noncomputable def monsterNortonCodeTwentyTwoInverseActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeTwentyTwoInverseCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 9 e)

/-- The entire actual inverse-sixth packet equals this complete sixty-four-term signed expansion. -/
theorem monsterNortonCodeTwentyTwoInverseActualPacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 9 =
        monsterNortonCodeTwentyTwoInverseActualPacket := by
  unfold monsterNortonRemainingOctadInverseSixthPacket monsterNortonCodeTwentyTwoInverseActualPacket
  rw [Finset.smul_sum]
  simp_rw [smul_smul, monsterNortonCodeTwentyTwoInverseCoefficient_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
