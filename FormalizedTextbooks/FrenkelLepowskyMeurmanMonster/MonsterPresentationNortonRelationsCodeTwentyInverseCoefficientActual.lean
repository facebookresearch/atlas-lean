/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual whole inverse-sixth packet has exactly its finite full-phase integer coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyInverseCoefficientCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 7 e) =
      monsterNortonCodeTwentyInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 7 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeTwentyInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUOutput 7 e) =
      monsterNortonCodeTwentyInverseVSourcePhase (monsterNortonRemainingOctadUOutputQ 7 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeTwentyInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUOutputQ_actual]

/-- The cached coefficient is the entire actual inverse-sixth scalar, including the outer V. -/
theorem monsterNortonCodeTwentyInverseCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 7 0)) *
      monsterNortonRemainingOctadInverseSixthCoefficient 7 e =
        (monsterNortonCodeTwentyInverseCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeTwentyInverseCoefficient_cache]
  unfold monsterNortonRemainingOctadInverseSixthCoefficient
    monsterNortonCodeTwentyInverseCoefficient
  rw [input_phase, input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete source inverse packet with every actual scalar in its integer cache. -/
noncomputable def monsterNortonCodeTwentyInverseActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeTwentyInverseCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 7 e)

/-- The entire actual inverse-sixth packet equals this complete sixty-four-term signed expansion. -/
theorem monsterNortonCodeTwentyInverseActualPacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 7 =
        monsterNortonCodeTwentyInverseActualPacket := by
  unfold monsterNortonRemainingOctadInverseSixthPacket monsterNortonCodeTwentyInverseActualPacket
  rw [Finset.smul_sum]
  simp_rw [smul_smul, monsterNortonCodeTwentyInverseCoefficient_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
