/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual whole inverse-sixth packet has exactly its finite full-phase integer coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenInverseCoefficientCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 4 e) =
      monsterNortonCodeSeventeenInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 4 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeSeventeenInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUOutput 4 e) =
      monsterNortonCodeSeventeenInverseVSourcePhase (monsterNortonRemainingOctadUOutputQ 4 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeSeventeenInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUOutputQ_actual]

/-- The cached coefficient is the entire actual inverse-sixth scalar, including the outer V. -/
theorem monsterNortonCodeSeventeenInverseCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 4 0)) *
      monsterNortonRemainingOctadInverseSixthCoefficient 4 e =
        (monsterNortonCodeSeventeenInverseCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeSeventeenInverseCoefficient_cache]
  unfold monsterNortonRemainingOctadInverseSixthCoefficient
    monsterNortonCodeSeventeenInverseCoefficient
  rw [input_phase, input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete source inverse packet with every actual scalar in its integer cache. -/
noncomputable def monsterNortonCodeSeventeenInverseActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeSeventeenInverseCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 4 e)

/-- The entire actual inverse-sixth packet equals this complete sixty-four-term signed expansion. -/
theorem monsterNortonCodeSeventeenInverseActualPacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 4 =
        monsterNortonCodeSeventeenInverseActualPacket := by
  unfold monsterNortonRemainingOctadInverseSixthPacket monsterNortonCodeSeventeenInverseActualPacket
  rw [Finset.smul_sum]
  simp_rw [smul_smul, monsterNortonCodeSeventeenInverseCoefficient_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
