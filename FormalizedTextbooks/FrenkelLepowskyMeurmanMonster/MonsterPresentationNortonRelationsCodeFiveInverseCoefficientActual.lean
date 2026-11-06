/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual whole inverse-sixth packet has exactly its finite full-phase integer coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveInverseCoefficientCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 0 e) =
      monsterNortonCodeFiveVSourcePhase (monsterNortonRemainingOctadUInputQ 0 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeFiveVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUOutput 0 e) =
      monsterNortonCodeFiveVSourcePhase (monsterNortonRemainingOctadUOutputQ 0 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeFiveVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUOutputQ_actual]

/-- The cached coefficient is the entire actual inverse-sixth scalar, including the outer V. -/
theorem monsterNortonCodeFiveInverseCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 0 0)) *
      monsterNortonRemainingOctadInverseSixthCoefficient 0 e =
        (monsterNortonCodeFiveInverseCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeFiveInverseCoefficient_cache]
  unfold monsterNortonRemainingOctadInverseSixthCoefficient
    monsterNortonCodeFiveInverseCoefficient
  rw [input_phase, input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete source inverse packet with every actual scalar in its integer cache. -/
noncomputable def monsterNortonCodeFiveInverseActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeFiveInverseCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 0 e)

/-- The entire actual inverse-sixth packet equals this complete sixty-four-term signed expansion. -/
theorem monsterNortonCodeFiveInverseActualPacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 0 = monsterNortonCodeFiveInverseActualPacket := by
  unfold monsterNortonRemainingOctadInverseSixthPacket monsterNortonCodeFiveInverseActualPacket
  rw [Finset.smul_sum]
  simp_rw [smul_smul, monsterNortonCodeFiveInverseCoefficient_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
