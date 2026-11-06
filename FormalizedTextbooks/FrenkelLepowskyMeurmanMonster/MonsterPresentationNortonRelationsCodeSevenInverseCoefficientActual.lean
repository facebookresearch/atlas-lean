/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual whole inverse-sixth packet has exactly its finite full-phase integer coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenInverseCoefficientCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 1 e) =
      monsterNortonCodeSevenVSourcePhase (monsterNortonRemainingOctadUInputQ 1 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeSevenVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUOutput 1 e) =
      monsterNortonCodeSevenVSourcePhase (monsterNortonRemainingOctadUOutputQ 1 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeSevenVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUOutputQ_actual]

/-- The cached coefficient is the entire actual inverse-sixth scalar, including the outer V. -/
theorem monsterNortonCodeSevenInverseCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 1 0)) *
      monsterNortonRemainingOctadInverseSixthCoefficient 1 e =
        (monsterNortonCodeSevenInverseCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeSevenInverseCoefficient_cache]
  unfold monsterNortonRemainingOctadInverseSixthCoefficient
    monsterNortonCodeSevenInverseCoefficient
  rw [input_phase, input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete source inverse packet with every actual scalar in its integer cache. -/
noncomputable def monsterNortonCodeSevenInverseActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeSevenInverseCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 1 e)

/-- The entire actual inverse-sixth packet equals this complete sixty-four-term signed expansion. -/
theorem monsterNortonCodeSevenInverseActualPacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 1 =
        monsterNortonCodeSevenInverseActualPacket := by
  unfold monsterNortonRemainingOctadInverseSixthPacket monsterNortonCodeSevenInverseActualPacket
  rw [Finset.smul_sum]
  simp_rw [smul_smul, monsterNortonCodeSevenInverseCoefficient_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
