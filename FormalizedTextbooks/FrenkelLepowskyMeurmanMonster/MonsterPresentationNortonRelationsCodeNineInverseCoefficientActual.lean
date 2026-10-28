/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual whole inverse-sixth packet has exactly its finite full-phase integer coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineInverseCoefficientCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 2 e) =
      monsterNortonCodeNineVSourcePhase (monsterNortonRemainingOctadUInputQ 2 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeNineVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUOutput 2 e) =
      monsterNortonCodeNineVSourcePhase (monsterNortonRemainingOctadUOutputQ 2 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeNineVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUOutputQ_actual]

/-- The cached coefficient is the entire actual inverse-sixth scalar, including the outer V. -/
theorem monsterNortonCodeNineInverseCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 2 0)) *
      monsterNortonRemainingOctadInverseSixthCoefficient 2 e =
        (monsterNortonCodeNineInverseCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeNineInverseCoefficient_cache]
  unfold monsterNortonRemainingOctadInverseSixthCoefficient
    monsterNortonCodeNineInverseCoefficient
  rw [input_phase, input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete source inverse packet with every actual scalar in its integer cache. -/
noncomputable def monsterNortonCodeNineInverseActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeNineInverseCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 2 e)

/-- The entire actual inverse-sixth packet equals this complete sixty-four-term signed expansion. -/
theorem monsterNortonCodeNineInverseActualPacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 2 =
        monsterNortonCodeNineInverseActualPacket := by
  unfold monsterNortonRemainingOctadInverseSixthPacket monsterNortonCodeNineInverseActualPacket
  rw [Finset.smul_sum]
  simp_rw [smul_smul, monsterNortonCodeNineInverseCoefficient_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
