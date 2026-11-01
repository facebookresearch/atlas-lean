/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual whole inverse-sixth packet has exactly its finite full-phase integer coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenInverseCoefficientCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 5 e) =
      monsterNortonCodeEighteenInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 5 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeEighteenInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUOutput 5 e) =
      monsterNortonCodeEighteenInverseVSourcePhase (monsterNortonRemainingOctadUOutputQ 5 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeEighteenInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUOutputQ_actual]

/-- The cached coefficient is the entire actual inverse-sixth scalar, including the outer V. -/
theorem monsterNortonCodeEighteenInverseCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 5 0)) *
      monsterNortonRemainingOctadInverseSixthCoefficient 5 e =
        (monsterNortonCodeEighteenInverseCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeEighteenInverseCoefficient_cache]
  unfold monsterNortonRemainingOctadInverseSixthCoefficient
    monsterNortonCodeEighteenInverseCoefficient
  rw [input_phase, input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete source inverse packet with every actual scalar in its integer cache. -/
noncomputable def monsterNortonCodeEighteenInverseActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeEighteenInverseCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 5 e)

/-- The entire actual inverse-sixth packet equals this complete sixty-four-term signed expansion. -/
theorem monsterNortonCodeEighteenInverseActualPacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 5 =
        monsterNortonCodeEighteenInverseActualPacket := by
  unfold monsterNortonRemainingOctadInverseSixthPacket monsterNortonCodeEighteenInverseActualPacket
  rw [Finset.smul_sum]
  simp_rw [smul_smul, monsterNortonCodeEighteenInverseCoefficient_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
