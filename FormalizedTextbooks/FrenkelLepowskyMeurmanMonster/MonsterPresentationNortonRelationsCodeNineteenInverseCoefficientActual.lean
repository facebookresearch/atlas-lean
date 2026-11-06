/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual whole inverse-sixth packet has exactly its finite full-phase integer coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenInverseCoefficientCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 6 e) =
      monsterNortonCodeNineteenInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 6 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeNineteenInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonRemainingOctadUOutput 6 e) =
      monsterNortonCodeNineteenInverseVSourcePhase (monsterNortonRemainingOctadUOutputQ 6 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeNineteenInverseVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonRemainingOctadUOutputQ_actual]

/-- The cached coefficient is the entire actual inverse-sixth scalar, including the outer V. -/
theorem monsterNortonCodeNineteenInverseCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonVShortPhase (monsterNortonRemainingOctadUInput 6 0)) *
      monsterNortonRemainingOctadInverseSixthCoefficient 6 e =
        (monsterNortonCodeNineteenInverseCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeNineteenInverseCoefficient_cache]
  unfold monsterNortonRemainingOctadInverseSixthCoefficient
    monsterNortonCodeNineteenInverseCoefficient
  rw [input_phase, input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete source inverse packet with every actual scalar in its integer cache. -/
noncomputable def monsterNortonCodeNineteenInverseActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeNineteenInverseCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonRemainingOctadUOutput 6 e)

/-- The entire actual inverse-sixth packet equals this complete sixty-four-term signed expansion. -/
theorem monsterNortonCodeNineteenInverseActualPacket_actual :
    monsterNortonRemainingOctadInverseSixthPacket 6 =
        monsterNortonCodeNineteenInverseActualPacket := by
  unfold monsterNortonRemainingOctadInverseSixthPacket monsterNortonCodeNineteenInverseActualPacket
  rw [Finset.smul_sum]
  simp_rw [smul_smul, monsterNortonCodeNineteenInverseCoefficient_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
