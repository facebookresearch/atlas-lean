/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact first inverse-triality octad packet in the pair-short line-square test. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairFirstU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadTrialityInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Integer coefficients of the full reached inverse-octad packet. -/
def monsterNortonLine01PairOctadInverseNumerator (e : Fin 64) : ℤ :=
  -monsterNortonOctadInverseCoefficient e 45

/-- The full actual third vector, supported in the original octad1281 block. -/
noncomputable def monsterNortonLine01PairAfterVUExtraInverse : GriessSpace :=
  (-1 : ℝ) • monsterNortonOctadShortVector
    (monsterNortonOctadIndex 1281 monsterNortonLine01PairUOctad_weight)
      (trialityOctadAction.symm (Pi.single 45 1))

/-- Literal inverse extra acts on the entire proved V,U state by this complete octad packet. -/
theorem monsterNortonLine01PairExtraInverse_actual :
    sExtra.symm (y555NortonActualU.val
      (y555NortonV.val (monsterNortonPureShort monsterNortonLine01PairShortInput))) =
        monsterNortonLine01PairAfterVUExtraInverse := by
  have hs : monsterNortonPureShort monsterNortonLine01PairUShortOutput =
      monsterNortonOctadShortVector
        (monsterNortonOctadIndex 1281 monsterNortonLine01PairUOctad_weight)
          (Pi.single 45 1) :=
    (monsterNortonOctadShortVector_single _ _ _).symm
  rw [monsterNortonLine01PairVU_actual, map_smul, hs,
    monsterNortonOctadShortVector_extra_inverse]
  rfl

/-- Every original octad coordinate of this packet has its exact integer numerator. -/
theorem monsterNortonLine01PairOctadInverse_coefficient (e : Fin 64) :
    (-1 : ℝ) * trialityOctadAction.symm (Pi.single 45 1) e =
      (monsterNortonLine01PairOctadInverseNumerator e : ℝ) / 8 := by
  rw [monsterNortonOctadTriality_inverse_single]
  simp only [monsterNortonLine01PairOctadInverseNumerator, Int.cast_neg]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
