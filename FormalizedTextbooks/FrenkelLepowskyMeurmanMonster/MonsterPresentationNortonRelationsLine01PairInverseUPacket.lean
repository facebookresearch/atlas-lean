/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The entire actual fifth state of the first pair-short line-square test. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairOctadV

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire inverse-U packet in its checked original pair and octad coordinates. -/
noncomputable def monsterNortonLine01PairAfterInverseU : GriessSpace :=
  ∑ e, (((monsterNortonLine01PairOctadInverseNumerator e : ℝ) / 8) *
    qSign (monsterNortonLine01PairOctadVPhase e)) •
      monsterNortonPureShort (monsterNortonLine01PairInverseShortOutput e)

/-- The reached inverse-triality vector has exactly these sixty-four original unit coefficients. -/
theorem monsterNortonLine01PairInverseOctad_expansion :
    monsterNortonLine01PairAfterVUExtraInverse =
      ∑ e, ((monsterNortonLine01PairOctadInverseNumerator e : ℝ) / 8) •
        monsterNortonPureShort (monsterNortonLine01PairInverseShortInput e) := by
  rw [monsterNortonLine01PairAfterVUExtraInverse,
    monsterNortonOctadShortVector_expansion, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [smul_smul, monsterNortonLine01PairOctadInverse_coefficient]
  rfl

/-- Literal inverse U sends the whole actual fourth state to the checked sixty-four-unit packet. -/
theorem monsterNortonLine01PairInverseU_packet :
    (y555NortonActualU⁻¹).val
      (y555NortonV.val monsterNortonLine01PairAfterVUExtraInverse) =
        monsterNortonLine01PairAfterInverseU := by
  rw [monsterNortonLine01PairOctadV_packet, monsterNortonLine01PairAfterVUExtraInverseV,
    map_sum]
  simp only [map_smul, monsterNortonLine01PairInverseU_unit]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
