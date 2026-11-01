/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The full actual sixth state of the first pair-short line-square test. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseUPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseV

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact sixth-state coefficients retain both inverse-triality and actual V phases. -/
noncomputable def monsterNortonLine01PairAfterInverseUV : GriessSpace :=
  ∑ e, (((monsterNortonLine01PairOctadInverseNumerator e : ℝ) / 8) *
    qSign (monsterNortonLine01PairOctadVPhase e) *
      qSign (monsterNortonLine01PairInverseVPhase e)) •
      monsterNortonPureShort (monsterNortonLine01PairInverseShortOutput e)

/-- The sixth literal operator has this entire checked signed pair/octet packet. -/
theorem monsterNortonLine01PairSixth_actual :
    y555NortonV.val ((y555NortonActualU⁻¹).val
      (y555NortonV.val monsterNortonLine01PairAfterVUExtraInverse)) =
        monsterNortonLine01PairAfterInverseUV := by
  rw [monsterNortonLine01PairInverseU_packet, monsterNortonLine01PairAfterInverseU, map_sum]
  simp only [map_smul, monsterNortonLine01PairInverseV_unit, smul_smul]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
