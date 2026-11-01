/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole explicit positive triality image of every original Conway short unit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadShortExpansion
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSourceCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Pair, octad Fourier, and source Y packets for positive triality on original short units. -/
noncomputable def monsterNortonShortExtraPacket : GriessShortIndex → GriessSpace
  | Sum.inl (s, p) =>
      (1 / 2 : ℝ) • trialityABCBasis 0 p +
        (if s = 0 then (1 / 2 : ℝ) else -1 / 2) • trialityABCBasis 2 p
  | Sum.inr (Sum.inl (d, e)) =>
      monsterNortonOctadShortVector d (trialityOctadAction (Pi.single e 1))
  | Sum.inr (Sum.inr (d, j)) => trialityXYZBasis 1 (finProdFinEquiv (d, j))

/-- Every whole actual positive-triality short image is its explicit physical dictionary packet. -/
theorem monsterNortonShortExtraPacket_actual (r : GriessShortIndex) :
    sExtra (monsterNortonPureShort r) = monsterNortonShortExtraPacket r := by
  rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, j⟩)
  · exact monsterNortonPairShort_extra s p
  · change sExtra (monsterNortonPureShort (Sum.inr (Sum.inl (d, e)))) =
      monsterNortonOctadShortVector d (trialityOctadAction (Pi.single e 1))
    unfold monsterNortonPureShort
    rw [← monsterNortonOctadShortVector_single _ _ 1, monsterNortonOctadShortVector_extra]
  · rw [← monsterNortonSourceX_pure_short, sExtra_XYZ_basis]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
