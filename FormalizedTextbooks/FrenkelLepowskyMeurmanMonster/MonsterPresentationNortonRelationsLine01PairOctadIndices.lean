/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Injective original octad indexing for the fourteen reached pair-short blocks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseShortData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Equality of certified original octad indices is precisely equality of their Golay labels. -/
theorem monsterNortonOctadIndex_eq_iff (a b : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8)
    (hb : golayMaskWeight (golayEncodedMask b.val) = 8) :
    monsterNortonOctadIndex a ha = monsterNortonOctadIndex b hb ↔ a = b := by
  constructor
  · intro h
    have hc := congrArg golayOctadLabel h
    rwa [monsterNortonOctadIndex_label, monsterNortonOctadIndex_label] at hc
  · intro h
    subst b
    rfl

/-- The fourteen actual octad indices appearing in the inverse-U pair-short packet. -/
noncomputable def monsterNortonLine01PairBlockOctad (a : Fin 14) : Fin 759 :=
  monsterNortonOctadIndex (monsterNortonLine01PairInverseOctadCodes a)
    (monsterNortonLine01PairInverseOctad_weight a)

/-- All displayed Golay labels are distinct, by a finite kernel certificate. -/
theorem monsterNortonLine01PairBlock_codes_injective :
    Function.Injective monsterNortonLine01PairInverseOctadCodes := by
  decide +kernel

/-- Hence their indices in the original octad dictionary are also all distinct. -/
theorem monsterNortonLine01PairBlockOctad_injective :
    Function.Injective monsterNortonLine01PairBlockOctad := by
  intro a b h
  exact monsterNortonLine01PairBlock_codes_injective
    ((monsterNortonOctadIndex_eq_iff _ _ _ _).1 h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
