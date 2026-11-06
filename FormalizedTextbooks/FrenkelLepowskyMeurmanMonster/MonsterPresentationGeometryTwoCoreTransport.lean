/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Intrinsic normal two-cores commute with genuine group isomorphisms. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTwoCoreGeneric

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- An actual isomorphism sends the intrinsic normal two-core into the target two-core. -/
theorem monsterGeometryTwoCore_map_le {K L : Type*} [Group K] [Group L]
    (e : K ≃* L) : (monsterGeometryTwoCore K).map e.toMonoidHom ≤
      monsterGeometryTwoCore L := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro P hP
  apply Subgroup.map_le_iff_le_comap.mp
  have : (P.map e.toMonoidHom).Normal := hP.1.map e.toMonoidHom e.surjective
  exact monsterGeometryNormalTwo_le_core (P.map e.toMonoidHom) (hP.2.map e.toMonoidHom)

/-- The normal two-core is intrinsic: every genuine group isomorphism transports it exactly. -/
theorem monsterGeometryTwoCore_map_equiv {K L : Type*} [Group K] [Group L]
    (e : K ≃* L) : (monsterGeometryTwoCore K).map e.toMonoidHom =
      monsterGeometryTwoCore L := by
  apply le_antisymm (monsterGeometryTwoCore_map_le e)
  intro x hx
  have hi : e.symm x ∈ monsterGeometryTwoCore K :=
    monsterGeometryTwoCore_map_le e.symm ⟨x, hx, rfl⟩
  exact ⟨e.symm x, hi, e.apply_symm_apply x⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
