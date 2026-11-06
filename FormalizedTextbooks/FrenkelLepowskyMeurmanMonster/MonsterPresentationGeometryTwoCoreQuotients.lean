/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Intrinsic normal two-cores descend through actual surjections with two-group kernel. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTwoCoreGeneric

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Any surjective group homomorphism sends its intrinsic normal two-core into the target's. -/
theorem monsterGeometryTwoCore_map_surjective_le {K L : Type*} [Group K] [Group L]
    (f : K →* L) (hf : Function.Surjective f) :
    (monsterGeometryTwoCore K).map f ≤ monsterGeometryTwoCore L := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro P hP
  apply Subgroup.map_le_iff_le_comap.mp
  have : (P.map f).Normal := hP.1.map f hf
  exact monsterGeometryNormalTwo_le_core (P.map f) (hP.2.map f)

/-- A two-group kernel makes the actual image of the two-core exactly the target two-core. -/
theorem monsterGeometryTwoCore_map_surjective {K L : Type*} [Group K] [Group L]
    (f : K →* L) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    (monsterGeometryTwoCore K).map f = monsterGeometryTwoCore L := by
  apply le_antisymm (monsterGeometryTwoCore_map_surjective_le f hf)
  apply sSup_le
  intro P hP
  have : P.Normal := hP.1
  have hp : IsPGroup 2 (P.comap f) := hP.2.comap_of_ker_isPGroup f hker
  have hle := Subgroup.map_mono (f := f) (monsterGeometryNormalTwo_le_core (P.comap f) hp)
  rw [Subgroup.map_comap_eq_self_of_surjective hf P] at hle
  exact hle

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
