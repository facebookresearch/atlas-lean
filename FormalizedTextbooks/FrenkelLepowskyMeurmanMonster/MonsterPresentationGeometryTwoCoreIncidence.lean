/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact source Q-incidence is membership in the intrinsic O₂ of actual centralizers. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTwoCorePoints
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryQIncidence

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Source Q-incidence is exactly intrinsic O₂(C_G(p)) membership. -/
theorem monsterGeometryQIncident_iff_twoCore (p q : MonsterGeometryPoint) :
    monsterGeometryQIncident p q ↔
      q.val ∈ (monsterGeometryTwoCore (monsterGeometryPointCentralizer p)).map
        (monsterGeometryPointCentralizer p).subtype := by
  obtain ⟨g, hg⟩ := isConj_iff.mp p.property
  rw [monsterGeometryPointTwoCore_image_eq_Q p g hg,
    monsterGeometryQIncident_iff_of_conjugator p q g hg]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨qIntoGenerated x, ⟨x, rfl⟩, hx⟩
  · rintro ⟨v, ⟨x, rfl⟩, hx⟩
    exact ⟨x, hx⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
