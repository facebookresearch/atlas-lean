/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Conway transport intertwines the original genuine-line universal module map. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryUniversalBinary

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The natural genuine-line universal module map intertwines actual Conway transport
on every vector, since its original point generators span the source module. -/
theorem monsterCo1GeometryUniversalBinary_action (g : Co1)
    (v : MonsterCo1GeometryUniversalModule) :
    monsterCo1GeometryUniversalBinary (monsterCo1GeometryUniversalAction g v) =
      co1BinaryAction g (monsterCo1GeometryUniversalBinary v) := by
  have h : monsterCo1GeometryUniversalBinary.comp (monsterCo1GeometryUniversalAction g) =
      (co1BinaryAction g).toLinearMap.comp monsterCo1GeometryUniversalBinary := by
    apply LinearMap.ext_on_range monsterCo1GeometryUniversalPoint_span
    intro p
    exact monsterCo1GeometryUniversalBinary_action_point g p
  exact LinearMap.congr_fun h v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
