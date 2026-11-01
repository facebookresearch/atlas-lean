/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal Conway transport is a representation on the independent original-line module. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryUniversalAction

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Identity Conway transport acts identically on the independently presented source module. -/
theorem monsterCo1GeometryUniversalAction_one :
    monsterCo1GeometryUniversalAction (1 : Co1) = 1 := by
  apply LinearMap.ext_on_range monsterCo1GeometryUniversalPoint_span
  intro p
  simp only [monsterCo1GeometryUniversalAction_point, one_smul, Module.End.one_apply]

/-- Composition retains the actual Conway multiplication on the independent source module. -/
theorem monsterCo1GeometryUniversalAction_mul (g h : Co1) :
    monsterCo1GeometryUniversalAction (g * h) =
      monsterCo1GeometryUniversalAction g * monsterCo1GeometryUniversalAction h := by
  apply LinearMap.ext_on_range monsterCo1GeometryUniversalPoint_span
  intro p
  simp only [monsterCo1GeometryUniversalAction_point, Module.End.mul_apply, mul_smul]

/-- The actual Conway group acts linearly on the independently defined source universal module. -/
def monsterCo1GeometryUniversalRepresentation :
    Co1 →* Module.End (ZMod 2) MonsterCo1GeometryUniversalModule where
  toFun := monsterCo1GeometryUniversalAction
  map_one' := monsterCo1GeometryUniversalAction_one
  map_mul' := monsterCo1GeometryUniversalAction_mul

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
