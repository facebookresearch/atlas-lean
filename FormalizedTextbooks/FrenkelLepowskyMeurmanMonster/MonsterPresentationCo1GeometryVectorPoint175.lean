/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source point is the literal actual operator image of its earlier actual parent. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint018

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Source point 175 is a literal actual Conway image of the prior source point. -/
def monsterCo1GeometryVectorPoint175 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint18

/-- All coordinates are checked against the actual parent action and actual operator matrix. -/
theorem monsterCo1GeometryVectorPoint175_binary :
    monsterCo1GeometryVectorPoint175.val =
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0] := by
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
    monsterCo1GeometryVectorPoint18.val =
      _
  rw [monsterCo1GeometryVectorPoint18_binary, monsterCo1GeometryTransportOperator_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
