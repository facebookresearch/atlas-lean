/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source point is the literal actual operator image of its earlier actual parent. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint021

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Source point 184 is a literal actual Conway image of the prior source point. -/
def monsterCo1GeometryVectorPoint184 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint21

/-- All coordinates are checked against the actual parent action and actual operator matrix. -/
theorem monsterCo1GeometryVectorPoint184_binary :
    monsterCo1GeometryVectorPoint184.val =
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0] := by
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
    monsterCo1GeometryVectorPoint21.val =
      _
  rw [monsterCo1GeometryVectorPoint21_binary, monsterCo1GeometryTransportOperator_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
