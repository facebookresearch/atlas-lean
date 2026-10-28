/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source point is the literal actual operator image of its earlier actual parent. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskOperators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint406

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Source point 615 is a literal actual Conway image of the prior source point. -/
def monsterCo1GeometryVectorPoint615 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint406

/-- All coordinates are checked against the actual parent action and actual operator matrix. -/
theorem monsterCo1GeometryVectorPoint615_binary :
    monsterCo1GeometryVectorPoint615.val =
      ![0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1] := by
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
    monsterCo1GeometryVectorPoint406.val =
      _
  rw [monsterCo1GeometryVectorPoint406_binary, monsterCo1GeometryTransportOperator_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 16169874 15221634
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
