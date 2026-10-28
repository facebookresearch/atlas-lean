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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint678

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Source point 813 is a literal actual Conway image of the prior source point. -/
def monsterCo1GeometryVectorPoint813 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint678

/-- All coordinates are checked against the actual parent action and actual operator matrix. -/
theorem monsterCo1GeometryVectorPoint813_binary :
    monsterCo1GeometryVectorPoint813.val =
      ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0] := by
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
    monsterCo1GeometryVectorPoint678.val =
      _
  rw [monsterCo1GeometryVectorPoint678_binary, monsterCo1GeometryTransportOperator_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 8243466 5808071
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
