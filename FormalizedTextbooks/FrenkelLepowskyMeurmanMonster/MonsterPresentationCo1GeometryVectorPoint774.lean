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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint186

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Source point 774 is a literal actual Conway image of the prior source point. -/
def monsterCo1GeometryVectorPoint774 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint186

/-- All coordinates are checked against the actual parent action and actual operator matrix. -/
theorem monsterCo1GeometryVectorPoint774_binary :
    monsterCo1GeometryVectorPoint774.val =
      ![1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1] := by
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
    monsterCo1GeometryVectorPoint186.val =
      _
  rw [monsterCo1GeometryVectorPoint186_binary, monsterCo1GeometryTransportOperator_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 11725704 16372555
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
