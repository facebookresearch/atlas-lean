/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal source-generator values of the actual finite universal-module certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPointRegistry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorRowData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorRowTransport

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Each finite certificate value is an original source universal point generator. -/
def monsterCo1GeometryVectorValue (j : Fin 867) : MonsterCo1GeometryUniversalModule :=
  monsterCo1GeometryUniversalPoint (monsterCo1GeometryVectorPoints j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
