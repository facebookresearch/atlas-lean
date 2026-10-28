/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete supported coefficient table of the five actual mixed inverse-spin words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinCaseZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinCaseOne
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinCaseTwo
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinCaseThree
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinCaseFour

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every displayed coefficient is calculated by the full actual compact inverse spin word. -/
theorem monsterNortonMixedOddSpinNumerator_coefficient (k : Fin 5) (i : Fin 128) :
    monsterNortonMixedOddSpinNumerator k (monsterNortonMixedOddSpinLabel k i) =
      monsterNortonMixedOddSpinCoefficient k i := by
  fin_cases k
  · exact monsterNortonMixedOddSpinNumerator_coefficient_0 i
  · exact monsterNortonMixedOddSpinNumerator_coefficient_1 i
  · exact monsterNortonMixedOddSpinNumerator_coefficient_2 i
  · exact monsterNortonMixedOddSpinNumerator_coefficient_3 i
  · exact monsterNortonMixedOddSpinNumerator_coefficient_4 i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
