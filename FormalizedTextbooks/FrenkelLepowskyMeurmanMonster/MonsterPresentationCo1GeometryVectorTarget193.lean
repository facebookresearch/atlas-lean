/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A literal target generator lies in the twenty-four-point span by prior source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation027
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation054
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation055
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation075
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation485
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation486
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation489
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation529
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation574
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation579
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation585
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation632

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Verify the final sparse row using only prior proved original-source equations.
/-- Target point 193 belongs to the proposed source span by the exact finite source certificate. -/
theorem monsterCo1GeometryVectorTarget193 :
    monsterCo1GeometryVectorValue 193 ∈ monsterCo1GeometryVectorBasisSpan := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow0, monsterCo1GeometryVectorRow1,
      monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow10,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow27, monsterCo1GeometryVectorRow54,
      monsterCo1GeometryVectorRow55, monsterCo1GeometryVectorRow75,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow287,
      monsterCo1GeometryVectorRow485, monsterCo1GeometryVectorRow486,
      monsterCo1GeometryVectorRow489, monsterCo1GeometryVectorRow529,
      monsterCo1GeometryVectorRow574, monsterCo1GeometryVectorRow579,
      monsterCo1GeometryVectorRow585, monsterCo1GeometryVectorRow632] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation0
    · exact monsterCo1GeometryVectorEquation1
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation10
    · exact monsterCo1GeometryVectorEquation18
    · exact monsterCo1GeometryVectorEquation20
    · exact monsterCo1GeometryVectorEquation27
    · exact monsterCo1GeometryVectorEquation54
    · exact monsterCo1GeometryVectorEquation55
    · exact monsterCo1GeometryVectorEquation75
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation287
    · exact monsterCo1GeometryVectorEquation485
    · exact monsterCo1GeometryVectorEquation486
    · exact monsterCo1GeometryVectorEquation489
    · exact monsterCo1GeometryVectorEquation529
    · exact monsterCo1GeometryVectorEquation574
    · exact monsterCo1GeometryVectorEquation579
    · exact monsterCo1GeometryVectorEquation585
    · exact monsterCo1GeometryVectorEquation632
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [193, 0, 1, 4, 5,
      7, 9, 13, 17] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow0,
      monsterCo1GeometryVectorRow1, monsterCo1GeometryVectorRow6,
      monsterCo1GeometryVectorRow10, monsterCo1GeometryVectorRow18,
      monsterCo1GeometryVectorRow20, monsterCo1GeometryVectorRow27,
      monsterCo1GeometryVectorRow54, monsterCo1GeometryVectorRow55,
      monsterCo1GeometryVectorRow75, monsterCo1GeometryVectorRow149,
      monsterCo1GeometryVectorRow287, monsterCo1GeometryVectorRow485,
      monsterCo1GeometryVectorRow486, monsterCo1GeometryVectorRow489,
      monsterCo1GeometryVectorRow529, monsterCo1GeometryVectorRow574,
      monsterCo1GeometryVectorRow579, monsterCo1GeometryVectorRow585,
      monsterCo1GeometryVectorRow632] hp
    decide +kernel
  apply monsterCo1GeometryVectorRowEval_leading_mem _ _ 193 [0, 1, 4, 5, 7, 9, 13, 17] _ hs
  have hb : ∀ j ∈ ([0, 1, 4, 5, 7, 9, 13, 17] : List (Fin 867)), j.val < 24 := by decide +kernel
  exact fun j hj => monsterCo1GeometryVectorBasis_mem j (hb j hj)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
