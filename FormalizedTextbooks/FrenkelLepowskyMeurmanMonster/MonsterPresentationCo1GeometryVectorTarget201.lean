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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation027
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation050
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation054
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation075
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation155
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation159
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation206
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation226
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation236
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation290
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation306
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation321
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation345
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation355
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation356
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation376
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation380
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation474
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation485
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation486
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation489
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation490
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation491
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
/-- Target point 201 belongs to the proposed source span by the exact finite source certificate. -/
theorem monsterCo1GeometryVectorTarget201 :
    monsterCo1GeometryVectorValue 201 ∈ monsterCo1GeometryVectorBasisSpan := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow0, monsterCo1GeometryVectorRow1,
      monsterCo1GeometryVectorRow5, monsterCo1GeometryVectorRow10,
      monsterCo1GeometryVectorRow11, monsterCo1GeometryVectorRow12,
      monsterCo1GeometryVectorRow15, monsterCo1GeometryVectorRow18,
      monsterCo1GeometryVectorRow21, monsterCo1GeometryVectorRow27,
      monsterCo1GeometryVectorRow39, monsterCo1GeometryVectorRow50,
      monsterCo1GeometryVectorRow54, monsterCo1GeometryVectorRow75,
      monsterCo1GeometryVectorRow97, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow155, monsterCo1GeometryVectorRow159,
      monsterCo1GeometryVectorRow206, monsterCo1GeometryVectorRow226,
      monsterCo1GeometryVectorRow236, monsterCo1GeometryVectorRow265,
      monsterCo1GeometryVectorRow290, monsterCo1GeometryVectorRow306,
      monsterCo1GeometryVectorRow321, monsterCo1GeometryVectorRow345,
      monsterCo1GeometryVectorRow355, monsterCo1GeometryVectorRow356,
      monsterCo1GeometryVectorRow376, monsterCo1GeometryVectorRow380,
      monsterCo1GeometryVectorRow474, monsterCo1GeometryVectorRow485,
      monsterCo1GeometryVectorRow486, monsterCo1GeometryVectorRow489,
      monsterCo1GeometryVectorRow490, monsterCo1GeometryVectorRow491,
      monsterCo1GeometryVectorRow529, monsterCo1GeometryVectorRow574,
      monsterCo1GeometryVectorRow579, monsterCo1GeometryVectorRow585,
      monsterCo1GeometryVectorRow632] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation0
    · exact monsterCo1GeometryVectorEquation1
    · exact monsterCo1GeometryVectorEquation5
    · exact monsterCo1GeometryVectorEquation10
    · exact monsterCo1GeometryVectorEquation11
    · exact monsterCo1GeometryVectorEquation12
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation18
    · exact monsterCo1GeometryVectorEquation21
    · exact monsterCo1GeometryVectorEquation27
    · exact monsterCo1GeometryVectorEquation39
    · exact monsterCo1GeometryVectorEquation50
    · exact monsterCo1GeometryVectorEquation54
    · exact monsterCo1GeometryVectorEquation75
    · exact monsterCo1GeometryVectorEquation97
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation155
    · exact monsterCo1GeometryVectorEquation159
    · exact monsterCo1GeometryVectorEquation206
    · exact monsterCo1GeometryVectorEquation226
    · exact monsterCo1GeometryVectorEquation236
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation290
    · exact monsterCo1GeometryVectorEquation306
    · exact monsterCo1GeometryVectorEquation321
    · exact monsterCo1GeometryVectorEquation345
    · exact monsterCo1GeometryVectorEquation355
    · exact monsterCo1GeometryVectorEquation356
    · exact monsterCo1GeometryVectorEquation376
    · exact monsterCo1GeometryVectorEquation380
    · exact monsterCo1GeometryVectorEquation474
    · exact monsterCo1GeometryVectorEquation485
    · exact monsterCo1GeometryVectorEquation486
    · exact monsterCo1GeometryVectorEquation489
    · exact monsterCo1GeometryVectorEquation490
    · exact monsterCo1GeometryVectorEquation491
    · exact monsterCo1GeometryVectorEquation529
    · exact monsterCo1GeometryVectorEquation574
    · exact monsterCo1GeometryVectorEquation579
    · exact monsterCo1GeometryVectorEquation585
    · exact monsterCo1GeometryVectorEquation632
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [201, 1, 3, 4, 5,
      6, 7, 8, 13] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow0,
      monsterCo1GeometryVectorRow1, monsterCo1GeometryVectorRow5,
      monsterCo1GeometryVectorRow10, monsterCo1GeometryVectorRow11,
      monsterCo1GeometryVectorRow12, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow21,
      monsterCo1GeometryVectorRow27, monsterCo1GeometryVectorRow39,
      monsterCo1GeometryVectorRow50, monsterCo1GeometryVectorRow54,
      monsterCo1GeometryVectorRow75, monsterCo1GeometryVectorRow97,
      monsterCo1GeometryVectorRow101, monsterCo1GeometryVectorRow155,
      monsterCo1GeometryVectorRow159, monsterCo1GeometryVectorRow206,
      monsterCo1GeometryVectorRow226, monsterCo1GeometryVectorRow236,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow290,
      monsterCo1GeometryVectorRow306, monsterCo1GeometryVectorRow321,
      monsterCo1GeometryVectorRow345, monsterCo1GeometryVectorRow355,
      monsterCo1GeometryVectorRow356, monsterCo1GeometryVectorRow376,
      monsterCo1GeometryVectorRow380, monsterCo1GeometryVectorRow474,
      monsterCo1GeometryVectorRow485, monsterCo1GeometryVectorRow486,
      monsterCo1GeometryVectorRow489, monsterCo1GeometryVectorRow490,
      monsterCo1GeometryVectorRow491, monsterCo1GeometryVectorRow529,
      monsterCo1GeometryVectorRow574, monsterCo1GeometryVectorRow579,
      monsterCo1GeometryVectorRow585, monsterCo1GeometryVectorRow632] hp
    decide +kernel
  apply monsterCo1GeometryVectorRowEval_leading_mem _ _ 201 [1, 3, 4, 5, 6, 7, 8, 13] _ hs
  have hb : ∀ j ∈ ([1, 3, 4, 5, 6, 7, 8, 13] : List (Fin 867)), j.val < 24 := by decide +kernel
  exact fun j hj => monsterCo1GeometryVectorBasis_mem j (hb j hj)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
