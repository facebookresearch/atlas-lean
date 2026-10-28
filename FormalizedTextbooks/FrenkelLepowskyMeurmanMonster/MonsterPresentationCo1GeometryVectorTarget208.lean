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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation017
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation033
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation050
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation054
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation059
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation080
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation159
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation226
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation236
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation255
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation263
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation351
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation376
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation431
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation433
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation445
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation474

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Verify the final sparse row using only prior proved original-source equations.
/-- Target point 208 belongs to the proposed source span by the exact finite source certificate. -/
theorem monsterCo1GeometryVectorTarget208 :
    monsterCo1GeometryVectorValue 208 ∈ monsterCo1GeometryVectorBasisSpan := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow0, monsterCo1GeometryVectorRow1,
      monsterCo1GeometryVectorRow4, monsterCo1GeometryVectorRow5, monsterCo1GeometryVectorRow7,
      monsterCo1GeometryVectorRow11, monsterCo1GeometryVectorRow12,
      monsterCo1GeometryVectorRow14, monsterCo1GeometryVectorRow17,
      monsterCo1GeometryVectorRow20, monsterCo1GeometryVectorRow21,
      monsterCo1GeometryVectorRow33, monsterCo1GeometryVectorRow39,
      monsterCo1GeometryVectorRow44, monsterCo1GeometryVectorRow50,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow54,
      monsterCo1GeometryVectorRow59, monsterCo1GeometryVectorRow80,
      monsterCo1GeometryVectorRow90, monsterCo1GeometryVectorRow97,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow159,
      monsterCo1GeometryVectorRow226, monsterCo1GeometryVectorRow236,
      monsterCo1GeometryVectorRow255, monsterCo1GeometryVectorRow263,
      monsterCo1GeometryVectorRow287, monsterCo1GeometryVectorRow351,
      monsterCo1GeometryVectorRow376, monsterCo1GeometryVectorRow431,
      monsterCo1GeometryVectorRow433, monsterCo1GeometryVectorRow445,
      monsterCo1GeometryVectorRow474] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation0
    · exact monsterCo1GeometryVectorEquation1
    · exact monsterCo1GeometryVectorEquation4
    · exact monsterCo1GeometryVectorEquation5
    · exact monsterCo1GeometryVectorEquation7
    · exact monsterCo1GeometryVectorEquation11
    · exact monsterCo1GeometryVectorEquation12
    · exact monsterCo1GeometryVectorEquation14
    · exact monsterCo1GeometryVectorEquation17
    · exact monsterCo1GeometryVectorEquation20
    · exact monsterCo1GeometryVectorEquation21
    · exact monsterCo1GeometryVectorEquation33
    · exact monsterCo1GeometryVectorEquation39
    · exact monsterCo1GeometryVectorEquation44
    · exact monsterCo1GeometryVectorEquation50
    · exact monsterCo1GeometryVectorEquation52
    · exact monsterCo1GeometryVectorEquation54
    · exact monsterCo1GeometryVectorEquation59
    · exact monsterCo1GeometryVectorEquation80
    · exact monsterCo1GeometryVectorEquation90
    · exact monsterCo1GeometryVectorEquation97
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation159
    · exact monsterCo1GeometryVectorEquation226
    · exact monsterCo1GeometryVectorEquation236
    · exact monsterCo1GeometryVectorEquation255
    · exact monsterCo1GeometryVectorEquation263
    · exact monsterCo1GeometryVectorEquation287
    · exact monsterCo1GeometryVectorEquation351
    · exact monsterCo1GeometryVectorEquation376
    · exact monsterCo1GeometryVectorEquation431
    · exact monsterCo1GeometryVectorEquation433
    · exact monsterCo1GeometryVectorEquation445
    · exact monsterCo1GeometryVectorEquation474
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [208, 2, 3, 4, 5,
      7, 9, 10, 11] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow0,
      monsterCo1GeometryVectorRow1, monsterCo1GeometryVectorRow4, monsterCo1GeometryVectorRow5,
      monsterCo1GeometryVectorRow7, monsterCo1GeometryVectorRow11,
      monsterCo1GeometryVectorRow12, monsterCo1GeometryVectorRow14,
      monsterCo1GeometryVectorRow17, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow21, monsterCo1GeometryVectorRow33,
      monsterCo1GeometryVectorRow39, monsterCo1GeometryVectorRow44,
      monsterCo1GeometryVectorRow50, monsterCo1GeometryVectorRow52,
      monsterCo1GeometryVectorRow54, monsterCo1GeometryVectorRow59,
      monsterCo1GeometryVectorRow80, monsterCo1GeometryVectorRow90,
      monsterCo1GeometryVectorRow97, monsterCo1GeometryVectorRow149,
      monsterCo1GeometryVectorRow159, monsterCo1GeometryVectorRow226,
      monsterCo1GeometryVectorRow236, monsterCo1GeometryVectorRow255,
      monsterCo1GeometryVectorRow263, monsterCo1GeometryVectorRow287,
      monsterCo1GeometryVectorRow351, monsterCo1GeometryVectorRow376,
      monsterCo1GeometryVectorRow431, monsterCo1GeometryVectorRow433,
      monsterCo1GeometryVectorRow445, monsterCo1GeometryVectorRow474] hp
    decide +kernel
  apply monsterCo1GeometryVectorRowEval_leading_mem _ _ 208 [2, 3, 4, 5, 7, 9, 10, 11] _ hs
  have hb : ∀ j ∈ ([2, 3, 4, 5, 7, 9, 10, 11] : List (Fin 867)), j.val < 24 := by decide +kernel
  exact fun j hj => monsterCo1GeometryVectorBasis_mem j (hb j hj)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
