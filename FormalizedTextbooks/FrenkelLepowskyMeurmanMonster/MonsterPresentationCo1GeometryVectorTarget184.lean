/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A literal target generator lies in the twenty-four-point span by prior source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation048
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation050
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation059
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation155
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation203
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation292
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation306
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation353
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation355
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation361
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation373
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation380
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation382
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation484
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation485
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation486
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation491
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation504
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation550
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation585
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation590
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation607

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Verify the final sparse row using only prior proved original-source equations.
/-- Target point 184 belongs to the proposed source span by the exact finite source certificate. -/
theorem monsterCo1GeometryVectorTarget184 :
    monsterCo1GeometryVectorValue 184 ∈ monsterCo1GeometryVectorBasisSpan := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow1, monsterCo1GeometryVectorRow5,
      monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow14,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow39, monsterCo1GeometryVectorRow48,
      monsterCo1GeometryVectorRow50, monsterCo1GeometryVectorRow59,
      monsterCo1GeometryVectorRow97, monsterCo1GeometryVectorRow155,
      monsterCo1GeometryVectorRow203, monsterCo1GeometryVectorRow292,
      monsterCo1GeometryVectorRow306, monsterCo1GeometryVectorRow353,
      monsterCo1GeometryVectorRow355, monsterCo1GeometryVectorRow361,
      monsterCo1GeometryVectorRow373, monsterCo1GeometryVectorRow380,
      monsterCo1GeometryVectorRow382, monsterCo1GeometryVectorRow484,
      monsterCo1GeometryVectorRow485, monsterCo1GeometryVectorRow486,
      monsterCo1GeometryVectorRow491, monsterCo1GeometryVectorRow504,
      monsterCo1GeometryVectorRow550, monsterCo1GeometryVectorRow585,
      monsterCo1GeometryVectorRow590, monsterCo1GeometryVectorRow607] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation1
    · exact monsterCo1GeometryVectorEquation5
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation14
    · exact monsterCo1GeometryVectorEquation18
    · exact monsterCo1GeometryVectorEquation20
    · exact monsterCo1GeometryVectorEquation39
    · exact monsterCo1GeometryVectorEquation48
    · exact monsterCo1GeometryVectorEquation50
    · exact monsterCo1GeometryVectorEquation59
    · exact monsterCo1GeometryVectorEquation97
    · exact monsterCo1GeometryVectorEquation155
    · exact monsterCo1GeometryVectorEquation203
    · exact monsterCo1GeometryVectorEquation292
    · exact monsterCo1GeometryVectorEquation306
    · exact monsterCo1GeometryVectorEquation353
    · exact monsterCo1GeometryVectorEquation355
    · exact monsterCo1GeometryVectorEquation361
    · exact monsterCo1GeometryVectorEquation373
    · exact monsterCo1GeometryVectorEquation380
    · exact monsterCo1GeometryVectorEquation382
    · exact monsterCo1GeometryVectorEquation484
    · exact monsterCo1GeometryVectorEquation485
    · exact monsterCo1GeometryVectorEquation486
    · exact monsterCo1GeometryVectorEquation491
    · exact monsterCo1GeometryVectorEquation504
    · exact monsterCo1GeometryVectorEquation550
    · exact monsterCo1GeometryVectorEquation585
    · exact monsterCo1GeometryVectorEquation590
    · exact monsterCo1GeometryVectorEquation607
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [184, 0, 1, 2, 3,
      5, 7, 8, 10, 12, 13, 21] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow1,
      monsterCo1GeometryVectorRow5, monsterCo1GeometryVectorRow6,
      monsterCo1GeometryVectorRow14, monsterCo1GeometryVectorRow18,
      monsterCo1GeometryVectorRow20, monsterCo1GeometryVectorRow39,
      monsterCo1GeometryVectorRow48, monsterCo1GeometryVectorRow50,
      monsterCo1GeometryVectorRow59, monsterCo1GeometryVectorRow97,
      monsterCo1GeometryVectorRow155, monsterCo1GeometryVectorRow203,
      monsterCo1GeometryVectorRow292, monsterCo1GeometryVectorRow306,
      monsterCo1GeometryVectorRow353, monsterCo1GeometryVectorRow355,
      monsterCo1GeometryVectorRow361, monsterCo1GeometryVectorRow373,
      monsterCo1GeometryVectorRow380, monsterCo1GeometryVectorRow382,
      monsterCo1GeometryVectorRow484, monsterCo1GeometryVectorRow485,
      monsterCo1GeometryVectorRow486, monsterCo1GeometryVectorRow491,
      monsterCo1GeometryVectorRow504, monsterCo1GeometryVectorRow550,
      monsterCo1GeometryVectorRow585, monsterCo1GeometryVectorRow590,
      monsterCo1GeometryVectorRow607] hp
    decide +kernel
  apply monsterCo1GeometryVectorRowEval_leading_mem _ _ 184 [0, 1, 2, 3, 5, 7, 8, 10, 12,
      13, 21] _ hs
  have hb : ∀ j ∈ ([0, 1, 2, 3, 5, 7, 8, 10, 12, 13, 21] : List (Fin 867)), j.val < 24 :=
      by decide +kernel
  exact fun j hj => monsterCo1GeometryVectorBasis_mem j (hb j hj)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
