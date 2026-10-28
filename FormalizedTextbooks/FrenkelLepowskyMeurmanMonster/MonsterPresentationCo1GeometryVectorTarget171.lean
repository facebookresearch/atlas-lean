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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation159
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation226
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation236
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Verify the final sparse row using only prior proved original-source equations.
/-- Target point 171 belongs to the proposed source span by the exact finite source certificate. -/
theorem monsterCo1GeometryVectorTarget171 :
    monsterCo1GeometryVectorValue 171 ∈ monsterCo1GeometryVectorBasisSpan := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow1, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow20, monsterCo1GeometryVectorRow21,
      monsterCo1GeometryVectorRow101, monsterCo1GeometryVectorRow149,
      monsterCo1GeometryVectorRow159, monsterCo1GeometryVectorRow226,
      monsterCo1GeometryVectorRow236, monsterCo1GeometryVectorRow265,
      monsterCo1GeometryVectorRow287] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation1
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation20
    · exact monsterCo1GeometryVectorEquation21
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation159
    · exact monsterCo1GeometryVectorEquation226
    · exact monsterCo1GeometryVectorEquation236
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation287
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [171, 3, 6, 7] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow1,
      monsterCo1GeometryVectorRow15, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow21, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow159,
      monsterCo1GeometryVectorRow226, monsterCo1GeometryVectorRow236,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow287] hp
    decide +kernel
  apply monsterCo1GeometryVectorRowEval_leading_mem _ _ 171 [3, 6, 7] _ hs
  have hb : ∀ j ∈ ([3, 6, 7] : List (Fin 867)), j.val < 24 := by decide +kernel
  exact fun j hj => monsterCo1GeometryVectorBasis_mem j (hb j hj)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
