/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A literal target generator lies in the twenty-four-point span by prior source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation090

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Verify the final sparse row using only prior proved original-source equations.
/-- Target point 114 belongs to the proposed source span by the exact finite source certificate. -/
theorem monsterCo1GeometryVectorTarget114 :
    monsterCo1GeometryVectorValue 114 ∈ monsterCo1GeometryVectorBasisSpan := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow7, monsterCo1GeometryVectorRow11,
      monsterCo1GeometryVectorRow44, monsterCo1GeometryVectorRow90] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation7
    · exact monsterCo1GeometryVectorEquation11
    · exact monsterCo1GeometryVectorEquation44
    · exact monsterCo1GeometryVectorEquation90
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [114, 2, 4, 5, 8,
      10] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow7,
      monsterCo1GeometryVectorRow11, monsterCo1GeometryVectorRow44,
      monsterCo1GeometryVectorRow90] hp
    decide +kernel
  apply monsterCo1GeometryVectorRowEval_leading_mem _ _ 114 [2, 4, 5, 8, 10] _ hs
  have hb : ∀ j ∈ ([2, 4, 5, 8, 10] : List (Fin 867)), j.val < 24 := by decide +kernel
  exact fun j hj => monsterCo1GeometryVectorBasis_mem j (hb j hj)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
