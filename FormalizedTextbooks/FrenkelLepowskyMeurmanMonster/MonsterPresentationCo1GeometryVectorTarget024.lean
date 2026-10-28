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

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Verify the final sparse row using only prior proved original-source equations.
/-- Target point 24 belongs to the proposed source span by the exact finite source certificate. -/
theorem monsterCo1GeometryVectorTarget24 :
    monsterCo1GeometryVectorValue 24 ∈ monsterCo1GeometryVectorBasisSpan := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow0] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact monsterCo1GeometryVectorEquation0
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [24, 0, 1] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow0] hp
    decide +kernel
  apply monsterCo1GeometryVectorRowEval_leading_mem _ _ 24 [0, 1] _ hs
  have hb : ∀ j ∈ ([0, 1] : List (Fin 867)), j.val < 24 := by decide +kernel
  exact fun j hj => monsterCo1GeometryVectorBasis_mem j (hb j hj)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
