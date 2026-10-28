/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A literal target generator lies in the twenty-four-point span by prior source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorBasis

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Verify the final sparse row using only prior proved original-source equations.
/-- Target point 21 belongs to the proposed source span by the exact finite source certificate. -/
theorem monsterCo1GeometryVectorTarget21 :
    monsterCo1GeometryVectorValue 21 ∈ monsterCo1GeometryVectorBasisSpan := by
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [21, 21] = 0 :=
    monsterCo1GeometryVectorRowEval_zero_of_normalize _ _ (by decide +kernel)
  apply monsterCo1GeometryVectorRowEval_leading_mem _ _ 21 [21] _ hs
  have hb : ∀ j ∈ ([21] : List (Fin 867)), j.val < 24 := by decide +kernel
  exact fun j hj => monsterCo1GeometryVectorBasis_mem j (hb j hj)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
