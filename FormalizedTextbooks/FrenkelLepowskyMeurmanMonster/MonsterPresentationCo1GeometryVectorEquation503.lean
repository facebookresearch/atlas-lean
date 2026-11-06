/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation318
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 503 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation503 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow503) = 0 := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow318] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact monsterCo1GeometryVectorEquation318
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [408, 206, 378] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow318] hp
    decide +kernel
  have images : ([589, 620, 379] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([408, 206, 378] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 408) = monsterCo1GeometryVectorValue 589 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint408) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint589
      rw [monsterCo1GeometryVectorAction412]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 206) = monsterCo1GeometryVectorValue 620 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint206) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint620
      rw [monsterCo1GeometryVectorAction385]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 378) = monsterCo1GeometryVectorValue 379 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint378) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint379
      rw [monsterCo1GeometryVectorAction405]
    rw [h0, h1, h2]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6))
    [408, 206, 378] [589, 620, 379] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [589, 620, 379] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow503) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
