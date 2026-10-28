/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation202
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 370 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation370 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow370) = 0 := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow202] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact monsterCo1GeometryVectorEquation202
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [269, 0, 3, 211, 213] = 0
      := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow202] hp
    decide +kernel
  have images : ([490, 0, 200, 378, 416] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([269, 0, 3, 211, 213] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 269) = monsterCo1GeometryVectorValue 490 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint269) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint490
      rw [monsterCo1GeometryVectorAction607]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 0 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint0
      rw [monsterCo1GeometryVectorAction467]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 3) = monsterCo1GeometryVectorValue 200 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint3) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint200
      rw [monsterCo1GeometryVectorAction470]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 211) = monsterCo1GeometryVectorValue 378 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint211) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint378
      rw [monsterCo1GeometryVectorAction569]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 213) = monsterCo1GeometryVectorValue 416 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint213) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint416
      rw [monsterCo1GeometryVectorAction570]
    rw [h0, h1, h2, h3, h4]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13))
    [269, 0, 3, 211, 213] [490, 0, 200, 378, 416] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [490, 0, 200, 378, 416] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow370) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
