/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation326
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 517 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation517 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow517) = 0 := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow326] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact monsterCo1GeometryVectorEquation326
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [422, 207, 373] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow326] hp
    decide +kernel
  have images : ([546, 452, 374] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([422, 207, 373] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 422) = monsterCo1GeometryVectorValue 546 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint422) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint546
      rw [monsterCo1GeometryVectorAction275]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 207) = monsterCo1GeometryVectorValue 452 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint207) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint452
      rw [monsterCo1GeometryVectorAction237]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 373) = monsterCo1GeometryVectorValue 374 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint373) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint374
      rw [monsterCo1GeometryVectorAction263]
    rw [h0, h1, h2]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5))
    [422, 207, 373] [546, 452, 374] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [546, 452, 374] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow517) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
