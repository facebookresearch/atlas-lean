/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation317
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 502 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation502 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow502) = 0 := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow317] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact monsterCo1GeometryVectorEquation317
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [406, 23, 377] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow317] hp
    decide +kernel
  have images : ([616, 199, 595] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([406, 23, 377] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 406) = monsterCo1GeometryVectorValue 616 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint406) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint616
      rw [monsterCo1GeometryVectorAction411]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 23) = monsterCo1GeometryVectorValue 199 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint23) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint199
      rw [monsterCo1GeometryVectorAction353]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 377) = monsterCo1GeometryVectorValue 595 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint377) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint595
      rw [monsterCo1GeometryVectorAction404]
    rw [h0, h1, h2]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6))
    [406, 23, 377] [616, 199, 595] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [616, 199, 595] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow502) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
