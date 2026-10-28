/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions31
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions33
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions34
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation169
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 327 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation327 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow327) = 0 := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow169] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact monsterCo1GeometryVectorEquation169
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [238, 21, 201] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow169] hp
    decide +kernel
  have images : ([423, 215, 375] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([238, 21, 201] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 238) = monsterCo1GeometryVectorValue 423 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint238) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint423
      rw [monsterCo1GeometryVectorAction830]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 21) = monsterCo1GeometryVectorValue 215 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint21) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint215
      rw [monsterCo1GeometryVectorAction766]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 201) = monsterCo1GeometryVectorValue 375 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint201) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint375
      rw [monsterCo1GeometryVectorAction815]
    rw [h0, h1, h2]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14))
    [238, 21, 201] [423, 215, 375] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [423, 215, 375] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow327) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
