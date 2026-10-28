/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation048
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation190
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 355 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation355 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow355) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow48,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow190] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation48
    · exact monsterCo1GeometryVectorEquation52
    · exact monsterCo1GeometryVectorEquation190
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [258, 1, 203] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow6,
      monsterCo1GeometryVectorRow48, monsterCo1GeometryVectorRow52,
      monsterCo1GeometryVectorRow190] hp
    decide +kernel
  have images : ([475, 1, 392] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([258, 1, 203] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 258) = monsterCo1GeometryVectorValue 475 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint258) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint475
      rw [monsterCo1GeometryVectorAction249]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 1) = monsterCo1GeometryVectorValue 1 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint1) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint1
      rw [monsterCo1GeometryVectorAction190]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 203) = monsterCo1GeometryVectorValue 392 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint203) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint392
      rw [monsterCo1GeometryVectorAction234]
    rw [h0, h1, h2]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5))
    [258, 1, 203] [475, 1, 392] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [475, 1, 392] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow355) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
