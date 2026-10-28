/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation027
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation075
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 206 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation206 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow206) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow27,
      monsterCo1GeometryVectorRow75] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation27
    · exact monsterCo1GeometryVectorEquation75
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [99, 1, 5, 12, 17] = 0 :=
      by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow6,
      monsterCo1GeometryVectorRow27, monsterCo1GeometryVectorRow75] hp
    decide +kernel
  have images : ([273, 1, 5, 12, 181] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([99, 1, 5, 12, 17] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 99) = monsterCo1GeometryVectorValue 273 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint99) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint273
      rw [monsterCo1GeometryVectorAction217]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 1) = monsterCo1GeometryVectorValue 1 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint1) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint1
      rw [monsterCo1GeometryVectorAction190]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 5) = monsterCo1GeometryVectorValue 5 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint5) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint5
      rw [monsterCo1GeometryVectorAction194]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 12) = monsterCo1GeometryVectorValue 12 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint12) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint12
      rw [monsterCo1GeometryVectorAction201]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 17) = monsterCo1GeometryVectorValue 181 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint17) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint181
      rw [monsterCo1GeometryVectorAction206]
    rw [h0, h1, h2, h3, h4]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5))
    [99, 1, 5, 12, 17] [273, 1, 5, 12, 181] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [273, 1, 5, 12, 181] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow206) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
