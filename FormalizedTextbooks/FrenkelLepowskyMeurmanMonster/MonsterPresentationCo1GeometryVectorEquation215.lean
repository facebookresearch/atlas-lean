/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation033
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation041
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation089
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 215 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation215 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow215) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow4, monsterCo1GeometryVectorRow6,
      monsterCo1GeometryVectorRow33, monsterCo1GeometryVectorRow41,
      monsterCo1GeometryVectorRow89] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation4
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation33
    · exact monsterCo1GeometryVectorEquation41
    · exact monsterCo1GeometryVectorEquation89
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [113, 1, 2, 4, 5, 8, 14] =
      0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow4,
      monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow33,
      monsterCo1GeometryVectorRow41, monsterCo1GeometryVectorRow89] hp
    decide +kernel
  have images : ([281, 2, 5, 76, 83, 72, 203] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([113, 1, 2, 4, 5, 8, 14] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 113) = monsterCo1GeometryVectorValue 281 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint113) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint281
      rw [monsterCo1GeometryVectorAction515]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 1) = monsterCo1GeometryVectorValue 2 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint1) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint2
      rw [monsterCo1GeometryVectorAction468]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 2) = monsterCo1GeometryVectorValue 5 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint2) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint5
      rw [monsterCo1GeometryVectorAction469]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 4) = monsterCo1GeometryVectorValue 76 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint4) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint76
      rw [monsterCo1GeometryVectorAction471]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 5) = monsterCo1GeometryVectorValue 83 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint5) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint83
      rw [monsterCo1GeometryVectorAction472]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 8) = monsterCo1GeometryVectorValue 72 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint8) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint72
      rw [monsterCo1GeometryVectorAction475]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 14) = monsterCo1GeometryVectorValue 203 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint14) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint203
      rw [monsterCo1GeometryVectorAction481]
    rw [h0, h1, h2, h3, h4, h5, h6]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13))
    [113, 1, 2, 4, 5, 8, 14] [281, 2, 5, 76, 83, 72, 203] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [281, 2, 5, 76, 83, 72, 203] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow215) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
