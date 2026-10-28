/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation016
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation065
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 192 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation192 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow192) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow8, monsterCo1GeometryVectorRow16,
      monsterCo1GeometryVectorRow65] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation8
    · exact monsterCo1GeometryVectorEquation16
    · exact monsterCo1GeometryVectorEquation65
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [89, 0, 3, 6, 11] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow8,
      monsterCo1GeometryVectorRow16, monsterCo1GeometryVectorRow65] hp
    decide +kernel
  have images : ([260, 1, 7, 171, 172] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([89, 0, 3, 6, 11] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 89) = monsterCo1GeometryVectorValue 260 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint89) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint260
      rw [monsterCo1GeometryVectorAction30]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 1 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint1
      rw [monsterCo1GeometryVectorAction0]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 3) = monsterCo1GeometryVectorValue 7 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint3) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint7
      rw [monsterCo1GeometryVectorAction3]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 6) = monsterCo1GeometryVectorValue 171 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint6) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint171
      rw [monsterCo1GeometryVectorAction6]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 11) = monsterCo1GeometryVectorValue 172 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint11) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint172
      rw [monsterCo1GeometryVectorAction11]
    rw [h0, h1, h2, h3, h4]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0))
    [89, 0, 3, 6, 11] [260, 1, 7, 171, 172] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [260, 1, 7, 171, 172] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow192) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
