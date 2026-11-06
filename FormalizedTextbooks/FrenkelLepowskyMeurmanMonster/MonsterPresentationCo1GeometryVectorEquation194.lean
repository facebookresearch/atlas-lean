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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation017
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation066
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 194 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation194 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow194) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow17, monsterCo1GeometryVectorRow66] : List (List (Fin
      867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact monsterCo1GeometryVectorEquation17
    · exact monsterCo1GeometryVectorEquation66
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [90, 6, 11, 15] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow17,
      monsterCo1GeometryVectorRow66] hp
    decide +kernel
  have images : ([262, 171, 172, 18] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([90, 6, 11, 15] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 90) = monsterCo1GeometryVectorValue 262 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint90) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint262
      rw [monsterCo1GeometryVectorAction31]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 6) = monsterCo1GeometryVectorValue 171 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint6) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint171
      rw [monsterCo1GeometryVectorAction6]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 11) = monsterCo1GeometryVectorValue 172 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint11) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint172
      rw [monsterCo1GeometryVectorAction11]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 15) = monsterCo1GeometryVectorValue 18 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint15) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint18
      rw [monsterCo1GeometryVectorAction15]
    rw [h0, h1, h2, h3]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0))
    [90, 6, 11, 15] [262, 171, 172, 18] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [262, 171, 172, 18] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow194) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
