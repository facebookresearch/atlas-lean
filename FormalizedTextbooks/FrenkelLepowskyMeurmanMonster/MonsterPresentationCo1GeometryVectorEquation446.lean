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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation050
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation059
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation271
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 446 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation446 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow446) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow7,
      monsterCo1GeometryVectorRow14, monsterCo1GeometryVectorRow39,
      monsterCo1GeometryVectorRow44, monsterCo1GeometryVectorRow50,
      monsterCo1GeometryVectorRow59, monsterCo1GeometryVectorRow90,
      monsterCo1GeometryVectorRow97, monsterCo1GeometryVectorRow271] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation7
    · exact monsterCo1GeometryVectorEquation14
    · exact monsterCo1GeometryVectorEquation39
    · exact monsterCo1GeometryVectorEquation44
    · exact monsterCo1GeometryVectorEquation50
    · exact monsterCo1GeometryVectorEquation59
    · exact monsterCo1GeometryVectorEquation90
    · exact monsterCo1GeometryVectorEquation97
    · exact monsterCo1GeometryVectorEquation271
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [335, 0, 1, 4, 8, 16] = 0
      := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow6,
      monsterCo1GeometryVectorRow7, monsterCo1GeometryVectorRow14,
      monsterCo1GeometryVectorRow39, monsterCo1GeometryVectorRow44,
      monsterCo1GeometryVectorRow50, monsterCo1GeometryVectorRow59,
      monsterCo1GeometryVectorRow90, monsterCo1GeometryVectorRow97,
      monsterCo1GeometryVectorRow271] hp
    decide +kernel
  have images : ([568, 0, 2, 76, 72, 19] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([335, 0, 1, 4, 8, 16] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 335) = monsterCo1GeometryVectorValue 568 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint335) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint568
      rw [monsterCo1GeometryVectorAction636]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 0 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint0
      rw [monsterCo1GeometryVectorAction467]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 1) = monsterCo1GeometryVectorValue 2 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint1) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint2
      rw [monsterCo1GeometryVectorAction468]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 4) = monsterCo1GeometryVectorValue 76 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint4) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint76
      rw [monsterCo1GeometryVectorAction471]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 8) = monsterCo1GeometryVectorValue 72 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint8) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint72
      rw [monsterCo1GeometryVectorAction475]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 16) = monsterCo1GeometryVectorValue 19 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint16) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint19
      rw [monsterCo1GeometryVectorAction483]
    rw [h0, h1, h2, h3, h4, h5]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13))
    [335, 0, 1, 4, 8, 16] [568, 0, 2, 76, 72, 19] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [568, 0, 2, 76, 72, 19] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow446) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
