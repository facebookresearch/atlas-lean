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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation048
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation050
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation059
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation273
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation620
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 631 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation631 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow631) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow7, monsterCo1GeometryVectorRow14,
      monsterCo1GeometryVectorRow39, monsterCo1GeometryVectorRow44,
      monsterCo1GeometryVectorRow48, monsterCo1GeometryVectorRow50,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow59,
      monsterCo1GeometryVectorRow90, monsterCo1GeometryVectorRow97,
      monsterCo1GeometryVectorRow273, monsterCo1GeometryVectorRow620] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation7
    · exact monsterCo1GeometryVectorEquation14
    · exact monsterCo1GeometryVectorEquation39
    · exact monsterCo1GeometryVectorEquation44
    · exact monsterCo1GeometryVectorEquation48
    · exact monsterCo1GeometryVectorEquation50
    · exact monsterCo1GeometryVectorEquation52
    · exact monsterCo1GeometryVectorEquation59
    · exact monsterCo1GeometryVectorEquation90
    · exact monsterCo1GeometryVectorEquation97
    · exact monsterCo1GeometryVectorEquation273
    · exact monsterCo1GeometryVectorEquation620
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [174, 0, 5, 16, 17] = 0 :=
      by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow7,
      monsterCo1GeometryVectorRow14, monsterCo1GeometryVectorRow39,
      monsterCo1GeometryVectorRow44, monsterCo1GeometryVectorRow48,
      monsterCo1GeometryVectorRow50, monsterCo1GeometryVectorRow52,
      monsterCo1GeometryVectorRow59, monsterCo1GeometryVectorRow90,
      monsterCo1GeometryVectorRow97, monsterCo1GeometryVectorRow273,
      monsterCo1GeometryVectorRow620] hp
    decide +kernel
  have images : ([402, 0, 210, 20, 213] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([174, 0, 5, 16, 17] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 174) = monsterCo1GeometryVectorValue 402 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint174) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint402
      rw [monsterCo1GeometryVectorAction801]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 0 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint0
      rw [monsterCo1GeometryVectorAction745]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 5) = monsterCo1GeometryVectorValue 210 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint5) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint210
      rw [monsterCo1GeometryVectorAction750]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 16) = monsterCo1GeometryVectorValue 20 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint16) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint20
      rw [monsterCo1GeometryVectorAction761]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 17) = monsterCo1GeometryVectorValue 213 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint17) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint213
      rw [monsterCo1GeometryVectorAction762]
    rw [h0, h1, h2, h3, h4]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14))
    [174, 0, 5, 16, 17] [402, 0, 210, 20, 213] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [402, 0, 210, 20, 213] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow631) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
