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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions37
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation048
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation292
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation388
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation551
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation552
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 570 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation570 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow570) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow1, monsterCo1GeometryVectorRow6,
      monsterCo1GeometryVectorRow48, monsterCo1GeometryVectorRow52,
      monsterCo1GeometryVectorRow292, monsterCo1GeometryVectorRow388,
      monsterCo1GeometryVectorRow551, monsterCo1GeometryVectorRow552] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation1
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation48
    · exact monsterCo1GeometryVectorEquation52
    · exact monsterCo1GeometryVectorEquation292
    · exact monsterCo1GeometryVectorEquation388
    · exact monsterCo1GeometryVectorEquation551
    · exact monsterCo1GeometryVectorEquation552
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [504, 1, 2, 5, 14, 16, 190,
      192, 204] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow1,
      monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow48,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow292,
      monsterCo1GeometryVectorRow388, monsterCo1GeometryVectorRow551,
      monsterCo1GeometryVectorRow552] hp
    decide +kernel
  have images :
      ([711, 3, 6, 210, 212, 20, 383, 398, 433] : List (Fin 867)).map
      monsterCo1GeometryVectorValue =
      (([504, 1, 2, 5, 14, 16, 190, 192, 204] :
      List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 504) = monsterCo1GeometryVectorValue 711 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint504) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint711
      rw [monsterCo1GeometryVectorAction904]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 1) = monsterCo1GeometryVectorValue 3 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint1) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint3
      rw [monsterCo1GeometryVectorAction746]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 2) = monsterCo1GeometryVectorValue 6 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint2) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint6
      rw [monsterCo1GeometryVectorAction747]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 5) = monsterCo1GeometryVectorValue 210 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint5) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint210
      rw [monsterCo1GeometryVectorAction750]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 14) = monsterCo1GeometryVectorValue 212 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint14) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint212
      rw [monsterCo1GeometryVectorAction759]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 16) = monsterCo1GeometryVectorValue 20 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint16) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint20
      rw [monsterCo1GeometryVectorAction761]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 190) = monsterCo1GeometryVectorValue 383 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint190) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint383
      rw [monsterCo1GeometryVectorAction807]
    have h7 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 192) = monsterCo1GeometryVectorValue 398 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint192) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint398
      rw [monsterCo1GeometryVectorAction808]
    have h8 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 204) = monsterCo1GeometryVectorValue 433 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint204) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint433
      rw [monsterCo1GeometryVectorAction817]
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14))
    [504, 1, 2, 5, 14, 16, 190, 192, 204] [711, 3, 6, 210, 212, 20, 383, 398, 433] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [711, 3, 6, 210, 212, 20, 383, 398, 433] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow570) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
