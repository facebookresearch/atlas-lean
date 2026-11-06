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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation017
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation033
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation054
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation055
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation080
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation159
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation226
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation236
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation425
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation577
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation653
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 659 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation659 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow659) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow1, monsterCo1GeometryVectorRow4,
      monsterCo1GeometryVectorRow15, monsterCo1GeometryVectorRow17,
      monsterCo1GeometryVectorRow20, monsterCo1GeometryVectorRow21,
      monsterCo1GeometryVectorRow33, monsterCo1GeometryVectorRow54,
      monsterCo1GeometryVectorRow55, monsterCo1GeometryVectorRow80,
      monsterCo1GeometryVectorRow101, monsterCo1GeometryVectorRow149,
      monsterCo1GeometryVectorRow159, monsterCo1GeometryVectorRow226,
      monsterCo1GeometryVectorRow236, monsterCo1GeometryVectorRow265,
      monsterCo1GeometryVectorRow287, monsterCo1GeometryVectorRow425,
      monsterCo1GeometryVectorRow577, monsterCo1GeometryVectorRow653] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation1
    · exact monsterCo1GeometryVectorEquation4
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation17
    · exact monsterCo1GeometryVectorEquation20
    · exact monsterCo1GeometryVectorEquation21
    · exact monsterCo1GeometryVectorEquation33
    · exact monsterCo1GeometryVectorEquation54
    · exact monsterCo1GeometryVectorEquation55
    · exact monsterCo1GeometryVectorEquation80
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation159
    · exact monsterCo1GeometryVectorEquation226
    · exact monsterCo1GeometryVectorEquation236
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation287
    · exact monsterCo1GeometryVectorEquation425
    · exact monsterCo1GeometryVectorEquation577
    · exact monsterCo1GeometryVectorEquation653
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [458, 1, 2, 3, 6, 9, 10,
      13, 15, 440] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow1,
      monsterCo1GeometryVectorRow4, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow17, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow21, monsterCo1GeometryVectorRow33,
      monsterCo1GeometryVectorRow54, monsterCo1GeometryVectorRow55,
      monsterCo1GeometryVectorRow80, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow159,
      monsterCo1GeometryVectorRow226, monsterCo1GeometryVectorRow236,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow287,
      monsterCo1GeometryVectorRow425, monsterCo1GeometryVectorRow577,
      monsterCo1GeometryVectorRow653] hp
    decide +kernel
  have images :
      ([683, 1, 25, 3, 32, 4, 106, 7, 11, 657] : List (Fin 867)).map
      monsterCo1GeometryVectorValue =
      (([458, 1, 2, 3, 6, 9, 10, 13, 15, 440] :
      List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 458) = monsterCo1GeometryVectorValue 683 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint458) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint683
      rw [monsterCo1GeometryVectorAction287]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 1) = monsterCo1GeometryVectorValue 1 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint1) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint1
      rw [monsterCo1GeometryVectorAction190]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 2) = monsterCo1GeometryVectorValue 25 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint2) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint25
      rw [monsterCo1GeometryVectorAction191]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 3) = monsterCo1GeometryVectorValue 3 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint3) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint3
      rw [monsterCo1GeometryVectorAction192]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 6) = monsterCo1GeometryVectorValue 32 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint6) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint32
      rw [monsterCo1GeometryVectorAction195]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 9) = monsterCo1GeometryVectorValue 4 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint9) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint4
      rw [monsterCo1GeometryVectorAction198]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 10) = monsterCo1GeometryVectorValue 106 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint10) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint106
      rw [monsterCo1GeometryVectorAction199]
    have h7 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 13) = monsterCo1GeometryVectorValue 7 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint13) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint7
      rw [monsterCo1GeometryVectorAction202]
    have h8 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 15) = monsterCo1GeometryVectorValue 11 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint15) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint11
      rw [monsterCo1GeometryVectorAction204]
    have h9 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 440) = monsterCo1GeometryVectorValue 657 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint440) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint657
      rw [monsterCo1GeometryVectorAction282]
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5))
    [458, 1, 2, 3, 6, 9, 10, 13, 15, 440] [683, 1, 25, 3, 32, 4, 106, 7, 11, 657] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [683, 1, 25, 3, 32, 4, 106, 7, 11, 657] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow659) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
