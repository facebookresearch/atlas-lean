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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions29
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation038
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation045
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation054
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation055
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation057
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation064
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation071
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation086
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation091
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation112
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation117
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation129
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation131
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation141
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation159
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation195
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation238
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation261
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation476
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation483
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation493
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation522
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation533
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation544
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation566
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation586
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation587
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation612
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation633
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation634
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation638
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation661
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation663
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation768
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 774 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation774 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow774) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow1, monsterCo1GeometryVectorRow6,
      monsterCo1GeometryVectorRow12, monsterCo1GeometryVectorRow14,
      monsterCo1GeometryVectorRow15, monsterCo1GeometryVectorRow21,
      monsterCo1GeometryVectorRow23, monsterCo1GeometryVectorRow38,
      monsterCo1GeometryVectorRow45, monsterCo1GeometryVectorRow54,
      monsterCo1GeometryVectorRow55, monsterCo1GeometryVectorRow57,
      monsterCo1GeometryVectorRow64, monsterCo1GeometryVectorRow71,
      monsterCo1GeometryVectorRow86, monsterCo1GeometryVectorRow91,
      monsterCo1GeometryVectorRow112, monsterCo1GeometryVectorRow117,
      monsterCo1GeometryVectorRow129, monsterCo1GeometryVectorRow131,
      monsterCo1GeometryVectorRow141, monsterCo1GeometryVectorRow159,
      monsterCo1GeometryVectorRow195, monsterCo1GeometryVectorRow238,
      monsterCo1GeometryVectorRow261, monsterCo1GeometryVectorRow476,
      monsterCo1GeometryVectorRow483, monsterCo1GeometryVectorRow493,
      monsterCo1GeometryVectorRow522, monsterCo1GeometryVectorRow533,
      monsterCo1GeometryVectorRow544, monsterCo1GeometryVectorRow566,
      monsterCo1GeometryVectorRow586, monsterCo1GeometryVectorRow587,
      monsterCo1GeometryVectorRow612, monsterCo1GeometryVectorRow633,
      monsterCo1GeometryVectorRow634, monsterCo1GeometryVectorRow638,
      monsterCo1GeometryVectorRow661, monsterCo1GeometryVectorRow663,
      monsterCo1GeometryVectorRow768] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation1
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation12
    · exact monsterCo1GeometryVectorEquation14
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation21
    · exact monsterCo1GeometryVectorEquation23
    · exact monsterCo1GeometryVectorEquation38
    · exact monsterCo1GeometryVectorEquation45
    · exact monsterCo1GeometryVectorEquation54
    · exact monsterCo1GeometryVectorEquation55
    · exact monsterCo1GeometryVectorEquation57
    · exact monsterCo1GeometryVectorEquation64
    · exact monsterCo1GeometryVectorEquation71
    · exact monsterCo1GeometryVectorEquation86
    · exact monsterCo1GeometryVectorEquation91
    · exact monsterCo1GeometryVectorEquation112
    · exact monsterCo1GeometryVectorEquation117
    · exact monsterCo1GeometryVectorEquation129
    · exact monsterCo1GeometryVectorEquation131
    · exact monsterCo1GeometryVectorEquation141
    · exact monsterCo1GeometryVectorEquation159
    · exact monsterCo1GeometryVectorEquation195
    · exact monsterCo1GeometryVectorEquation238
    · exact monsterCo1GeometryVectorEquation261
    · exact monsterCo1GeometryVectorEquation476
    · exact monsterCo1GeometryVectorEquation483
    · exact monsterCo1GeometryVectorEquation493
    · exact monsterCo1GeometryVectorEquation522
    · exact monsterCo1GeometryVectorEquation533
    · exact monsterCo1GeometryVectorEquation544
    · exact monsterCo1GeometryVectorEquation566
    · exact monsterCo1GeometryVectorEquation586
    · exact monsterCo1GeometryVectorEquation587
    · exact monsterCo1GeometryVectorEquation612
    · exact monsterCo1GeometryVectorEquation633
    · exact monsterCo1GeometryVectorEquation634
    · exact monsterCo1GeometryVectorEquation638
    · exact monsterCo1GeometryVectorEquation661
    · exact monsterCo1GeometryVectorEquation663
    · exact monsterCo1GeometryVectorEquation768
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [649, 0, 2, 3, 8, 9, 11,
      12, 15, 19, 204, 214] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow1,
      monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow12,
      monsterCo1GeometryVectorRow14, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow21, monsterCo1GeometryVectorRow23,
      monsterCo1GeometryVectorRow38, monsterCo1GeometryVectorRow45,
      monsterCo1GeometryVectorRow54, monsterCo1GeometryVectorRow55,
      monsterCo1GeometryVectorRow57, monsterCo1GeometryVectorRow64,
      monsterCo1GeometryVectorRow71, monsterCo1GeometryVectorRow86,
      monsterCo1GeometryVectorRow91, monsterCo1GeometryVectorRow112,
      monsterCo1GeometryVectorRow117, monsterCo1GeometryVectorRow129,
      monsterCo1GeometryVectorRow131, monsterCo1GeometryVectorRow141,
      monsterCo1GeometryVectorRow159, monsterCo1GeometryVectorRow195,
      monsterCo1GeometryVectorRow238, monsterCo1GeometryVectorRow261,
      monsterCo1GeometryVectorRow476, monsterCo1GeometryVectorRow483,
      monsterCo1GeometryVectorRow493, monsterCo1GeometryVectorRow522,
      monsterCo1GeometryVectorRow533, monsterCo1GeometryVectorRow544,
      monsterCo1GeometryVectorRow566, monsterCo1GeometryVectorRow586,
      monsterCo1GeometryVectorRow587, monsterCo1GeometryVectorRow612,
      monsterCo1GeometryVectorRow633, monsterCo1GeometryVectorRow634,
      monsterCo1GeometryVectorRow638, monsterCo1GeometryVectorRow661,
      monsterCo1GeometryVectorRow663, monsterCo1GeometryVectorRow768] hp
    decide +kernel
  have images :
      ([801, 0, 5, 200, 72, 121, 16, 201, 192, 205, 432, 537] : List (Fin 867)).map
      monsterCo1GeometryVectorValue =
      (([649, 0, 2, 3, 8, 9, 11, 12, 15, 19, 204, 214] :
      List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 649) = monsterCo1GeometryVectorValue 801 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint649) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint801
      rw [monsterCo1GeometryVectorAction714]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 0 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint0
      rw [monsterCo1GeometryVectorAction467]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 2) = monsterCo1GeometryVectorValue 5 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint2) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint5
      rw [monsterCo1GeometryVectorAction469]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 3) = monsterCo1GeometryVectorValue 200 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint3) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint200
      rw [monsterCo1GeometryVectorAction470]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 8) = monsterCo1GeometryVectorValue 72 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint8) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint72
      rw [monsterCo1GeometryVectorAction475]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 9) = monsterCo1GeometryVectorValue 121 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint9) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint121
      rw [monsterCo1GeometryVectorAction476]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 11) = monsterCo1GeometryVectorValue 16 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint11) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint16
      rw [monsterCo1GeometryVectorAction478]
    have h7 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 12) = monsterCo1GeometryVectorValue 201 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint12) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint201
      rw [monsterCo1GeometryVectorAction479]
    have h8 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 15) = monsterCo1GeometryVectorValue 192 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint15) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint192
      rw [monsterCo1GeometryVectorAction482]
    have h9 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 19) = monsterCo1GeometryVectorValue 205 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint19) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint205
      rw [monsterCo1GeometryVectorAction486]
    have h10 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 204) = monsterCo1GeometryVectorValue 432 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint204) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint432
      rw [monsterCo1GeometryVectorAction563]
    have h11 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 214) = monsterCo1GeometryVectorValue 537 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint214) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint537
      rw [monsterCo1GeometryVectorAction571]
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13))
      [649, 0, 2, 3, 8, 9, 11, 12, 15, 19, 204, 214] [801, 0, 5, 200, 72, 121, 16, 201, 192,
      205, 432, 537] images hs
  have hc :
      monsterCo1GeometryVectorRowNormalize [801, 0, 5, 200, 72, 121, 16, 201, 192, 205, 432,
      537] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow774) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
