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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation055
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation159
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation203
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation226
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation236
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation485
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation486
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation489
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation529
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation554
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation574
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation579
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation585
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 715 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation715 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow715) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow0, monsterCo1GeometryVectorRow5,
      monsterCo1GeometryVectorRow12, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow20, monsterCo1GeometryVectorRow21,
      monsterCo1GeometryVectorRow55, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow159, monsterCo1GeometryVectorRow203,
      monsterCo1GeometryVectorRow226, monsterCo1GeometryVectorRow236,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow485,
      monsterCo1GeometryVectorRow486, monsterCo1GeometryVectorRow489,
      monsterCo1GeometryVectorRow529, monsterCo1GeometryVectorRow554,
      monsterCo1GeometryVectorRow574, monsterCo1GeometryVectorRow579,
      monsterCo1GeometryVectorRow585] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation0
    · exact monsterCo1GeometryVectorEquation5
    · exact monsterCo1GeometryVectorEquation12
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation20
    · exact monsterCo1GeometryVectorEquation21
    · exact monsterCo1GeometryVectorEquation55
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation159
    · exact monsterCo1GeometryVectorEquation203
    · exact monsterCo1GeometryVectorEquation226
    · exact monsterCo1GeometryVectorEquation236
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation485
    · exact monsterCo1GeometryVectorEquation486
    · exact monsterCo1GeometryVectorEquation489
    · exact monsterCo1GeometryVectorEquation529
    · exact monsterCo1GeometryVectorEquation554
    · exact monsterCo1GeometryVectorEquation574
    · exact monsterCo1GeometryVectorEquation579
    · exact monsterCo1GeometryVectorEquation585
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [698, 1, 2, 3, 4, 5, 6, 7,
      8, 17, 532] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow0,
      monsterCo1GeometryVectorRow5, monsterCo1GeometryVectorRow12,
      monsterCo1GeometryVectorRow15, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow21, monsterCo1GeometryVectorRow55,
      monsterCo1GeometryVectorRow101, monsterCo1GeometryVectorRow159,
      monsterCo1GeometryVectorRow203, monsterCo1GeometryVectorRow226,
      monsterCo1GeometryVectorRow236, monsterCo1GeometryVectorRow265,
      monsterCo1GeometryVectorRow485, monsterCo1GeometryVectorRow486,
      monsterCo1GeometryVectorRow489, monsterCo1GeometryVectorRow529,
      monsterCo1GeometryVectorRow554, monsterCo1GeometryVectorRow574,
      monsterCo1GeometryVectorRow579, monsterCo1GeometryVectorRow585] hp
    decide +kernel
  have images :
      ([825, 1, 25, 3, 9, 5, 32, 13, 78, 181, 730] : List (Fin 867)).map
      monsterCo1GeometryVectorValue =
      (([698, 1, 2, 3, 4, 5, 6, 7, 8, 17, 532] :
      List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 698) = monsterCo1GeometryVectorValue 825 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint698) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint825
      rw [monsterCo1GeometryVectorAction311]
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
        (monsterCo1GeometryVectorValue 4) = monsterCo1GeometryVectorValue 9 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint4) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint9
      rw [monsterCo1GeometryVectorAction193]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 5) = monsterCo1GeometryVectorValue 5 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint5) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint5
      rw [monsterCo1GeometryVectorAction194]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 6) = monsterCo1GeometryVectorValue 32 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint6) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint32
      rw [monsterCo1GeometryVectorAction195]
    have h7 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 7) = monsterCo1GeometryVectorValue 13 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint7) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint13
      rw [monsterCo1GeometryVectorAction196]
    have h8 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 8) = monsterCo1GeometryVectorValue 78 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint8) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint78
      rw [monsterCo1GeometryVectorAction197]
    have h9 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 17) = monsterCo1GeometryVectorValue 181 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint17) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint181
      rw [monsterCo1GeometryVectorAction206]
    have h10 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 532) = monsterCo1GeometryVectorValue 730 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint532) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint730
      rw [monsterCo1GeometryVectorAction301]
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5))
    [698, 1, 2, 3, 4, 5, 6, 7, 8, 17, 532] [825, 1, 25, 3, 9, 5, 32, 13, 78, 181, 730] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [825, 1, 25, 3, 9, 5, 32, 13, 78, 181, 730] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow715) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
