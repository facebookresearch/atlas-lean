/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation017
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation033
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation055
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation080
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation255
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation351
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation430
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation431
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation433
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation442
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation465
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation510
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation565
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation567
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 683 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation683 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow683) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow4, monsterCo1GeometryVectorRow5,
      monsterCo1GeometryVectorRow10, monsterCo1GeometryVectorRow12,
      monsterCo1GeometryVectorRow15, monsterCo1GeometryVectorRow17,
      monsterCo1GeometryVectorRow20, monsterCo1GeometryVectorRow33,
      monsterCo1GeometryVectorRow55, monsterCo1GeometryVectorRow80,
      monsterCo1GeometryVectorRow101, monsterCo1GeometryVectorRow149,
      monsterCo1GeometryVectorRow255, monsterCo1GeometryVectorRow265,
      monsterCo1GeometryVectorRow287, monsterCo1GeometryVectorRow351,
      monsterCo1GeometryVectorRow430, monsterCo1GeometryVectorRow431,
      monsterCo1GeometryVectorRow433, monsterCo1GeometryVectorRow442,
      monsterCo1GeometryVectorRow465, monsterCo1GeometryVectorRow510,
      monsterCo1GeometryVectorRow565, monsterCo1GeometryVectorRow567] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation4
    · exact monsterCo1GeometryVectorEquation5
    · exact monsterCo1GeometryVectorEquation10
    · exact monsterCo1GeometryVectorEquation12
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation17
    · exact monsterCo1GeometryVectorEquation20
    · exact monsterCo1GeometryVectorEquation33
    · exact monsterCo1GeometryVectorEquation55
    · exact monsterCo1GeometryVectorEquation80
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation255
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation287
    · exact monsterCo1GeometryVectorEquation351
    · exact monsterCo1GeometryVectorEquation430
    · exact monsterCo1GeometryVectorEquation431
    · exact monsterCo1GeometryVectorEquation433
    · exact monsterCo1GeometryVectorEquation442
    · exact monsterCo1GeometryVectorEquation465
    · exact monsterCo1GeometryVectorEquation510
    · exact monsterCo1GeometryVectorEquation565
    · exact monsterCo1GeometryVectorEquation567
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [631, 0, 1, 5, 6, 11, 13,
      18, 414] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow4,
      monsterCo1GeometryVectorRow5, monsterCo1GeometryVectorRow10,
      monsterCo1GeometryVectorRow12, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow17, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow33, monsterCo1GeometryVectorRow55,
      monsterCo1GeometryVectorRow80, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow255,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow287,
      monsterCo1GeometryVectorRow351, monsterCo1GeometryVectorRow430,
      monsterCo1GeometryVectorRow431, monsterCo1GeometryVectorRow433,
      monsterCo1GeometryVectorRow442, monsterCo1GeometryVectorRow465,
      monsterCo1GeometryVectorRow510, monsterCo1GeometryVectorRow565,
      monsterCo1GeometryVectorRow567] hp
    decide +kernel
  have images :
      ([790, 0, 1, 29, 32, 188, 189, 194, 628] : List (Fin 867)).map
      monsterCo1GeometryVectorValue =
      (([631, 0, 1, 5, 6, 11, 13, 18, 414] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 631) = monsterCo1GeometryVectorValue 790 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint631) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint790
      rw [monsterCo1GeometryVectorAction444]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 0 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint0
      rw [monsterCo1GeometryVectorAction330]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 1) = monsterCo1GeometryVectorValue 1 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint1) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint1
      rw [monsterCo1GeometryVectorAction331]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 5) = monsterCo1GeometryVectorValue 29 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint5) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint29
      rw [monsterCo1GeometryVectorAction335]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 6) = monsterCo1GeometryVectorValue 32 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint6) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint32
      rw [monsterCo1GeometryVectorAction336]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 11) = monsterCo1GeometryVectorValue 188 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint11) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint188
      rw [monsterCo1GeometryVectorAction341]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 13) = monsterCo1GeometryVectorValue 189 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint13) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint189
      rw [monsterCo1GeometryVectorAction343]
    have h7 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 18) = monsterCo1GeometryVectorValue 194 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint18) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint194
      rw [monsterCo1GeometryVectorAction348]
    have h8 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 414) = monsterCo1GeometryVectorValue 628 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint414) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint628
      rw [monsterCo1GeometryVectorAction413]
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6))
    [631, 0, 1, 5, 6, 11, 13, 18, 414] [790, 0, 1, 29, 32, 188, 189, 194, 628] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [790, 0, 1, 29, 32, 188, 189, 194, 628] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow683) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
