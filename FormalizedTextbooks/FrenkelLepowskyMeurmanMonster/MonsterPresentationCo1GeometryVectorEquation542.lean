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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation038
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation048
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation050
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation054
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation057
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation064
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation071
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation086
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation112
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation117
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation129
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation131
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation141
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation159
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation226
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation236
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation266
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation346
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation353
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation376
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation391
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation440
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation441
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation474
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation484
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 542 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation542 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow542) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow5, monsterCo1GeometryVectorRow7,
      monsterCo1GeometryVectorRow11, monsterCo1GeometryVectorRow14,
      monsterCo1GeometryVectorRow15, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow21, monsterCo1GeometryVectorRow23,
      monsterCo1GeometryVectorRow38, monsterCo1GeometryVectorRow39,
      monsterCo1GeometryVectorRow44, monsterCo1GeometryVectorRow48,
      monsterCo1GeometryVectorRow50, monsterCo1GeometryVectorRow54,
      monsterCo1GeometryVectorRow57, monsterCo1GeometryVectorRow64,
      monsterCo1GeometryVectorRow71, monsterCo1GeometryVectorRow86,
      monsterCo1GeometryVectorRow90, monsterCo1GeometryVectorRow97,
      monsterCo1GeometryVectorRow112, monsterCo1GeometryVectorRow117,
      monsterCo1GeometryVectorRow129, monsterCo1GeometryVectorRow131,
      monsterCo1GeometryVectorRow141, monsterCo1GeometryVectorRow149,
      monsterCo1GeometryVectorRow159, monsterCo1GeometryVectorRow226,
      monsterCo1GeometryVectorRow236, monsterCo1GeometryVectorRow266,
      monsterCo1GeometryVectorRow287, monsterCo1GeometryVectorRow346,
      monsterCo1GeometryVectorRow353, monsterCo1GeometryVectorRow376,
      monsterCo1GeometryVectorRow391, monsterCo1GeometryVectorRow440,
      monsterCo1GeometryVectorRow441, monsterCo1GeometryVectorRow474,
      monsterCo1GeometryVectorRow484] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation5
    · exact monsterCo1GeometryVectorEquation7
    · exact monsterCo1GeometryVectorEquation11
    · exact monsterCo1GeometryVectorEquation14
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation20
    · exact monsterCo1GeometryVectorEquation21
    · exact monsterCo1GeometryVectorEquation23
    · exact monsterCo1GeometryVectorEquation38
    · exact monsterCo1GeometryVectorEquation39
    · exact monsterCo1GeometryVectorEquation44
    · exact monsterCo1GeometryVectorEquation48
    · exact monsterCo1GeometryVectorEquation50
    · exact monsterCo1GeometryVectorEquation54
    · exact monsterCo1GeometryVectorEquation57
    · exact monsterCo1GeometryVectorEquation64
    · exact monsterCo1GeometryVectorEquation71
    · exact monsterCo1GeometryVectorEquation86
    · exact monsterCo1GeometryVectorEquation90
    · exact monsterCo1GeometryVectorEquation97
    · exact monsterCo1GeometryVectorEquation112
    · exact monsterCo1GeometryVectorEquation117
    · exact monsterCo1GeometryVectorEquation129
    · exact monsterCo1GeometryVectorEquation131
    · exact monsterCo1GeometryVectorEquation141
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation159
    · exact monsterCo1GeometryVectorEquation226
    · exact monsterCo1GeometryVectorEquation236
    · exact monsterCo1GeometryVectorEquation266
    · exact monsterCo1GeometryVectorEquation287
    · exact monsterCo1GeometryVectorEquation346
    · exact monsterCo1GeometryVectorEquation353
    · exact monsterCo1GeometryVectorEquation376
    · exact monsterCo1GeometryVectorEquation391
    · exact monsterCo1GeometryVectorEquation440
    · exact monsterCo1GeometryVectorEquation441
    · exact monsterCo1GeometryVectorEquation474
    · exact monsterCo1GeometryVectorEquation484
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [468, 0, 4, 5, 8, 9, 12,
      17] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow5,
      monsterCo1GeometryVectorRow7, monsterCo1GeometryVectorRow11,
      monsterCo1GeometryVectorRow14, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow20, monsterCo1GeometryVectorRow21,
      monsterCo1GeometryVectorRow23, monsterCo1GeometryVectorRow38,
      monsterCo1GeometryVectorRow39, monsterCo1GeometryVectorRow44,
      monsterCo1GeometryVectorRow48, monsterCo1GeometryVectorRow50,
      monsterCo1GeometryVectorRow54, monsterCo1GeometryVectorRow57,
      monsterCo1GeometryVectorRow64, monsterCo1GeometryVectorRow71,
      monsterCo1GeometryVectorRow86, monsterCo1GeometryVectorRow90,
      monsterCo1GeometryVectorRow97, monsterCo1GeometryVectorRow112,
      monsterCo1GeometryVectorRow117, monsterCo1GeometryVectorRow129,
      monsterCo1GeometryVectorRow131, monsterCo1GeometryVectorRow141,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow159,
      monsterCo1GeometryVectorRow226, monsterCo1GeometryVectorRow236,
      monsterCo1GeometryVectorRow266, monsterCo1GeometryVectorRow287,
      monsterCo1GeometryVectorRow346, monsterCo1GeometryVectorRow353,
      monsterCo1GeometryVectorRow376, monsterCo1GeometryVectorRow391,
      monsterCo1GeometryVectorRow440, monsterCo1GeometryVectorRow441,
      monsterCo1GeometryVectorRow474, monsterCo1GeometryVectorRow484] hp
    decide +kernel
  have images :
      ([599, 0, 10, 29, 79, 106, 42, 193] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([468, 0, 4, 5, 8, 9, 12, 17] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 468) = monsterCo1GeometryVectorValue 599 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint468) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint599
      rw [monsterCo1GeometryVectorAction421]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 0 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint0
      rw [monsterCo1GeometryVectorAction330]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 4) = monsterCo1GeometryVectorValue 10 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint4) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint10
      rw [monsterCo1GeometryVectorAction334]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 5) = monsterCo1GeometryVectorValue 29 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint5) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint29
      rw [monsterCo1GeometryVectorAction335]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 8) = monsterCo1GeometryVectorValue 79 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint8) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint79
      rw [monsterCo1GeometryVectorAction338]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 9) = monsterCo1GeometryVectorValue 106 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint9) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint106
      rw [monsterCo1GeometryVectorAction339]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 12) = monsterCo1GeometryVectorValue 42 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint12) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint42
      rw [monsterCo1GeometryVectorAction342]
    have h7 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 17) = monsterCo1GeometryVectorValue 193 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint17) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint193
      rw [monsterCo1GeometryVectorAction347]
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6))
    [468, 0, 4, 5, 8, 9, 12, 17] [599, 0, 10, 29, 79, 106, 42, 193] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [599, 0, 10, 29, 79, 106, 42, 193] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow542) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
