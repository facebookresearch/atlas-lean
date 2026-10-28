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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation027
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation038
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation057
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation059
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation064
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation071
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation075
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation086
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation112
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation117
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation129
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation131
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation141
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation155
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation266
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation290
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation297
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation321
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation345
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation347
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation356
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation391
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation426
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation440
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation441
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation459
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation461
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation468
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation481
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation482
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation490
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation521
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation542
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 543 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation543 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow543) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow0, monsterCo1GeometryVectorRow6,
      monsterCo1GeometryVectorRow7, monsterCo1GeometryVectorRow12,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow23,
      monsterCo1GeometryVectorRow27, monsterCo1GeometryVectorRow38,
      monsterCo1GeometryVectorRow44, monsterCo1GeometryVectorRow52,
      monsterCo1GeometryVectorRow57, monsterCo1GeometryVectorRow59,
      monsterCo1GeometryVectorRow64, monsterCo1GeometryVectorRow71,
      monsterCo1GeometryVectorRow75, monsterCo1GeometryVectorRow86,
      monsterCo1GeometryVectorRow90, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow112, monsterCo1GeometryVectorRow117,
      monsterCo1GeometryVectorRow129, monsterCo1GeometryVectorRow131,
      monsterCo1GeometryVectorRow141, monsterCo1GeometryVectorRow155,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow266,
      monsterCo1GeometryVectorRow290, monsterCo1GeometryVectorRow297,
      monsterCo1GeometryVectorRow321, monsterCo1GeometryVectorRow345,
      monsterCo1GeometryVectorRow347, monsterCo1GeometryVectorRow356,
      monsterCo1GeometryVectorRow391, monsterCo1GeometryVectorRow426,
      monsterCo1GeometryVectorRow440, monsterCo1GeometryVectorRow441,
      monsterCo1GeometryVectorRow459, monsterCo1GeometryVectorRow461,
      monsterCo1GeometryVectorRow468, monsterCo1GeometryVectorRow481,
      monsterCo1GeometryVectorRow482, monsterCo1GeometryVectorRow490,
      monsterCo1GeometryVectorRow521, monsterCo1GeometryVectorRow542] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact monsterCo1GeometryVectorEquation0
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation7
    · exact monsterCo1GeometryVectorEquation12
    · exact monsterCo1GeometryVectorEquation18
    · exact monsterCo1GeometryVectorEquation23
    · exact monsterCo1GeometryVectorEquation27
    · exact monsterCo1GeometryVectorEquation38
    · exact monsterCo1GeometryVectorEquation44
    · exact monsterCo1GeometryVectorEquation52
    · exact monsterCo1GeometryVectorEquation57
    · exact monsterCo1GeometryVectorEquation59
    · exact monsterCo1GeometryVectorEquation64
    · exact monsterCo1GeometryVectorEquation71
    · exact monsterCo1GeometryVectorEquation75
    · exact monsterCo1GeometryVectorEquation86
    · exact monsterCo1GeometryVectorEquation90
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation112
    · exact monsterCo1GeometryVectorEquation117
    · exact monsterCo1GeometryVectorEquation129
    · exact monsterCo1GeometryVectorEquation131
    · exact monsterCo1GeometryVectorEquation141
    · exact monsterCo1GeometryVectorEquation155
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation266
    · exact monsterCo1GeometryVectorEquation290
    · exact monsterCo1GeometryVectorEquation297
    · exact monsterCo1GeometryVectorEquation321
    · exact monsterCo1GeometryVectorEquation345
    · exact monsterCo1GeometryVectorEquation347
    · exact monsterCo1GeometryVectorEquation356
    · exact monsterCo1GeometryVectorEquation391
    · exact monsterCo1GeometryVectorEquation426
    · exact monsterCo1GeometryVectorEquation440
    · exact monsterCo1GeometryVectorEquation441
    · exact monsterCo1GeometryVectorEquation459
    · exact monsterCo1GeometryVectorEquation461
    · exact monsterCo1GeometryVectorEquation468
    · exact monsterCo1GeometryVectorEquation481
    · exact monsterCo1GeometryVectorEquation482
    · exact monsterCo1GeometryVectorEquation490
    · exact monsterCo1GeometryVectorEquation521
    · exact monsterCo1GeometryVectorEquation542
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [469, 0, 2, 3, 4, 6, 7, 8,
      13, 15, 174, 175, 193] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow0,
      monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow7,
      monsterCo1GeometryVectorRow12, monsterCo1GeometryVectorRow18,
      monsterCo1GeometryVectorRow23, monsterCo1GeometryVectorRow27,
      monsterCo1GeometryVectorRow38, monsterCo1GeometryVectorRow44,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow57,
      monsterCo1GeometryVectorRow59, monsterCo1GeometryVectorRow64,
      monsterCo1GeometryVectorRow71, monsterCo1GeometryVectorRow75,
      monsterCo1GeometryVectorRow86, monsterCo1GeometryVectorRow90,
      monsterCo1GeometryVectorRow101, monsterCo1GeometryVectorRow112,
      monsterCo1GeometryVectorRow117, monsterCo1GeometryVectorRow129,
      monsterCo1GeometryVectorRow131, monsterCo1GeometryVectorRow141,
      monsterCo1GeometryVectorRow155, monsterCo1GeometryVectorRow265,
      monsterCo1GeometryVectorRow266, monsterCo1GeometryVectorRow290,
      monsterCo1GeometryVectorRow297, monsterCo1GeometryVectorRow321,
      monsterCo1GeometryVectorRow345, monsterCo1GeometryVectorRow347,
      monsterCo1GeometryVectorRow356, monsterCo1GeometryVectorRow391,
      monsterCo1GeometryVectorRow426, monsterCo1GeometryVectorRow440,
      monsterCo1GeometryVectorRow441, monsterCo1GeometryVectorRow459,
      monsterCo1GeometryVectorRow461, monsterCo1GeometryVectorRow468,
      monsterCo1GeometryVectorRow481, monsterCo1GeometryVectorRow482,
      monsterCo1GeometryVectorRow490, monsterCo1GeometryVectorRow521,
      monsterCo1GeometryVectorRow542] hp
    decide +kernel
  have images :
      ([469, 0, 25, 3, 9, 32, 13, 78, 7, 11, 399, 425, 409] : List (Fin 867)).map
      monsterCo1GeometryVectorValue =
      (([469, 0, 2, 3, 4, 6, 7, 8, 13, 15, 174, 175, 193] :
      List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 469) = monsterCo1GeometryVectorValue 469 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint469) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint469
      rw [monsterCo1GeometryVectorAction289]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 0 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint0
      rw [monsterCo1GeometryVectorAction189]
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
        (monsterCo1GeometryVectorValue 6) = monsterCo1GeometryVectorValue 32 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint6) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint32
      rw [monsterCo1GeometryVectorAction195]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 7) = monsterCo1GeometryVectorValue 13 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint7) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint13
      rw [monsterCo1GeometryVectorAction196]
    have h7 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 8) = monsterCo1GeometryVectorValue 78 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint8) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint78
      rw [monsterCo1GeometryVectorAction197]
    have h8 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 13) = monsterCo1GeometryVectorValue 7 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint13) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint7
      rw [monsterCo1GeometryVectorAction202]
    have h9 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 15) = monsterCo1GeometryVectorValue 11 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint15) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint11
      rw [monsterCo1GeometryVectorAction204]
    have h10 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 174) = monsterCo1GeometryVectorValue 399 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint174) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint399
      rw [monsterCo1GeometryVectorAction225]
    have h11 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 175) = monsterCo1GeometryVectorValue 425 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint175) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint425
      rw [monsterCo1GeometryVectorAction226]
    have h12 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 193) = monsterCo1GeometryVectorValue 409 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint193) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint409
      rw [monsterCo1GeometryVectorAction230]
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5))
      [469, 0, 2, 3, 4, 6, 7, 8, 13, 15, 174, 175, 193] [469, 0, 25, 3, 9, 32, 13, 78, 7, 11,
      399, 425, 409] images hs
  have hc :
      monsterCo1GeometryVectorRowNormalize [469, 0, 25, 3, 9, 32, 13, 78, 7, 11, 399, 425, 409]
      =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow543) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
