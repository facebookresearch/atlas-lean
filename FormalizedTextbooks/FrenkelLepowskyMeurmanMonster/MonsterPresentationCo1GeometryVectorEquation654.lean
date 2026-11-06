/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation027
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation050
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation059
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation075
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation203
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation292
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation489
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation529
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation574
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation579
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation632
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation636
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 654 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation654 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow654) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow5, monsterCo1GeometryVectorRow7,
      monsterCo1GeometryVectorRow10, monsterCo1GeometryVectorRow14,
      monsterCo1GeometryVectorRow27, monsterCo1GeometryVectorRow39,
      monsterCo1GeometryVectorRow44, monsterCo1GeometryVectorRow50,
      monsterCo1GeometryVectorRow59, monsterCo1GeometryVectorRow75,
      monsterCo1GeometryVectorRow90, monsterCo1GeometryVectorRow97,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow203,
      monsterCo1GeometryVectorRow287, monsterCo1GeometryVectorRow292,
      monsterCo1GeometryVectorRow489, monsterCo1GeometryVectorRow529,
      monsterCo1GeometryVectorRow574, monsterCo1GeometryVectorRow579,
      monsterCo1GeometryVectorRow632, monsterCo1GeometryVectorRow636] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation5
    · exact monsterCo1GeometryVectorEquation7
    · exact monsterCo1GeometryVectorEquation10
    · exact monsterCo1GeometryVectorEquation14
    · exact monsterCo1GeometryVectorEquation27
    · exact monsterCo1GeometryVectorEquation39
    · exact monsterCo1GeometryVectorEquation44
    · exact monsterCo1GeometryVectorEquation50
    · exact monsterCo1GeometryVectorEquation59
    · exact monsterCo1GeometryVectorEquation75
    · exact monsterCo1GeometryVectorEquation90
    · exact monsterCo1GeometryVectorEquation97
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation203
    · exact monsterCo1GeometryVectorEquation287
    · exact monsterCo1GeometryVectorEquation292
    · exact monsterCo1GeometryVectorEquation489
    · exact monsterCo1GeometryVectorEquation529
    · exact monsterCo1GeometryVectorEquation574
    · exact monsterCo1GeometryVectorEquation579
    · exact monsterCo1GeometryVectorEquation632
    · exact monsterCo1GeometryVectorEquation636
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [448, 1, 2, 3, 4, 5, 10,
      12, 207] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow5,
      monsterCo1GeometryVectorRow7, monsterCo1GeometryVectorRow10,
      monsterCo1GeometryVectorRow14, monsterCo1GeometryVectorRow27,
      monsterCo1GeometryVectorRow39, monsterCo1GeometryVectorRow44,
      monsterCo1GeometryVectorRow50, monsterCo1GeometryVectorRow59,
      monsterCo1GeometryVectorRow75, monsterCo1GeometryVectorRow90,
      monsterCo1GeometryVectorRow97, monsterCo1GeometryVectorRow149,
      monsterCo1GeometryVectorRow203, monsterCo1GeometryVectorRow287,
      monsterCo1GeometryVectorRow292, monsterCo1GeometryVectorRow489,
      monsterCo1GeometryVectorRow529, monsterCo1GeometryVectorRow574,
      monsterCo1GeometryVectorRow579, monsterCo1GeometryVectorRow632,
      monsterCo1GeometryVectorRow636] hp
    decide +kernel
  have images :
      ([670, 2, 5, 200, 76, 83, 114, 201, 455] : List (Fin 867)).map
      monsterCo1GeometryVectorValue =
      (([448, 1, 2, 3, 4, 5, 10, 12, 207] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 448) = monsterCo1GeometryVectorValue 670 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint448) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint670
      rw [monsterCo1GeometryVectorAction668]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 1) = monsterCo1GeometryVectorValue 2 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint1) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint2
      rw [monsterCo1GeometryVectorAction468]
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
        (monsterCo1GeometryVectorValue 4) = monsterCo1GeometryVectorValue 76 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint4) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint76
      rw [monsterCo1GeometryVectorAction471]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 5) = monsterCo1GeometryVectorValue 83 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint5) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint83
      rw [monsterCo1GeometryVectorAction472]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 10) = monsterCo1GeometryVectorValue 114 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint10) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint114
      rw [monsterCo1GeometryVectorAction477]
    have h7 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 12) = monsterCo1GeometryVectorValue 201 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint12) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint201
      rw [monsterCo1GeometryVectorAction479]
    have h8 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 207) = monsterCo1GeometryVectorValue 455 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint207) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint455
      rw [monsterCo1GeometryVectorAction566]
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13))
    [448, 1, 2, 3, 4, 5, 10, 12, 207] [670, 2, 5, 200, 76, 83, 114, 201, 455] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [670, 2, 5, 200, 76, 83, 114, 201, 455] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow654) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
