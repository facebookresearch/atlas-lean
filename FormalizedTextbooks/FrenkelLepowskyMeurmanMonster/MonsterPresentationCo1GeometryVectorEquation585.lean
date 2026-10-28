/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation038
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation055
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation057
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation064
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation071
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation086
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation112
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation117
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation129
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation131
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation141
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation291
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation292
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation343
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation352
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation376
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation402
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation471
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation474
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation487
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation489
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation529
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation534
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation541
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation574
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation579
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 585 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation585 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow585) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow0, monsterCo1GeometryVectorRow1,
      monsterCo1GeometryVectorRow5, monsterCo1GeometryVectorRow8,
      monsterCo1GeometryVectorRow11, monsterCo1GeometryVectorRow14,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow23, monsterCo1GeometryVectorRow38,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow55,
      monsterCo1GeometryVectorRow57, monsterCo1GeometryVectorRow64,
      monsterCo1GeometryVectorRow71, monsterCo1GeometryVectorRow86,
      monsterCo1GeometryVectorRow101, monsterCo1GeometryVectorRow112,
      monsterCo1GeometryVectorRow117, monsterCo1GeometryVectorRow129,
      monsterCo1GeometryVectorRow131, monsterCo1GeometryVectorRow141,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow265,
      monsterCo1GeometryVectorRow287, monsterCo1GeometryVectorRow291,
      monsterCo1GeometryVectorRow292, monsterCo1GeometryVectorRow343,
      monsterCo1GeometryVectorRow352, monsterCo1GeometryVectorRow376,
      monsterCo1GeometryVectorRow402, monsterCo1GeometryVectorRow471,
      monsterCo1GeometryVectorRow474, monsterCo1GeometryVectorRow487,
      monsterCo1GeometryVectorRow489, monsterCo1GeometryVectorRow529,
      monsterCo1GeometryVectorRow534, monsterCo1GeometryVectorRow541,
      monsterCo1GeometryVectorRow574, monsterCo1GeometryVectorRow579] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation0
    · exact monsterCo1GeometryVectorEquation1
    · exact monsterCo1GeometryVectorEquation5
    · exact monsterCo1GeometryVectorEquation8
    · exact monsterCo1GeometryVectorEquation11
    · exact monsterCo1GeometryVectorEquation14
    · exact monsterCo1GeometryVectorEquation18
    · exact monsterCo1GeometryVectorEquation20
    · exact monsterCo1GeometryVectorEquation23
    · exact monsterCo1GeometryVectorEquation38
    · exact monsterCo1GeometryVectorEquation52
    · exact monsterCo1GeometryVectorEquation55
    · exact monsterCo1GeometryVectorEquation57
    · exact monsterCo1GeometryVectorEquation64
    · exact monsterCo1GeometryVectorEquation71
    · exact monsterCo1GeometryVectorEquation86
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation112
    · exact monsterCo1GeometryVectorEquation117
    · exact monsterCo1GeometryVectorEquation129
    · exact monsterCo1GeometryVectorEquation131
    · exact monsterCo1GeometryVectorEquation141
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation287
    · exact monsterCo1GeometryVectorEquation291
    · exact monsterCo1GeometryVectorEquation292
    · exact monsterCo1GeometryVectorEquation343
    · exact monsterCo1GeometryVectorEquation352
    · exact monsterCo1GeometryVectorEquation376
    · exact monsterCo1GeometryVectorEquation402
    · exact monsterCo1GeometryVectorEquation471
    · exact monsterCo1GeometryVectorEquation474
    · exact monsterCo1GeometryVectorEquation487
    · exact monsterCo1GeometryVectorEquation489
    · exact monsterCo1GeometryVectorEquation529
    · exact monsterCo1GeometryVectorEquation534
    · exact monsterCo1GeometryVectorEquation541
    · exact monsterCo1GeometryVectorEquation574
    · exact monsterCo1GeometryVectorEquation579
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [518, 0, 3, 4, 8, 9, 12,
      13, 14, 193] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow0,
      monsterCo1GeometryVectorRow1, monsterCo1GeometryVectorRow5, monsterCo1GeometryVectorRow8,
      monsterCo1GeometryVectorRow11, monsterCo1GeometryVectorRow14,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow23, monsterCo1GeometryVectorRow38,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow55,
      monsterCo1GeometryVectorRow57, monsterCo1GeometryVectorRow64,
      monsterCo1GeometryVectorRow71, monsterCo1GeometryVectorRow86,
      monsterCo1GeometryVectorRow101, monsterCo1GeometryVectorRow112,
      monsterCo1GeometryVectorRow117, monsterCo1GeometryVectorRow129,
      monsterCo1GeometryVectorRow131, monsterCo1GeometryVectorRow141,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow265,
      monsterCo1GeometryVectorRow287, monsterCo1GeometryVectorRow291,
      monsterCo1GeometryVectorRow292, monsterCo1GeometryVectorRow343,
      monsterCo1GeometryVectorRow352, monsterCo1GeometryVectorRow376,
      monsterCo1GeometryVectorRow402, monsterCo1GeometryVectorRow471,
      monsterCo1GeometryVectorRow474, monsterCo1GeometryVectorRow487,
      monsterCo1GeometryVectorRow489, monsterCo1GeometryVectorRow529,
      monsterCo1GeometryVectorRow534, monsterCo1GeometryVectorRow541,
      monsterCo1GeometryVectorRow574, monsterCo1GeometryVectorRow579] hp
    decide +kernel
  have images :
      ([601, 1, 7, 8, 2, 78, 17, 44, 173, 270] : List (Fin 867)).map
      monsterCo1GeometryVectorValue =
      (([518, 0, 3, 4, 8, 9, 12, 13, 14, 193] :
      List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 518) = monsterCo1GeometryVectorValue 601 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint518) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint601
      rw [monsterCo1GeometryVectorAction141]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 1 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint1
      rw [monsterCo1GeometryVectorAction0]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 3) = monsterCo1GeometryVectorValue 7 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint3) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint7
      rw [monsterCo1GeometryVectorAction3]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 4) = monsterCo1GeometryVectorValue 8 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint4) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint8
      rw [monsterCo1GeometryVectorAction4]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 8) = monsterCo1GeometryVectorValue 2 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint8) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint2
      rw [monsterCo1GeometryVectorAction8]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 9) = monsterCo1GeometryVectorValue 78 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint9) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint78
      rw [monsterCo1GeometryVectorAction9]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 12) = monsterCo1GeometryVectorValue 17 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint12) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint17
      rw [monsterCo1GeometryVectorAction12]
    have h7 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 13) = monsterCo1GeometryVectorValue 44 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint13) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint44
      rw [monsterCo1GeometryVectorAction13]
    have h8 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 14) = monsterCo1GeometryVectorValue 173 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint14) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint173
      rw [monsterCo1GeometryVectorAction14]
    have h9 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 193) = monsterCo1GeometryVectorValue 270 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint193) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint270
      rw [monsterCo1GeometryVectorAction60]
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0))
    [518, 0, 3, 4, 8, 9, 12, 13, 14, 193] [601, 1, 7, 8, 2, 78, 17, 44, 173, 270] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [601, 1, 7, 8, 2, 78, 17, 44, 173, 270] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow585) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
