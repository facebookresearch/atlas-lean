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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation050
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation309
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation353
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation361
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation382
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation484
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 490 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation490 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow490) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow0, monsterCo1GeometryVectorRow39,
      monsterCo1GeometryVectorRow50, monsterCo1GeometryVectorRow52,
      monsterCo1GeometryVectorRow97, monsterCo1GeometryVectorRow309,
      monsterCo1GeometryVectorRow353, monsterCo1GeometryVectorRow361,
      monsterCo1GeometryVectorRow382, monsterCo1GeometryVectorRow484] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation0
    · exact monsterCo1GeometryVectorEquation39
    · exact monsterCo1GeometryVectorEquation50
    · exact monsterCo1GeometryVectorEquation52
    · exact monsterCo1GeometryVectorEquation97
    · exact monsterCo1GeometryVectorEquation309
    · exact monsterCo1GeometryVectorEquation353
    · exact monsterCo1GeometryVectorEquation361
    · exact monsterCo1GeometryVectorEquation382
    · exact monsterCo1GeometryVectorEquation484
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [389, 0, 1, 8, 9, 10, 17,
      201] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow0,
      monsterCo1GeometryVectorRow39, monsterCo1GeometryVectorRow50,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow97,
      monsterCo1GeometryVectorRow309, monsterCo1GeometryVectorRow353,
      monsterCo1GeometryVectorRow361, monsterCo1GeometryVectorRow382,
      monsterCo1GeometryVectorRow484] hp
    decide +kernel
  have images :
      ([476, 0, 1, 78, 4, 106, 181, 225] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([389, 0, 1, 8, 9, 10, 17, 201] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 389) = monsterCo1GeometryVectorValue 476 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint389) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint476
      rw [monsterCo1GeometryVectorAction267]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 0 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint0
      rw [monsterCo1GeometryVectorAction189]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 1) = monsterCo1GeometryVectorValue 1 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint1) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint1
      rw [monsterCo1GeometryVectorAction190]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 8) = monsterCo1GeometryVectorValue 78 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint8) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint78
      rw [monsterCo1GeometryVectorAction197]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 9) = monsterCo1GeometryVectorValue 4 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint9) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint4
      rw [monsterCo1GeometryVectorAction198]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 10) = monsterCo1GeometryVectorValue 106 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint10) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint106
      rw [monsterCo1GeometryVectorAction199]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 17) = monsterCo1GeometryVectorValue 181 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint17) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint181
      rw [monsterCo1GeometryVectorAction206]
    have h7 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5)
        (monsterCo1GeometryVectorValue 201) = monsterCo1GeometryVectorValue 225 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint201) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint225
      rw [monsterCo1GeometryVectorAction233]
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 5))
    [389, 0, 1, 8, 9, 10, 17, 201] [476, 0, 1, 78, 4, 106, 181, 225] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [476, 0, 1, 78, 4, 106, 181, 225] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow490) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
