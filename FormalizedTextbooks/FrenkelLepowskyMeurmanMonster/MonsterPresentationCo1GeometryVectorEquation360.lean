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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation159
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation194
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation226
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation236
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 360 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation360 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow360) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow1, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow20, monsterCo1GeometryVectorRow21,
      monsterCo1GeometryVectorRow101, monsterCo1GeometryVectorRow149,
      monsterCo1GeometryVectorRow159, monsterCo1GeometryVectorRow194,
      monsterCo1GeometryVectorRow226, monsterCo1GeometryVectorRow236,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow287] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation1
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation20
    · exact monsterCo1GeometryVectorEquation21
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation159
    · exact monsterCo1GeometryVectorEquation194
    · exact monsterCo1GeometryVectorEquation226
    · exact monsterCo1GeometryVectorEquation236
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation287
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [262, 3, 6, 7, 18, 172] = 0
      := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow1,
      monsterCo1GeometryVectorRow15, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow21, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow159,
      monsterCo1GeometryVectorRow194, monsterCo1GeometryVectorRow226,
      monsterCo1GeometryVectorRow236, monsterCo1GeometryVectorRow265,
      monsterCo1GeometryVectorRow287] hp
    decide +kernel
  have images : ([480, 200, 12, 14, 204, 365] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([262, 3, 6, 7, 18, 172] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 262) = monsterCo1GeometryVectorValue 480 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint262) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint480
      rw [monsterCo1GeometryVectorAction603]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 3) = monsterCo1GeometryVectorValue 200 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint3) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint200
      rw [monsterCo1GeometryVectorAction470]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 6) = monsterCo1GeometryVectorValue 12 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint6) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint12
      rw [monsterCo1GeometryVectorAction473]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 7) = monsterCo1GeometryVectorValue 14 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint7) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint14
      rw [monsterCo1GeometryVectorAction474]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 18) = monsterCo1GeometryVectorValue 204 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint18) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint204
      rw [monsterCo1GeometryVectorAction485]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 172) = monsterCo1GeometryVectorValue 365 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint172) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint365
      rw [monsterCo1GeometryVectorAction546]
    rw [h0, h1, h2, h3, h4, h5]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13))
    [262, 3, 6, 7, 18, 172] [480, 200, 12, 14, 204, 365] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [480, 200, 12, 14, 204, 365] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow360) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
