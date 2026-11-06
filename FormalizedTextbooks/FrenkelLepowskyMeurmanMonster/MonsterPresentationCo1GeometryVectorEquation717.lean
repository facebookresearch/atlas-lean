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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation027
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation075
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation159
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation226
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation236
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation485
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation486
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation489
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation529
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation556
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation574
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation579
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation585
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation632
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation644
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 717 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation717 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow717) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow0, monsterCo1GeometryVectorRow5,
      monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow8,
      monsterCo1GeometryVectorRow10, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow21, monsterCo1GeometryVectorRow27,
      monsterCo1GeometryVectorRow75, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow159,
      monsterCo1GeometryVectorRow226, monsterCo1GeometryVectorRow236,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow287,
      monsterCo1GeometryVectorRow485, monsterCo1GeometryVectorRow486,
      monsterCo1GeometryVectorRow489, monsterCo1GeometryVectorRow529,
      monsterCo1GeometryVectorRow556, monsterCo1GeometryVectorRow574,
      monsterCo1GeometryVectorRow579, monsterCo1GeometryVectorRow585,
      monsterCo1GeometryVectorRow632, monsterCo1GeometryVectorRow644] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    · exact monsterCo1GeometryVectorEquation0
    · exact monsterCo1GeometryVectorEquation5
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation8
    · exact monsterCo1GeometryVectorEquation10
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation18
    · exact monsterCo1GeometryVectorEquation20
    · exact monsterCo1GeometryVectorEquation21
    · exact monsterCo1GeometryVectorEquation27
    · exact monsterCo1GeometryVectorEquation75
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation159
    · exact monsterCo1GeometryVectorEquation226
    · exact monsterCo1GeometryVectorEquation236
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation287
    · exact monsterCo1GeometryVectorEquation485
    · exact monsterCo1GeometryVectorEquation486
    · exact monsterCo1GeometryVectorEquation489
    · exact monsterCo1GeometryVectorEquation529
    · exact monsterCo1GeometryVectorEquation556
    · exact monsterCo1GeometryVectorEquation574
    · exact monsterCo1GeometryVectorEquation579
    · exact monsterCo1GeometryVectorEquation585
    · exact monsterCo1GeometryVectorEquation632
    · exact monsterCo1GeometryVectorEquation644
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [700, 0, 4, 7, 17, 199] = 0
      := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow0,
      monsterCo1GeometryVectorRow5, monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow8,
      monsterCo1GeometryVectorRow10, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow20,
      monsterCo1GeometryVectorRow21, monsterCo1GeometryVectorRow27,
      monsterCo1GeometryVectorRow75, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow159,
      monsterCo1GeometryVectorRow226, monsterCo1GeometryVectorRow236,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow287,
      monsterCo1GeometryVectorRow485, monsterCo1GeometryVectorRow486,
      monsterCo1GeometryVectorRow489, monsterCo1GeometryVectorRow529,
      monsterCo1GeometryVectorRow556, monsterCo1GeometryVectorRow574,
      monsterCo1GeometryVectorRow579, monsterCo1GeometryVectorRow585,
      monsterCo1GeometryVectorRow632, monsterCo1GeometryVectorRow644] hp
    decide +kernel
  have images : ([827, 1, 8, 34, 99, 776] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([700, 0, 4, 7, 17, 199] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 700) = monsterCo1GeometryVectorValue 827 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint700) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint827
      rw [monsterCo1GeometryVectorAction173]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 1 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint1
      rw [monsterCo1GeometryVectorAction0]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 4) = monsterCo1GeometryVectorValue 8 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint4) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint8
      rw [monsterCo1GeometryVectorAction4]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 7) = monsterCo1GeometryVectorValue 34 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint7) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint34
      rw [monsterCo1GeometryVectorAction7]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 17) = monsterCo1GeometryVectorValue 99 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint17) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint99
      rw [monsterCo1GeometryVectorAction17]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 199) = monsterCo1GeometryVectorValue 776 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint199) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint776
      rw [monsterCo1GeometryVectorAction63]
    rw [h0, h1, h2, h3, h4, h5]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0))
    [700, 0, 4, 7, 17, 199] [827, 1, 8, 34, 99, 776] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [827, 1, 8, 34, 99, 776] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow717) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
