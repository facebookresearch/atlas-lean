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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation045
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation048
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation050
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation054
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation055
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation059
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation091
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation154
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation191
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation195
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation208
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation266
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation354
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation436
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation441
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation480
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation485
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation488
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation492
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 548 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation548 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow548) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow0, monsterCo1GeometryVectorRow1,
      monsterCo1GeometryVectorRow7, monsterCo1GeometryVectorRow8,
      monsterCo1GeometryVectorRow14, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow39,
      monsterCo1GeometryVectorRow44, monsterCo1GeometryVectorRow45,
      monsterCo1GeometryVectorRow48, monsterCo1GeometryVectorRow50,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow54,
      monsterCo1GeometryVectorRow55, monsterCo1GeometryVectorRow59,
      monsterCo1GeometryVectorRow90, monsterCo1GeometryVectorRow91,
      monsterCo1GeometryVectorRow97, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow154, monsterCo1GeometryVectorRow191,
      monsterCo1GeometryVectorRow195, monsterCo1GeometryVectorRow208,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow266,
      monsterCo1GeometryVectorRow354, monsterCo1GeometryVectorRow436,
      monsterCo1GeometryVectorRow441, monsterCo1GeometryVectorRow480,
      monsterCo1GeometryVectorRow485, monsterCo1GeometryVectorRow488,
      monsterCo1GeometryVectorRow492] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation0
    · exact monsterCo1GeometryVectorEquation1
    · exact monsterCo1GeometryVectorEquation7
    · exact monsterCo1GeometryVectorEquation8
    · exact monsterCo1GeometryVectorEquation14
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation18
    · exact monsterCo1GeometryVectorEquation39
    · exact monsterCo1GeometryVectorEquation44
    · exact monsterCo1GeometryVectorEquation45
    · exact monsterCo1GeometryVectorEquation48
    · exact monsterCo1GeometryVectorEquation50
    · exact monsterCo1GeometryVectorEquation52
    · exact monsterCo1GeometryVectorEquation54
    · exact monsterCo1GeometryVectorEquation55
    · exact monsterCo1GeometryVectorEquation59
    · exact monsterCo1GeometryVectorEquation90
    · exact monsterCo1GeometryVectorEquation91
    · exact monsterCo1GeometryVectorEquation97
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation154
    · exact monsterCo1GeometryVectorEquation191
    · exact monsterCo1GeometryVectorEquation195
    · exact monsterCo1GeometryVectorEquation208
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation266
    · exact monsterCo1GeometryVectorEquation354
    · exact monsterCo1GeometryVectorEquation436
    · exact monsterCo1GeometryVectorEquation441
    · exact monsterCo1GeometryVectorEquation480
    · exact monsterCo1GeometryVectorEquation485
    · exact monsterCo1GeometryVectorEquation488
    · exact monsterCo1GeometryVectorEquation492
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [474, 2, 5, 6, 8, 9, 12,
      14, 190] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow0,
      monsterCo1GeometryVectorRow1, monsterCo1GeometryVectorRow7, monsterCo1GeometryVectorRow8,
      monsterCo1GeometryVectorRow14, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow39,
      monsterCo1GeometryVectorRow44, monsterCo1GeometryVectorRow45,
      monsterCo1GeometryVectorRow48, monsterCo1GeometryVectorRow50,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow54,
      monsterCo1GeometryVectorRow55, monsterCo1GeometryVectorRow59,
      monsterCo1GeometryVectorRow90, monsterCo1GeometryVectorRow91,
      monsterCo1GeometryVectorRow97, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow154, monsterCo1GeometryVectorRow191,
      monsterCo1GeometryVectorRow195, monsterCo1GeometryVectorRow208,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow266,
      monsterCo1GeometryVectorRow354, monsterCo1GeometryVectorRow436,
      monsterCo1GeometryVectorRow441, monsterCo1GeometryVectorRow480,
      monsterCo1GeometryVectorRow485, monsterCo1GeometryVectorRow488,
      monsterCo1GeometryVectorRow492] hp
    decide +kernel
  have images :
      ([482, 4, 29, 171, 2, 78, 17, 173, 380] : List (Fin 867)).map
      monsterCo1GeometryVectorValue =
      (([474, 2, 5, 6, 8, 9, 12, 14, 190] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 474) = monsterCo1GeometryVectorValue 482 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint474) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint482
      rw [monsterCo1GeometryVectorAction135]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 2) = monsterCo1GeometryVectorValue 4 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint2) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint4
      rw [monsterCo1GeometryVectorAction2]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 5) = monsterCo1GeometryVectorValue 29 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint5) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint29
      rw [monsterCo1GeometryVectorAction5]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 6) = monsterCo1GeometryVectorValue 171 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint6) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint171
      rw [monsterCo1GeometryVectorAction6]
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
        (monsterCo1GeometryVectorValue 14) = monsterCo1GeometryVectorValue 173 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint14) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint173
      rw [monsterCo1GeometryVectorAction14]
    have h8 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0)
        (monsterCo1GeometryVectorValue 190) = monsterCo1GeometryVectorValue 380 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint190) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint380
      rw [monsterCo1GeometryVectorAction58]
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 0))
    [474, 2, 5, 6, 8, 9, 12, 14, 190] [482, 4, 29, 171, 2, 78, 17, 173, 380] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [482, 4, 29, 171, 2, 78, 17, 173, 380] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow548) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
