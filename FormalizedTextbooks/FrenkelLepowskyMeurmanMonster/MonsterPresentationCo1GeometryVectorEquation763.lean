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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions28
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation045
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation055
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation059
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation091
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation154
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation155
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation191
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation195
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation208
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation261
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation266
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation292
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation307
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation345
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation353
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation356
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation379
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation391
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation436
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation440
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation441
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation472
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation477
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation480
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation484
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation485
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation488
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation490
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation492
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation612
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation633
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation749
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 763 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation763 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow763) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow5, monsterCo1GeometryVectorRow6,
      monsterCo1GeometryVectorRow7, monsterCo1GeometryVectorRow12,
      monsterCo1GeometryVectorRow14, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow44,
      monsterCo1GeometryVectorRow45, monsterCo1GeometryVectorRow52,
      monsterCo1GeometryVectorRow55, monsterCo1GeometryVectorRow59,
      monsterCo1GeometryVectorRow90, monsterCo1GeometryVectorRow91,
      monsterCo1GeometryVectorRow101, monsterCo1GeometryVectorRow154,
      monsterCo1GeometryVectorRow155, monsterCo1GeometryVectorRow191,
      monsterCo1GeometryVectorRow195, monsterCo1GeometryVectorRow208,
      monsterCo1GeometryVectorRow261, monsterCo1GeometryVectorRow265,
      monsterCo1GeometryVectorRow266, monsterCo1GeometryVectorRow292,
      monsterCo1GeometryVectorRow307, monsterCo1GeometryVectorRow345,
      monsterCo1GeometryVectorRow353, monsterCo1GeometryVectorRow356,
      monsterCo1GeometryVectorRow379, monsterCo1GeometryVectorRow391,
      monsterCo1GeometryVectorRow436, monsterCo1GeometryVectorRow440,
      monsterCo1GeometryVectorRow441, monsterCo1GeometryVectorRow472,
      monsterCo1GeometryVectorRow477, monsterCo1GeometryVectorRow480,
      monsterCo1GeometryVectorRow484, monsterCo1GeometryVectorRow485,
      monsterCo1GeometryVectorRow488, monsterCo1GeometryVectorRow490,
      monsterCo1GeometryVectorRow492, monsterCo1GeometryVectorRow612,
      monsterCo1GeometryVectorRow633, monsterCo1GeometryVectorRow749] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact monsterCo1GeometryVectorEquation5
    · exact monsterCo1GeometryVectorEquation6
    · exact monsterCo1GeometryVectorEquation7
    · exact monsterCo1GeometryVectorEquation12
    · exact monsterCo1GeometryVectorEquation14
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation18
    · exact monsterCo1GeometryVectorEquation44
    · exact monsterCo1GeometryVectorEquation45
    · exact monsterCo1GeometryVectorEquation52
    · exact monsterCo1GeometryVectorEquation55
    · exact monsterCo1GeometryVectorEquation59
    · exact monsterCo1GeometryVectorEquation90
    · exact monsterCo1GeometryVectorEquation91
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation154
    · exact monsterCo1GeometryVectorEquation155
    · exact monsterCo1GeometryVectorEquation191
    · exact monsterCo1GeometryVectorEquation195
    · exact monsterCo1GeometryVectorEquation208
    · exact monsterCo1GeometryVectorEquation261
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation266
    · exact monsterCo1GeometryVectorEquation292
    · exact monsterCo1GeometryVectorEquation307
    · exact monsterCo1GeometryVectorEquation345
    · exact monsterCo1GeometryVectorEquation353
    · exact monsterCo1GeometryVectorEquation356
    · exact monsterCo1GeometryVectorEquation379
    · exact monsterCo1GeometryVectorEquation391
    · exact monsterCo1GeometryVectorEquation436
    · exact monsterCo1GeometryVectorEquation440
    · exact monsterCo1GeometryVectorEquation441
    · exact monsterCo1GeometryVectorEquation472
    · exact monsterCo1GeometryVectorEquation477
    · exact monsterCo1GeometryVectorEquation480
    · exact monsterCo1GeometryVectorEquation484
    · exact monsterCo1GeometryVectorEquation485
    · exact monsterCo1GeometryVectorEquation488
    · exact monsterCo1GeometryVectorEquation490
    · exact monsterCo1GeometryVectorEquation492
    · exact monsterCo1GeometryVectorEquation612
    · exact monsterCo1GeometryVectorEquation633
    · exact monsterCo1GeometryVectorEquation749
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [522, 8, 9, 10, 17, 19] = 0
      := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow5,
      monsterCo1GeometryVectorRow6, monsterCo1GeometryVectorRow7,
      monsterCo1GeometryVectorRow12, monsterCo1GeometryVectorRow14,
      monsterCo1GeometryVectorRow15, monsterCo1GeometryVectorRow18,
      monsterCo1GeometryVectorRow44, monsterCo1GeometryVectorRow45,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow55,
      monsterCo1GeometryVectorRow59, monsterCo1GeometryVectorRow90,
      monsterCo1GeometryVectorRow91, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow154, monsterCo1GeometryVectorRow155,
      monsterCo1GeometryVectorRow191, monsterCo1GeometryVectorRow195,
      monsterCo1GeometryVectorRow208, monsterCo1GeometryVectorRow261,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow266,
      monsterCo1GeometryVectorRow292, monsterCo1GeometryVectorRow307,
      monsterCo1GeometryVectorRow345, monsterCo1GeometryVectorRow353,
      monsterCo1GeometryVectorRow356, monsterCo1GeometryVectorRow379,
      monsterCo1GeometryVectorRow391, monsterCo1GeometryVectorRow436,
      monsterCo1GeometryVectorRow440, monsterCo1GeometryVectorRow441,
      monsterCo1GeometryVectorRow472, monsterCo1GeometryVectorRow477,
      monsterCo1GeometryVectorRow480, monsterCo1GeometryVectorRow484,
      monsterCo1GeometryVectorRow485, monsterCo1GeometryVectorRow488,
      monsterCo1GeometryVectorRow490, monsterCo1GeometryVectorRow492,
      monsterCo1GeometryVectorRow612, monsterCo1GeometryVectorRow633,
      monsterCo1GeometryVectorRow749] hp
    decide +kernel
  have images : ([722, 72, 121, 114, 21, 205] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([522, 8, 9, 10, 17, 19] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 522) = monsterCo1GeometryVectorValue 722 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint522) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint722
      rw [monsterCo1GeometryVectorAction684]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 8) = monsterCo1GeometryVectorValue 72 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint8) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint72
      rw [monsterCo1GeometryVectorAction475]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 9) = monsterCo1GeometryVectorValue 121 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint9) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint121
      rw [monsterCo1GeometryVectorAction476]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 10) = monsterCo1GeometryVectorValue 114 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint10) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint114
      rw [monsterCo1GeometryVectorAction477]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 17) = monsterCo1GeometryVectorValue 21 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint17) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint21
      rw [monsterCo1GeometryVectorAction484]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 19) = monsterCo1GeometryVectorValue 205 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint19) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint205
      rw [monsterCo1GeometryVectorAction486]
    rw [h0, h1, h2, h3, h4, h5]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13))
    [522, 8, 9, 10, 17, 19] [722, 72, 121, 114, 21, 205] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [722, 72, 121, 114, 21, 205] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow763) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
