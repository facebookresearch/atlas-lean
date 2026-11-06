/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions31
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions38
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation032
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation034
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation048
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation050
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation082
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation149
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation159
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation203
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation226
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation234
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation236
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation292
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation306
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation353
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation355
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation361
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation376
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation380
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation382
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation474
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation484
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation486
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation491
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation550
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation569
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation578
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation585
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation590
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation607
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation667
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 701 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation701 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow701) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow4, monsterCo1GeometryVectorRow11,
      monsterCo1GeometryVectorRow15, monsterCo1GeometryVectorRow18,
      monsterCo1GeometryVectorRow21, monsterCo1GeometryVectorRow32,
      monsterCo1GeometryVectorRow34, monsterCo1GeometryVectorRow39,
      monsterCo1GeometryVectorRow48, monsterCo1GeometryVectorRow50,
      monsterCo1GeometryVectorRow52, monsterCo1GeometryVectorRow82,
      monsterCo1GeometryVectorRow97, monsterCo1GeometryVectorRow101,
      monsterCo1GeometryVectorRow149, monsterCo1GeometryVectorRow159,
      monsterCo1GeometryVectorRow203, monsterCo1GeometryVectorRow226,
      monsterCo1GeometryVectorRow234, monsterCo1GeometryVectorRow236,
      monsterCo1GeometryVectorRow265, monsterCo1GeometryVectorRow287,
      monsterCo1GeometryVectorRow292, monsterCo1GeometryVectorRow306,
      monsterCo1GeometryVectorRow353, monsterCo1GeometryVectorRow355,
      monsterCo1GeometryVectorRow361, monsterCo1GeometryVectorRow376,
      monsterCo1GeometryVectorRow380, monsterCo1GeometryVectorRow382,
      monsterCo1GeometryVectorRow474, monsterCo1GeometryVectorRow484,
      monsterCo1GeometryVectorRow486, monsterCo1GeometryVectorRow491,
      monsterCo1GeometryVectorRow550, monsterCo1GeometryVectorRow569,
      monsterCo1GeometryVectorRow578, monsterCo1GeometryVectorRow585,
      monsterCo1GeometryVectorRow590, monsterCo1GeometryVectorRow607,
      monsterCo1GeometryVectorRow667] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation4
    · exact monsterCo1GeometryVectorEquation11
    · exact monsterCo1GeometryVectorEquation15
    · exact monsterCo1GeometryVectorEquation18
    · exact monsterCo1GeometryVectorEquation21
    · exact monsterCo1GeometryVectorEquation32
    · exact monsterCo1GeometryVectorEquation34
    · exact monsterCo1GeometryVectorEquation39
    · exact monsterCo1GeometryVectorEquation48
    · exact monsterCo1GeometryVectorEquation50
    · exact monsterCo1GeometryVectorEquation52
    · exact monsterCo1GeometryVectorEquation82
    · exact monsterCo1GeometryVectorEquation97
    · exact monsterCo1GeometryVectorEquation101
    · exact monsterCo1GeometryVectorEquation149
    · exact monsterCo1GeometryVectorEquation159
    · exact monsterCo1GeometryVectorEquation203
    · exact monsterCo1GeometryVectorEquation226
    · exact monsterCo1GeometryVectorEquation234
    · exact monsterCo1GeometryVectorEquation236
    · exact monsterCo1GeometryVectorEquation265
    · exact monsterCo1GeometryVectorEquation287
    · exact monsterCo1GeometryVectorEquation292
    · exact monsterCo1GeometryVectorEquation306
    · exact monsterCo1GeometryVectorEquation353
    · exact monsterCo1GeometryVectorEquation355
    · exact monsterCo1GeometryVectorEquation361
    · exact monsterCo1GeometryVectorEquation376
    · exact monsterCo1GeometryVectorEquation380
    · exact monsterCo1GeometryVectorEquation382
    · exact monsterCo1GeometryVectorEquation474
    · exact monsterCo1GeometryVectorEquation484
    · exact monsterCo1GeometryVectorEquation486
    · exact monsterCo1GeometryVectorEquation491
    · exact monsterCo1GeometryVectorEquation550
    · exact monsterCo1GeometryVectorEquation569
    · exact monsterCo1GeometryVectorEquation578
    · exact monsterCo1GeometryVectorEquation585
    · exact monsterCo1GeometryVectorEquation590
    · exact monsterCo1GeometryVectorEquation607
    · exact monsterCo1GeometryVectorEquation667
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [669, 1, 2, 4, 6, 8, 13,
      14, 17] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow4,
      monsterCo1GeometryVectorRow11, monsterCo1GeometryVectorRow15,
      monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow21,
      monsterCo1GeometryVectorRow32, monsterCo1GeometryVectorRow34,
      monsterCo1GeometryVectorRow39, monsterCo1GeometryVectorRow48,
      monsterCo1GeometryVectorRow50, monsterCo1GeometryVectorRow52,
      monsterCo1GeometryVectorRow82, monsterCo1GeometryVectorRow97,
      monsterCo1GeometryVectorRow101, monsterCo1GeometryVectorRow149,
      monsterCo1GeometryVectorRow159, monsterCo1GeometryVectorRow203,
      monsterCo1GeometryVectorRow226, monsterCo1GeometryVectorRow234,
      monsterCo1GeometryVectorRow236, monsterCo1GeometryVectorRow265,
      monsterCo1GeometryVectorRow287, monsterCo1GeometryVectorRow292,
      monsterCo1GeometryVectorRow306, monsterCo1GeometryVectorRow353,
      monsterCo1GeometryVectorRow355, monsterCo1GeometryVectorRow361,
      monsterCo1GeometryVectorRow376, monsterCo1GeometryVectorRow380,
      monsterCo1GeometryVectorRow382, monsterCo1GeometryVectorRow474,
      monsterCo1GeometryVectorRow484, monsterCo1GeometryVectorRow486,
      monsterCo1GeometryVectorRow491, monsterCo1GeometryVectorRow550,
      monsterCo1GeometryVectorRow569, monsterCo1GeometryVectorRow578,
      monsterCo1GeometryVectorRow585, monsterCo1GeometryVectorRow590,
      monsterCo1GeometryVectorRow607, monsterCo1GeometryVectorRow667] hp
    decide +kernel
  have images :
      ([810, 3, 6, 11, 2, 104, 13, 212, 213] : List (Fin 867)).map
      monsterCo1GeometryVectorValue =
      (([669, 1, 2, 4, 6, 8, 13, 14, 17] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 669) = monsterCo1GeometryVectorValue 810 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint669) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint810
      rw [monsterCo1GeometryVectorAction927]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 1) = monsterCo1GeometryVectorValue 3 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint1) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint3
      rw [monsterCo1GeometryVectorAction746]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 2) = monsterCo1GeometryVectorValue 6 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint2) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint6
      rw [monsterCo1GeometryVectorAction747]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 4) = monsterCo1GeometryVectorValue 11 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint4) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint11
      rw [monsterCo1GeometryVectorAction749]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 6) = monsterCo1GeometryVectorValue 2 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint6) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint2
      rw [monsterCo1GeometryVectorAction751]
    have h5 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 8) = monsterCo1GeometryVectorValue 104 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint8) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint104
      rw [monsterCo1GeometryVectorAction753]
    have h6 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 13) = monsterCo1GeometryVectorValue 13 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint13) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint13
      rw [monsterCo1GeometryVectorAction758]
    have h7 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 14) = monsterCo1GeometryVectorValue 212 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint14) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint212
      rw [monsterCo1GeometryVectorAction759]
    have h8 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 17) = monsterCo1GeometryVectorValue 213 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint17) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint213
      rw [monsterCo1GeometryVectorAction762]
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14))
    [669, 1, 2, 4, 6, 8, 13, 14, 17] [810, 3, 6, 11, 2, 104, 13, 212, 213] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [810, 3, 6, 11, 2, 104, 13, 212, 213] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow701) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
