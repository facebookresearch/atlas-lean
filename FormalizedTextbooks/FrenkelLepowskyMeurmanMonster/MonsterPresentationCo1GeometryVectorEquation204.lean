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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation026
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation074
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 204 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation204 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow204) = 0 := by
  have hp :
      ∀ r ∈ ([monsterCo1GeometryVectorRow18, monsterCo1GeometryVectorRow26,
      monsterCo1GeometryVectorRow74] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact monsterCo1GeometryVectorEquation18
    · exact monsterCo1GeometryVectorEquation26
    · exact monsterCo1GeometryVectorEquation74
  have hs :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [98, 0, 5, 12, 17] = 0 :=
      by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow18,
      monsterCo1GeometryVectorRow26, monsterCo1GeometryVectorRow74] hp
    decide +kernel
  have images : ([271, 0, 83, 201, 21] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([98, 0, 5, 12, 17] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 98) = monsterCo1GeometryVectorValue 271 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint98) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint271
      rw [monsterCo1GeometryVectorAction511]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 0) = monsterCo1GeometryVectorValue 0 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint0) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint0
      rw [monsterCo1GeometryVectorAction467]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 5) = monsterCo1GeometryVectorValue 83 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint5) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint83
      rw [monsterCo1GeometryVectorAction472]
    have h3 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 12) = monsterCo1GeometryVectorValue 201 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint12) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint201
      rw [monsterCo1GeometryVectorAction479]
    have h4 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13)
        (monsterCo1GeometryVectorValue 17) = monsterCo1GeometryVectorValue 21 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint17) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint21
      rw [monsterCo1GeometryVectorAction484]
    rw [h0, h1, h2, h3, h4]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 13))
    [98, 0, 5, 12, 17] [271, 0, 83, 201, 21] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [271, 0, 83, 201, 21] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow204) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
