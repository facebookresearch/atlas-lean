/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions31
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions32
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation025
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 165 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation165 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow165) = 0 := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow25] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact monsterCo1GeometryVectorEquation25
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [49, 1, 17] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow25] hp
    decide +kernel
  have images : ([234, 3, 213] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([49, 1, 17] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 49) = monsterCo1GeometryVectorValue 234 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint49) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint234
      rw [monsterCo1GeometryVectorAction773]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 1) = monsterCo1GeometryVectorValue 3 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint1) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint3
      rw [monsterCo1GeometryVectorAction746]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14)
        (monsterCo1GeometryVectorValue 17) = monsterCo1GeometryVectorValue 213 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint17) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint213
      rw [monsterCo1GeometryVectorAction762]
    rw [h0, h1, h2]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 14))
    [49, 1, 17] [234, 3, 213] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [234, 3, 213] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow165) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
