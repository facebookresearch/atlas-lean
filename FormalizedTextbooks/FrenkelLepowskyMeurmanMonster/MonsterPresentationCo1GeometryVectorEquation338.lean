/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorActions16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorEquation178
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 338 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation338 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow338) = 0 := by
  have hp : ∀ r ∈ ([monsterCo1GeometryVectorRow178] : List (List (Fin 867))),
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact monsterCo1GeometryVectorEquation178
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [246, 5, 207] = 0 := by
    apply monsterCo1GeometryVectorRowEval_zero_of_prior _ [monsterCo1GeometryVectorRow178] hp
    decide +kernel
  have images : ([454, 29, 453] : List (Fin 867)).map monsterCo1GeometryVectorValue =
      (([246, 5, 207] : List (Fin 867)).map monsterCo1GeometryVectorValue).map
        (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)) := by
    simp only [List.map_cons, List.map_nil]
    have h0 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 246) = monsterCo1GeometryVectorValue 454 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint246) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint454
      rw [monsterCo1GeometryVectorAction392]
    have h1 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 5) = monsterCo1GeometryVectorValue 29 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint5) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint29
      rw [monsterCo1GeometryVectorAction335]
    have h2 : monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6)
        (monsterCo1GeometryVectorValue 207) = monsterCo1GeometryVectorValue 453 := by
      rw [monsterCo1GeometryVectorValue, monsterCo1GeometryUniversalAction_point]
      change monsterCo1GeometryUniversalPoint
        (monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint207) =
        monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint453
      rw [monsterCo1GeometryVectorAction386]
    rw [h0, h1, h2]
  have ht := monsterCo1GeometryVectorRowEval_transport monsterCo1GeometryVectorValue
    (monsterCo1GeometryUniversalAction (monsterCo1GeometryTransportOperator 6))
    [246, 5, 207] [454, 29, 453] images hs
  have hc : monsterCo1GeometryVectorRowNormalize [454, 29, 453] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow338) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
