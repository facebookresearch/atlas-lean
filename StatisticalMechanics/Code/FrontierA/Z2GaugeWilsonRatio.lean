/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.Z2GaugeElitzur

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]


noncomputable def gaugeClosedSurfaceSum (incidence : P -> Finset E)
    (K : P -> ℝ) : ℝ := by
  classical
  exact ∑ A ∈ (Finset.univ : Finset P).powerset.filter
    (IsClosedPlaquetteSet incidence), ∏ p ∈ A, Real.tanh (K p)


noncomputable def gaugeWilsonSurfaceSum (incidence : P -> Finset E)
    (K : P -> ℝ) (L : Finset E) : ℝ := by
  classical
  exact ∑ A ∈ (Finset.univ : Finset P).powerset.filter
    (fun A => HasWilsonBoundary incidence A L), ∏ p ∈ A, Real.tanh (K p)

omit [DecidableEq E] [DecidableEq P] in

theorem gaugeHighTempPrefactor_pos (K : P -> ℝ) :
    0 < (2 : ℝ) ^ Fintype.card E * ∏ p : P, Real.cosh (K p) := by
  exact mul_pos (pow_pos (by norm_num) _)
    (Finset.prod_pos fun p _ => Real.cosh_pos (K p))

set_option linter.unusedFintypeInType false in
omit [DecidableEq P] in


theorem gaugeClosedSurfaceSum_pos (incidence : P -> Finset E) (K : P -> ℝ) :
    0 < gaugeClosedSurfaceSum incidence K := by
  classical
  have hpartition := gaugePartition_pos incidence K
  rw [gaugePartition_highTemp] at hpartition
  have hproduct : 0 <
      ((2 : ℝ) ^ Fintype.card E * ∏ p : P, Real.cosh (K p)) *
        gaugeClosedSurfaceSum incidence K := by
    simpa only [gaugeClosedSurfaceSum] using hpartition
  rcases mul_pos_iff.mp hproduct with hpos | hneg
  · exact hpos.2
  · exact False.elim (not_lt_of_ge (gaugeHighTempPrefactor_pos (E := E) K).le hneg.1)

omit [DecidableEq P] in


theorem gaugeWilsonExpectation_eq_surfaceRatio
    (incidence : P -> Finset E) (K : P -> ℝ) (L : Finset E) :
    gaugeWilsonExpectation incidence K L =
      gaugeWilsonSurfaceSum incidence K L /
        gaugeClosedSurfaceSum incidence K := by
  classical
  unfold gaugeWilsonExpectation
  rw [gaugeWilsonNumerator_highTemp, gaugePartition_highTemp]
  simp only [gaugeWilsonSurfaceSum, gaugeClosedSurfaceSum]
  exact mul_div_mul_left _ _ (gaugeHighTempPrefactor_pos (E := E) K).ne'

end StatMech.FrontierA
