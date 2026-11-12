/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierA.Z2GaugeWilsonRatio

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

noncomputable local instance gaugeDualPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p


noncomputable def gaugeDualCoupling (K : ℝ) : ℝ :=
  -Real.log (Real.tanh K) / 2


theorem tanh_pos_of_pos {K : ℝ} (hK : 0 < K) : 0 < Real.tanh K := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hK) (Real.cosh_pos K)


theorem gaugeDualCoupling_pos {K : ℝ} (hK : 0 < K) :
    0 < gaugeDualCoupling K := by
  have htPos : 0 < Real.tanh K := tanh_pos_of_pos hK
  have hlog : Real.log (Real.tanh K) < 0 :=
    Real.log_neg htPos (Real.tanh_lt_one K)
  unfold gaugeDualCoupling
  linarith



theorem exp_neg_two_mul_gaugeDualCoupling {K : ℝ} (hK : 0 < K) :
    Real.exp (-2 * gaugeDualCoupling K) = Real.tanh K := by
  have htPos : 0 < Real.tanh K := tanh_pos_of_pos hK
  rw [show -2 * gaugeDualCoupling K = Real.log (Real.tanh K) by
    unfold gaugeDualCoupling
    ring]
  exact Real.exp_log htPos



theorem exp_two_mul_gaugeDualCoupling {K : ℝ} (hK : 0 < K) :
    Real.exp (2 * gaugeDualCoupling K) = Real.cosh K / Real.sinh K := by
  calc
    Real.exp (2 * gaugeDualCoupling K) =
        (Real.exp (-2 * gaugeDualCoupling K))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    _ = (Real.tanh K)⁻¹ := by rw [exp_neg_two_mul_gaugeDualCoupling hK]
    _ = Real.cosh K / Real.sinh K := by
      rw [Real.tanh_eq_sinh_div_cosh, inv_div]

omit [Fintype P] [DecidableEq P] in


theorem prod_tanh_eq_prod_dualActivity (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (A : Finset P) :
    (∏ p ∈ A, Real.tanh (K p)) =
      ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p)) := by
  apply Finset.prod_congr rfl
  intro p _
  exact (exp_neg_two_mul_gaugeDualCoupling (hK p)).symm

omit [Fintype E] [DecidableEq P] in

theorem gaugeClosedSurfaceSum_eq_dualActivity
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p) :
    gaugeClosedSurfaceSum incidence K =
      ∑ A ∈ (Finset.univ : Finset P).powerset.filter
          (IsClosedPlaquetteSet incidence),
        ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p)) := by
  unfold gaugeClosedSurfaceSum
  apply Finset.sum_congr rfl
  intro A _
  exact prod_tanh_eq_prod_dualActivity K hK A

omit [Fintype E] [DecidableEq P] in

theorem gaugeWilsonSurfaceSum_eq_dualActivity
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (L : Finset E) :
    gaugeWilsonSurfaceSum incidence K L =
      ∑ A ∈ (Finset.univ : Finset P).powerset.filter
          (fun A => HasWilsonBoundary incidence A L),
        ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p)) := by
  unfold gaugeWilsonSurfaceSum
  apply Finset.sum_congr rfl
  intro A _
  exact prod_tanh_eq_prod_dualActivity K hK A

omit [DecidableEq P] in


theorem gaugePartition_dualActivity
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p) :
    gaugePartition incidence K =
      (2 : ℝ) ^ Fintype.card E * (∏ p : P, Real.cosh (K p)) *
        ∑ A ∈ (Finset.univ : Finset P).powerset.filter
            (IsClosedPlaquetteSet incidence),
          ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p)) := by
  rw [gaugePartition_highTemp]
  congr 1
  exact gaugeClosedSurfaceSum_eq_dualActivity incidence K hK

omit [DecidableEq P] in


theorem gaugeWilsonExpectation_eq_dualActivityRatio
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (L : Finset E) :
    gaugeWilsonExpectation incidence K L =
      (∑ A ∈ (Finset.univ : Finset P).powerset.filter
          (fun A => HasWilsonBoundary incidence A L),
        ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p))) /
      (∑ A ∈ (Finset.univ : Finset P).powerset.filter
          (IsClosedPlaquetteSet incidence),
        ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p))) := by
  rw [gaugeWilsonExpectation_eq_surfaceRatio,
    gaugeWilsonSurfaceSum_eq_dualActivity incidence K hK L,
    gaugeClosedSurfaceSum_eq_dualActivity incidence K hK]

end StatMech.FrontierA
