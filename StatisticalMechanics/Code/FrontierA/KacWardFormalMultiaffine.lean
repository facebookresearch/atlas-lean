/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardStraightLineDeletion










open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

open StatMech.Onsager



theorem kwGraph_formalRoot_coeff_eq_zero_of_repeated_of_scaleEdge_affine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (selected : G.Dart) (m : Sym2 V →₀ ℕ)
    (hrepeated : 2 ≤ m selected.edge)
    (haffine : ∀ (weight : Sym2 V → ℂ) (t : ℂ) (q : ℝ),
      0 ≤ q →
      (∀ dart next,
        ‖ons_scaleColumns
          ({selected, selected.symm} : Finset G.Dart) t
          (kwGraphTransition G weight phase) dart next‖ ≤ q) →
      q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹ →
      (Fintype.card G.Dart : ℝ) * q < 1 →
      ons_detWalkRoot
          (kwGraphTransition G
            (kwScaleGraphEdgeWeight weight selected.edge t) phase) =
        ons_detWalkRoot
            (ons_maskMatrix ({selected, selected.symm} : Finset G.Dart)
              (kwGraphTransition G weight phase)) *
          (1 - t * ∑' path, ons_firstReturnWeight
            (kwGraphTransition G weight phase)
            selected selected.symm path)) :
    MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0 := by
  letI : Nonempty G.Dart := ⟨selected⟩
  let root := kwGraphFormalRoot G phase
  let second := kwGraphFormalSecondDifference root selected.edge
  have hsecond : MvPowerSeries.coeff m second = 0 := by
    apply ons_coeff_eq_zero_of_degreeFiberCoeff second m
    intro weight
    let radius : ℝ := (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹
    let R : ℝ := min 1 radius
    let r : ℝ := R / 4
    let q : ℝ := 2 * r
    let S : ℝ := ∑ dart : G.Dart, ∑ next : G.Dart,
      ‖kwGraphTransition G weight phase dart next‖
    let c : ℂ := ((r / (1 + S) : ℝ) : ℂ)
    let base : Sym2 V → ℂ := fun edge ↦ c * weight edge
    have hradius : 0 < radius := by
      dsimp only [radius]
      positivity
    have hR : 0 < R := by
      dsimp only [R]
      exact lt_min (by norm_num) hradius
    have hRradius : R ≤ radius := min_le_right _ _
    have hr : 0 < r := by dsimp only [r]; linarith
    have hq : 0 < q := by dsimp only [q]; linarith
    have hsmall : q < radius := by
      dsimp only [q, r]
      linarith
    have hcard : (Fintype.card G.Dart : ℝ) * q < 1 :=
      ons_card_mul_lt_one_of_Sherman_small q hsmall
    have hS : 0 ≤ S := by
      dsimp only [S]
      exact Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have hden : 0 < 1 + S := by linarith
    have hc : c ≠ 0 := by
      dsimp only [c]
      exact_mod_cast div_ne_zero (ne_of_gt hr) (ne_of_gt hden)
    have hraw (dart next : G.Dart) :
        ‖kwGraphTransition G weight phase dart next‖ ≤ S := by
      have hinner :
          ‖kwGraphTransition G weight phase dart next‖ ≤
            ∑ e : G.Dart, ‖kwGraphTransition G weight phase dart e‖ :=
        Finset.single_le_sum
          (fun e _ ↦ norm_nonneg
            (kwGraphTransition G weight phase dart e))
          (Finset.mem_univ next)
      exact hinner.trans <| Finset.single_le_sum
        (fun d _ ↦ Finset.sum_nonneg fun e _ ↦ norm_nonneg
          (kwGraphTransition G weight phase d e))
        (Finset.mem_univ dart)
    have hbase (dart next : G.Dart) :
        ‖kwGraphTransition G base phase dart next‖ ≤ r := by
      rw [show base = fun edge ↦ c * weight edge from rfl,
        kwGraphTransition_smulWeight, norm_mul]
      have hnormc : ‖c‖ = r / (1 + S) := by
        dsimp only [c]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hr.le hden.le)]
      rw [hnormc, div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [hraw dart next]
    have hrootSummable (t : ℂ) (ht : ‖t‖ ≤ 2) :
        ons_MvSeriesEvalSummable root
          (kwScaleGraphEdgeWeight base selected.edge t) := by
      apply kw_MvSeriesEvalSummable_GraphFormalRoot
        G phase (kwScaleGraphEdgeWeight base selected.edge t)
          q hq.le
      · intro dart next
        simpa only [q] using norm_kwGraphTransition_scaleEdge_le
          G base phase selected t r hr.le ht hbase dart next
      · exact hcard
    have hsumSecond : ons_MvSeriesEvalSummable second base := by
      apply kw_MvSeriesEvalSummable_GraphFormalSecondDifference
      · exact hrootSummable 2 (by norm_num)
      · simpa only [kwScaleGraphEdgeWeight_one] using
          hrootSummable 1 (by norm_num)
      · exact hrootSummable 0 (by norm_num)
    have hzero : ∀ᶠ s : ℂ in nhds 0,
        ons_mvSeriesEval second (fun edge ↦ s * base edge) = 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
        (by norm_num : (0 : ℝ) < 1)] with s hs
      have hs1 : ‖s‖ ≤ 1 := by
        have : ‖s‖ < 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using hs
        exact this.le
      let scaled : Sym2 V → ℂ := fun edge ↦ s * base edge
      have hscaled (dart next : G.Dart) :
          ‖kwGraphTransition G scaled phase dart next‖ ≤ r := by
        rw [show scaled = fun edge ↦ s * base edge from rfl,
          kwGraphTransition_smulWeight, norm_mul]
        calc
          ‖s‖ * ‖kwGraphTransition G base phase dart next‖ ≤
              1 * r := mul_le_mul hs1 (hbase dart next)
                (norm_nonneg _) (by norm_num)
          _ = r := one_mul r
      have hsum (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_MvSeriesEvalSummable root
            (kwScaleGraphEdgeWeight scaled selected.edge t) := by
        apply kw_MvSeriesEvalSummable_GraphFormalRoot
          G phase (kwScaleGraphEdgeWeight scaled selected.edge t)
            q hq.le
        · intro dart next
          simpa only [q] using norm_kwGraphTransition_scaleEdge_le
            G scaled phase selected t r hr.le ht hscaled dart next
        · exact hcard
      have heval (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_mvSeriesEval root
              (kwScaleGraphEdgeWeight scaled selected.edge t) =
            ons_detWalkRoot
              (kwGraphTransition G
                (kwScaleGraphEdgeWeight scaled selected.edge t) phase) := by
        apply kw_mvSeriesEval_GraphFormalRoot
          G phase (kwScaleGraphEdgeWeight scaled selected.edge t)
            q hq.le
        · intro dart next
          simpa only [q] using norm_kwGraphTransition_scaleEdge_le
            G scaled phase selected t r hr.le ht hscaled dart next
        · exact hcard
      let A := ons_detWalkRoot
        (ons_maskMatrix ({selected, selected.symm} : Finset G.Dart)
          (kwGraphTransition G scaled phase))
      let B := ∑' path, ons_firstReturnWeight
        (kwGraphTransition G scaled phase) selected selected.symm path
      have haff (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_detWalkRoot
              (kwGraphTransition G
                (kwScaleGraphEdgeWeight scaled selected.edge t) phase) =
            A * (1 - t * B) := by
        apply haffine scaled t q hq.le
        · intro dart next
          simpa only [q] using norm_kwScaleColumns_le
            ({selected, selected.symm} : Finset G.Dart) t
            (kwGraphTransition G scaled phase) r hr.le ht hscaled dart next
        · exact hsmall
        · exact hcard
      have hscaleOne :
          kwScaleGraphEdgeWeight scaled selected.edge 1 = scaled :=
        kwScaleGraphEdgeWeight_one scaled selected.edge
      rw [kw_mvSeriesEval_GraphFormalSecondDifference
        root selected.edge scaled
        (hsum 2 (by norm_num))
        (by simpa only [hscaleOne] using hsum 1 (by norm_num))
        (hsum 0 (by norm_num))]
      rw [heval 2 (by norm_num)]
      have heval1 : ons_mvSeriesEval root scaled =
          ons_detWalkRoot (kwGraphTransition G scaled phase) := by
        simpa only [hscaleOne] using heval 1 (by norm_num)
      have haff1 : ons_detWalkRoot (kwGraphTransition G scaled phase) =
          A * (1 - B) := by
        simpa only [hscaleOne, one_mul] using haff 1 (by norm_num)
      rw [heval1, heval 0 (by norm_num),
        haff 2 (by norm_num), haff1,
        haff 0 (by norm_num)]
      ring
    have hfiber :=
      ons_degreeFiberCoeff_eq_zero_of_eval_smul_eventually_zero
        second base hsumSecond hzero (Finsupp.degree m)
    change ons_degreeFiberCoeff second
      (fun edge ↦ c * weight edge) (Finsupp.degree m) = 0 at hfiber
    rw [ons_degreeFiberCoeff_scale] at hfiber
    exact (mul_eq_zero.mp hfiber).resolve_left (pow_ne_zero _ hc)
  change ons_secondDifferenceFactor (m selected.edge) *
      MvPowerSeries.coeff m root = 0 at hsecond
  exact (mul_eq_zero.mp hsecond).resolve_left
    (ons_secondDifferenceFactor_ne_zero (m selected.edge) hrepeated)



theorem kw_straightLineGraph_formalRoot_coeff_eq_zero_of_repeated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (selected : G.Dart) (m : Sym2 V →₀ ℕ)
    (hrepeated : 2 ≤ m selected.edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G embedding.turnPhase) = 0 := by
  apply kwGraph_formalRoot_coeff_eq_zero_of_repeated_of_scaleEdge_affine
    G embedding.turnPhase selected m hrepeated
  intro weight t q hq hentry hsmall hcard
  exact kwStraightLineGraph_detWalkRoot_scaleEdge_affine
    G embedding weight selected t q hq hentry hsmall hcard


theorem kw_straightLineGraph_formalRoot_coeff_eq_zero_of_repeated_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (edge : Sym2 V) (hedge : edge ∈ G.edgeFinset)
    (m : Sym2 V →₀ ℕ) (hrepeated : 2 ≤ m edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G embedding.turnPhase) = 0 := by
  rw [SimpleGraph.mem_edgeFinset] at hedge
  obtain ⟨v, w⟩ := edge
  let selected : G.Dart := ⟨(v, w), hedge⟩
  exact kw_straightLineGraph_formalRoot_coeff_eq_zero_of_repeated
    G embedding selected m hrepeated

end StatMech.FrontierA
