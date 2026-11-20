/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.FiniteCurrentConditionalPMF
import Code.FrontierB.BoundaryCurrentTail

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def boundaryParityAllowed (interior : Finset V)
    (H : Finset (Sym2 V)) : Prop :=
  H ⊆ G.edgeFinset ∧
    sources G (edgeIndicatorCurrent H) ∩ interior = ∅

noncomputable def boundaryParityRawMass (beta : ℝ)
    (interior : Finset V) (H : Finset (Sym2 V)) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal
    (if boundaryParityAllowed G interior H then
        Real.tanh beta ^ H.card else 0)

noncomputable def boundaryParityPartition (beta : ℝ)
    (interior : Finset V) : ℝ := by
  classical
  exact ∑ H : Finset (Sym2 V),
    if boundaryParityAllowed G interior H then
        Real.tanh beta ^ H.card else 0

noncomputable def boundaryParityAvoidSum (beta : ℝ)
    (interior : Finset V) (F : Finset (Sym2 V)) : ℝ := by
  classical
  exact ∑ H : Finset (Sym2 V),
    if boundaryParityAllowed G interior H ∧ Disjoint H F then
      Real.tanh beta ^ H.card else 0

theorem boundaryPartitionJ_high_temp
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V) :
    boundaryPartitionJ G beta J interior =
      (2 : ℝ) ^ interior.card *
        (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          ∑ H ∈ G.edgeFinset.powerset,
            if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
              highTempSubgraphWeight beta J H else 0 := by
  unfold boundaryPartitionJ
  simp_rw [boltzmannJ_high_temp_factor G beta J]
  have hexpand (s : ConfigSpace ↑interior) :
      (∏ e ∈ G.edgeFinset,
          (1 + Real.tanh (beta * J e) *
            bond (extendInteriorPlus interior s) e)) =
        ∑ H ∈ G.edgeFinset.powerset,
          ∏ e ∈ H, (Real.tanh (beta * J e) *
            bond (extendInteriorPlus interior s) e) :=
    Finset.prod_one_add _
  simp_rw [hexpand]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [show (2 : ℝ) ^ interior.card *
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        (∑ H ∈ G.edgeFinset.powerset,
          if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
            highTempSubgraphWeight beta J H else 0) =
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        ((2 : ℝ) ^ interior.card *
          ∑ H ∈ G.edgeFinset.powerset,
            if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
              highTempSubgraphWeight beta J H else 0) by ring]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H hH
  have hHsub : H ⊆ G.edgeFinset := Finset.mem_powerset.mp hH
  have hfactor (s : ConfigSpace ↑interior) :
      (∏ e ∈ H, (Real.tanh (beta * J e) *
        bond (extendInteriorPlus interior s) e)) =
      highTempSubgraphWeight beta J H *
        ∏ e ∈ H, bond (extendInteriorPlus interior s) e := by
    unfold highTempSubgraphWeight
    rw [Finset.prod_mul_distrib]
  simp_rw [hfactor]
  rw [← Finset.mul_sum]
  have hbonds (s : ConfigSpace ↑interior) :
      (∏ e ∈ H, bond (extendInteriorPlus interior s) e) =
        ∏ e ∈ G.edgeFinset,
          bond (extendInteriorPlus interior s) e ^ edgeIndicatorCurrent H e := by
    rw [show (∏ e ∈ H, bond (extendInteriorPlus interior s) e) =
        ∏ e ∈ H,
          bond (extendInteriorPlus interior s) e ^ edgeIndicatorCurrent H e by
      apply Finset.prod_congr rfl
      intro e he
      simp [edgeIndicatorCurrent, he]]
    apply Finset.prod_subset hHsub
    intro e heG heH
    simp [edgeIndicatorCurrent, heH]
  simp_rw [hbonds]
  rw [interiorSpinSum_monomial_eq G interior (edgeIndicatorCurrent H)]
  by_cases hs : sources G (edgeIndicatorCurrent H) ∩ interior = ∅ <;>
    simp [hs, mul_assoc, mul_comm, mul_left_comm]

theorem boundaryPartitionJ_unit_high_temp
    (beta : ℝ) (interior : Finset V) :
    boundaryPartitionJ G beta (fun _ => 1) interior =
      (2 : ℝ) ^ interior.card *
        Real.cosh beta ^ G.edgeFinset.card *
          boundaryParityPartition G beta interior := by
  rw [boundaryPartitionJ_high_temp]
  simp only [mul_one, Finset.prod_const]
  change ((2 : ℝ) ^ interior.card * Real.cosh beta ^ G.edgeFinset.card) *
      (∑ H ∈ G.edgeFinset.powerset,
        if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
          highTempSubgraphWeight beta (fun _ => 1) H else 0) =
    ((2 : ℝ) ^ interior.card * Real.cosh beta ^ G.edgeFinset.card) *
      boundaryParityPartition G beta interior
  congr 1
  unfold boundaryParityPartition boundaryParityAllowed
  apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
  · intro H hgap
    have hnot : H ∉ G.edgeFinset.powerset := (Finset.mem_sdiff.mp hgap).2
    have hsub : ¬ H ⊆ G.edgeFinset := by simpa using hnot
    simp [hsub]
  · intro H hpow
    have hsub : H ⊆ G.edgeFinset := Finset.mem_powerset.mp hpow
    by_cases hs : sources G (edgeIndicatorCurrent H) ∩ interior = ∅ <;>
      simp [highTempSubgraphWeight, hsub, hs]

theorem boundaryPartitionJ_deleted_high_temp
    (beta : ℝ) (interior : Finset V)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    boundaryPartitionJ G beta (deletedEdgeCoupling F) interior =
      (2 : ℝ) ^ interior.card *
        Real.cosh beta ^ (G.edgeFinset.card - F.card) *
          boundaryParityAvoidSum G beta interior F := by
  rw [boundaryPartitionJ_high_temp,
    deletedEdgeCoupling_cosh_prod G beta F hF]
  change ((2 : ℝ) ^ interior.card *
      Real.cosh beta ^ (G.edgeFinset.card - F.card)) *
      (∑ H ∈ G.edgeFinset.powerset,
        if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
          highTempSubgraphWeight beta (deletedEdgeCoupling F) H else 0) =
    ((2 : ℝ) ^ interior.card *
      Real.cosh beta ^ (G.edgeFinset.card - F.card)) *
      boundaryParityAvoidSum G beta interior F
  congr 1
  unfold boundaryParityAvoidSum boundaryParityAllowed
  apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
  · intro H hgap
    have hnot : H ∉ G.edgeFinset.powerset := (Finset.mem_sdiff.mp hgap).2
    have hsub : ¬ H ⊆ G.edgeFinset := by simpa using hnot
    simp [hsub]
  · intro H hpow
    have hsub : H ⊆ G.edgeFinset := Finset.mem_powerset.mp hpow
    by_cases hs : sources G (edgeIndicatorCurrent H) ∩ interior = ∅
    · by_cases hd : Disjoint H F
      · have hw : highTempSubgraphWeight beta (deletedEdgeCoupling F) H =
            Real.tanh beta ^ H.card := by
          unfold highTempSubgraphWeight
          rw [← Finset.prod_const]
          apply Finset.prod_congr rfl
          intro e he
          have heF : e ∉ F := fun hef => Finset.disjoint_left.mp hd he hef
          simp [deletedEdgeCoupling, heF]
        simp [hsub, hs, hd, hw]
      · have hw : highTempSubgraphWeight beta (deletedEdgeCoupling F) H = 0 := by
          unfold highTempSubgraphWeight
          rw [Finset.not_disjoint_iff_nonempty_inter] at hd
          obtain ⟨e, he⟩ := hd
          apply Finset.prod_eq_zero (Finset.mem_inter.mp he).1
          simp [deletedEdgeCoupling, (Finset.mem_inter.mp he).2]
        simp [hsub, hs, hd, hw]
    · simp [hsub, hs]

theorem tsum_boundaryCurrentRawMass_fixedParity
    (beta : ℝ) (hbeta : 0 ≤ beta) (interior : Finset V)
    (H : Finset (Sym2 V)) :
    (∑' m : EdgeCurrent G,
      if currentParitySupport G m = H then
        boundaryCurrentRawMass G beta (fun _ => 1) interior m else 0) =
      boundaryParityRawMass G beta interior H *
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
  by_cases hH : H ⊆ G.edgeFinset
  · by_cases hsrc : sources G (edgeIndicatorCurrent H) ∩ interior = ∅
    · let f : EdgeCurrent G → ℝ := fun m =>
        if currentParitySupport G m = H then
          weight G beta (fun _ => 1) (ofEdgeFun G m) else 0
      have hf_nonneg : ∀ m, 0 ≤ f m := by
        intro m
        simp only [f]
        split
        · exact acw_weight_nonneg G beta (fun _ => 1)
            hbeta (fun _ => zero_le_one) _
        · exact le_rfl
      have hf_summable : Summable f := by
        refine Summable.of_nonneg_of_le hf_nonneg (fun m => ?_)
          (summable_norm_weight_ofEdgeFun G beta (fun _ => 1)).of_norm
        simp only [f]
        split
        · exact le_rfl
        · exact acw_weight_nonneg G beta (fun _ => 1)
            hbeta (fun _ => zero_le_one) _
      calc
        (∑' m : EdgeCurrent G,
            if currentParitySupport G m = H then
              boundaryCurrentRawMass G beta (fun _ => 1) interior m else 0) =
            ∑' m : EdgeCurrent G, ENNReal.ofReal (f m) := by
          apply tsum_congr
          intro m
          by_cases hm : currentParitySupport G m = H
          · have hsource :
                sources G (ofEdgeFun G m) ∩ interior = ∅ := by
              rw [sources_eq_sources_currentParitySupport G m, hm]
              exact hsrc
            simp [boundaryCurrentRawMass, f, hm, hsource]
          · simp [f, hm]
        _ = ENNReal.ofReal (∑' m : EdgeCurrent G, f m) :=
          (ENNReal.ofReal_tsum_of_nonneg hf_nonneg hf_summable).symm
        _ = ENNReal.ofReal
              (Real.cosh beta ^ G.edgeFinset.card *
                Real.tanh beta ^ H.card) := by
          apply congrArg ENNReal.ofReal
          exact fixedParity_weight_tsum_closed G beta hbeta H hH
        _ = boundaryParityRawMass G beta interior H *
              ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          simp [boundaryParityRawMass, boundaryParityAllowed, hH, hsrc,
            mul_comm]
    · have hzero : ∀ m : EdgeCurrent G,
          (if currentParitySupport G m = H then
            boundaryCurrentRawMass G beta (fun _ => 1) interior m else 0) = 0 := by
        intro m
        by_cases hm : currentParitySupport G m = H
        · have hsource : sources G (ofEdgeFun G m) ∩ interior ≠ ∅ := by
            rw [sources_eq_sources_currentParitySupport G m, hm]
            exact hsrc
          simp [boundaryCurrentRawMass, hm, hsource]
        · simp [hm]
      simp_rw [hzero]
      simp [boundaryParityRawMass, boundaryParityAllowed, hH, hsrc]
  · have hne : ∀ m : EdgeCurrent G, currentParitySupport G m ≠ H := by
      intro m hm
      apply hH
      rw [← hm]
      exact currentParitySupport_subset G m
    simp_rw [if_neg (hne _)]
    simp [boundaryParityRawMass, boundaryParityAllowed, hH]

theorem boundaryCurrentSum_eq_boundaryParityPartition
    (beta : ℝ) (hbeta : 0 ≤ beta) (interior : Finset V) :
    ENNReal.ofReal (boundaryCurrentSum G beta (fun _ => 1) interior) =
      ENNReal.ofReal (boundaryParityPartition G beta interior) *
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
  rw [← tsum_boundaryCurrentRawMass G beta (fun _ => 1) hbeta
    (fun _ => zero_le_one) interior]
  let p : EdgeCurrent G → Finset (Sym2 V) := currentParitySupport G
  have hfiber := ENNReal.tsum_fiberwise
    (boundaryCurrentRawMass G beta (fun _ => 1) interior) p
  rw [tsum_fintype] at hfiber
  rw [← hfiber]
  simp_rw [show ∀ H : Finset (Sym2 V),
      (∑' b : ↑(p ⁻¹' {H}),
        boundaryCurrentRawMass G beta (fun _ => 1) interior b.1) =
      ∑' m : EdgeCurrent G,
        if currentParitySupport G m = H then
          boundaryCurrentRawMass G beta (fun _ => 1) interior m else 0 by
    intro H
    rw [tsum_subtype]
    apply tsum_congr
    intro m
    by_cases hm : currentParitySupport G m = H
    · simp [p, hm]
    · simp [p, hm]]
  simp_rw [tsum_boundaryCurrentRawMass_fixedParity G beta hbeta interior]
  rw [← Finset.sum_mul]
  unfold boundaryParityRawMass boundaryParityPartition
  rw [← ENNReal.ofReal_sum_of_nonneg]
  intro H hH
  split
  · exact pow_nonneg (tanh_nonneg_of_nonneg hbeta) _
  · exact le_rfl

noncomputable def boundaryParityPMF (beta : ℝ) (hbeta : 0 ≤ beta)
    (interior : Finset V) : PMF (Finset (Sym2 V)) :=
  PMF.map (currentParitySupport G)
    (boundaryCurrentPMF G beta (fun _ => 1) hbeta
      (fun _ => zero_le_one) interior)

theorem boundaryParityPMF_apply
    (beta : ℝ) (hbeta : 0 ≤ beta) (interior : Finset V)
    (H : Finset (Sym2 V)) :
    boundaryParityPMF G beta hbeta interior H =
      boundaryParityRawMass G beta interior H *
        (ENNReal.ofReal (boundaryParityPartition G beta interior))⁻¹ := by
  rw [boundaryParityPMF, PMF.map_apply]
  simp_rw [boundaryCurrentPMF_apply]
  let Z := ENNReal.ofReal
    (boundaryCurrentSum G beta (fun _ => 1) interior)
  calc
    (∑' m : EdgeCurrent G,
        if H = currentParitySupport G m then
          boundaryCurrentRawMass G beta (fun _ => 1) interior m * Z⁻¹ else 0) =
        (∑' m : EdgeCurrent G,
          if currentParitySupport G m = H then
            boundaryCurrentRawMass G beta (fun _ => 1) interior m else 0) * Z⁻¹ := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro m
      by_cases hm : currentParitySupport G m = H
      · simp [hm]
      · have hm' : H ≠ currentParitySupport G m := Ne.symm hm
        simp [hm, hm']
    _ = boundaryParityRawMass G beta interior H *
          ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) * Z⁻¹ := by
      rw [tsum_boundaryCurrentRawMass_fixedParity G beta hbeta interior H]
    _ = boundaryParityRawMass G beta interior H *
          (ENNReal.ofReal (boundaryParityPartition G beta interior))⁻¹ := by
      have hc0 : ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) ≠ 0 :=
        (ENNReal.ofReal_pos.2 (by positivity)).ne'
      have hcT : ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      dsimp [Z]
      rw [boundaryCurrentSum_eq_boundaryParityPartition G beta hbeta interior]
      change _ * _ * (_ * _)⁻¹ = _
      rw [ENNReal.mul_inv (Or.inr hcT)
        (Or.inl ENNReal.ofReal_ne_top)]
      calc
        boundaryParityRawMass G beta interior H *
              ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) *
            ((ENNReal.ofReal (boundaryParityPartition G beta interior))⁻¹ *
              (ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card))⁻¹) =
            boundaryParityRawMass G beta interior H *
              (ENNReal.ofReal (boundaryParityPartition G beta interior))⁻¹ *
                (ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) *
                  (ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card))⁻¹) := by
          ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel hc0 hcT, mul_one]

theorem boundaryParityPartition_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) (interior : Finset V) :
    0 < boundaryParityPartition G beta interior := by
  classical
  unfold boundaryParityPartition
  have hempty : boundaryParityAllowed G interior
      (∅ : Finset (Sym2 V)) := by
    constructor
    · exact Finset.empty_subset _
    · rw [show edgeIndicatorCurrent (∅ : Finset (Sym2 V)) = 0 by
        funext e
        simp [edgeIndicatorCurrent]]
      have hz : Sharpness.sources G (0 : Sharpness.Current V) = ∅ := by
        ext x
        simp [Sharpness.sources, Sharpness.incidentFlux]
      rw [hz]
      exact Finset.empty_inter interior
  have hnonneg : ∀ H : Finset (Sym2 V),
      0 ≤ if boundaryParityAllowed G interior H then
        Real.tanh beta ^ H.card else 0 := by
    intro H
    split
    · exact pow_nonneg (tanh_nonneg_of_nonneg hbeta) _
    · exact le_rfl
  have hle := Finset.single_le_sum
    (s := (Finset.univ : Finset (Finset (Sym2 V))))
    (fun H _ => hnonneg H) (Finset.mem_univ (∅ : Finset (Sym2 V)))
  have hemptyTerm :
      (if boundaryParityAllowed G interior (∅ : Finset (Sym2 V)) then
        Real.tanh beta ^ (∅ : Finset (Sym2 V)).card else 0) = 1 := by
    rw [if_pos hempty]
    simp
  rw [hemptyTerm] at hle
  exact Real.zero_lt_one.trans_le hle

theorem boundaryParityMeasure_avoid
    (beta : ℝ) (hbeta : 0 ≤ beta) (interior : Finset V)
    (F : Finset (Sym2 V)) :
    (boundaryParityPMF G beta hbeta interior).toMeasure
        {H | Disjoint H F} =
      ENNReal.ofReal
        (boundaryParityAvoidSum G beta interior F /
          boundaryParityPartition G beta interior) := by
  classical
  rw [PMF.toMeasure_apply_eq_tsum, tsum_fintype,
    ENNReal.ofReal_div_of_pos
      (boundaryParityPartition_pos G beta hbeta interior)]
  let p := ENNReal.ofReal (boundaryParityPartition G beta interior)
  calc
    (∑ H : Finset (Sym2 V),
        {H | Disjoint H F}.indicator
          (boundaryParityPMF G beta hbeta interior) H) =
      ∑ H : Finset (Sym2 V),
        (if Disjoint H F then
          boundaryParityRawMass G beta interior H else 0) * p⁻¹ := by
        apply Finset.sum_congr rfl
        intro H hH
        by_cases hd : Disjoint H F
        · rw [Set.indicator_of_mem hd, boundaryParityPMF_apply]
          simp [p, hd]
        · rw [Set.indicator_of_notMem hd]
          simp [hd]
    _ = (∑ H : Finset (Sym2 V),
        if Disjoint H F then
          boundaryParityRawMass G beta interior H else 0) * p⁻¹ := by
      rw [Finset.sum_mul]
    _ = ENNReal.ofReal (boundaryParityAvoidSum G beta interior F) * p⁻¹ := by
      congr 1
      unfold boundaryParityAvoidSum boundaryParityRawMass
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro H hH
        by_cases hd : Disjoint H F <;>
          by_cases ha : boundaryParityAllowed G interior H <;>
            simp [hd, ha]
      · intro H hH
        split
        · exact pow_nonneg (tanh_nonneg_of_nonneg hbeta) _
        · exact le_rfl

theorem boundaryParityAvoidRatio_eq_spinExpectation
    (beta : ℝ) (interior : Finset V)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    boundaryParityAvoidSum G beta interior F /
        boundaryParityPartition G beta interior =
      ((∑ s : ConfigSpace ↑interior,
          boltzmannJ G beta (fun _ => 1) (extendInteriorPlus interior s) *
            Real.exp (-beta * edgeSpinSum F
              (extendInteriorPlus interior s))) /
        boundaryPartitionJ G beta (fun _ => 1) interior) *
          Real.cosh beta ^ F.card := by
  have hnum :
      (∑ s : ConfigSpace ↑interior,
          boltzmannJ G beta (fun _ => 1) (extendInteriorPlus interior s) *
            Real.exp (-beta * edgeSpinSum F
              (extendInteriorPlus interior s))) =
        boundaryPartitionJ G beta (deletedEdgeCoupling F) interior := by
    unfold boundaryPartitionJ
    apply Finset.sum_congr rfl
    intro s hs
    exact boltzmannJ_mul_exp_neg_edgeSpinSum G beta F hF _
  rw [hnum, boundaryPartitionJ_unit_high_temp,
    boundaryPartitionJ_deleted_high_temp G beta interior F hF]
  have htwo : (2 : ℝ) ^ interior.card ≠ 0 := by positivity
  have hcosh : Real.cosh beta ≠ 0 := ne_of_gt (Real.cosh_pos beta)
  have hpartition : boundaryParityPartition G beta interior ≠ 0 := by
    have hpos : 0 < boundaryPartitionJ G beta (fun _ => 1) interior := by
      unfold boundaryPartitionJ
      apply Finset.sum_pos
      · intro s hs
        exact Real.exp_pos _
      · exact Finset.univ_nonempty
    rw [boundaryPartitionJ_unit_high_temp] at hpos
    have hfac : 0 < (2 : ℝ) ^ interior.card *
        Real.cosh beta ^ G.edgeFinset.card := by positivity
    exact ne_of_gt (pos_of_mul_pos_right hpos hfac.le)
  have hcard : G.edgeFinset.card - F.card + F.card =
      G.edgeFinset.card := by
    rw [Nat.sub_add_cancel (Finset.card_le_card hF)]
  field_simp [hpartition]
  calc
    boundaryParityAvoidSum G beta interior F *
          Real.cosh beta ^ G.edgeFinset.card =
        boundaryParityAvoidSum G beta interior F *
          Real.cosh beta ^ (G.edgeFinset.card - F.card + F.card) := by
      rw [hcard]
    _ = boundaryParityAvoidSum G beta interior F *
          (Real.cosh beta ^ (G.edgeFinset.card - F.card) *
            Real.cosh beta ^ F.card) := by rw [pow_add]
    _ = boundaryParityAvoidSum G beta interior F *
          Real.cosh beta ^ (G.edgeFinset.card - F.card) *
            Real.cosh beta ^ F.card := by ring

theorem boundaryParityMeasure_avoid_eq_spinExpectation
    (beta : ℝ) (hbeta : 0 ≤ beta) (interior : Finset V)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    (boundaryParityPMF G beta hbeta interior).toMeasure
        {H | Disjoint H F} =
      ENNReal.ofReal
        (((∑ s : ConfigSpace ↑interior,
            boltzmannJ G beta (fun _ => 1) (extendInteriorPlus interior s) *
              Real.exp (-beta * edgeSpinSum F
                (extendInteriorPlus interior s))) /
          boundaryPartitionJ G beta (fun _ => 1) interior) *
            Real.cosh beta ^ F.card) := by
  rw [boundaryParityMeasure_avoid]
  exact congrArg ENNReal.ofReal
    (boundaryParityAvoidRatio_eq_spinExpectation G beta interior F hF)

theorem boundaryCurrentPMF_apply_eq_parity_factor
    (beta : ℝ) (hbeta : 0 < beta) (interior : Finset V)
    (m : EdgeCurrent G) :
    boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) interior m =
      boundaryParityPMF G beta hbeta.le interior
          (currentParitySupport G m) *
        parityCurrentPMF G beta hbeta (currentParitySupport G m) m := by
  let H := currentParitySupport G m
  have hH : H ⊆ G.edgeFinset := currentParitySupport_subset G m
  rw [boundaryCurrentPMF_apply, boundaryParityPMF_apply,
    parityCurrentPMF_apply]
  by_cases hsrc : sources G (ofEdgeFun G m) ∩ interior = ∅
  · have hallowed : boundaryParityAllowed G interior H := by
      exact ⟨hH, by
        rw [← sources_eq_sources_currentParitySupport G m]
        exact hsrc⟩
    have hkernel : 0 ≤ parityCurrentKernel G beta H m := by
      unfold parityCurrentKernel
      exact Finset.prod_nonneg fun e _ =>
        parityEdgeKernel_nonneg beta hbeta (e.1 ∈ H) (m e)
    have htanh : 0 ≤ Real.tanh beta ^ H.card :=
      pow_nonneg (tanh_nonneg_of_nonneg hbeta.le) _
    have hcosh : 0 ≤ Real.cosh beta ^ G.edgeFinset.card := by positivity
    have hw : ENNReal.ofReal
          (weight G beta (fun _ => 1) (ofEdgeFun G m)) =
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) *
          ENNReal.ofReal (Real.tanh beta ^ H.card) *
            ENNReal.ofReal (parityCurrentKernel G beta H m) := by
      rw [weight_eq_parityFiberMass_mul_kernel G beta hbeta H hH m rfl,
        parityFiberMass_closed G beta hbeta.le H hH,
        ENNReal.ofReal_mul (mul_nonneg hcosh htanh),
        ENNReal.ofReal_mul hcosh]
    let c : ℝ≥0∞ := ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card)
    let t : ℝ≥0∞ := ENNReal.ofReal (Real.tanh beta ^ H.card)
    let p : ℝ≥0∞ := ENNReal.ofReal
      (boundaryParityPartition G beta interior)
    let k : ℝ≥0∞ := ENNReal.ofReal (parityCurrentKernel G beta H m)
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
    simp only [boundaryCurrentRawMass, hsrc, if_true,
      boundaryParityRawMass, hallowed, H]
    rw [hw, boundaryCurrentSum_eq_boundaryParityPartition G beta hbeta.le interior]
    change c * t * k * (p * c)⁻¹ = t * p⁻¹ * k
    rw [ENNReal.mul_inv (Or.inr hcTop) (Or.inl ENNReal.ofReal_ne_top)]
    calc
      c * t * k * (p⁻¹ * c⁻¹) =
          (c * c⁻¹) * (t * p⁻¹ * k) := by ac_rfl
      _ = t * p⁻¹ * k := by
        rw [ENNReal.mul_inv_cancel hc0 hcTop, one_mul]
  · have hnotAllowed : ¬ boundaryParityAllowed G interior H := by
      intro ha
      apply hsrc
      rw [sources_eq_sources_currentParitySupport G m]
      exact ha.2
    have hraw : boundaryParityRawMass G beta interior
        (currentParitySupport G m) = 0 := by
      simp [boundaryParityRawMass, H, hnotAllowed]
    rw [hraw]
    simp [boundaryCurrentRawMass, hsrc]

theorem boundaryCurrentPMF_eq_parity_bind
    (beta : ℝ) (hbeta : 0 < beta) (interior : Finset V) :
    boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) interior =
      (boundaryParityPMF G beta hbeta.le interior).bind
        (parityCurrentPMF G beta hbeta) := by
  apply PMF.ext
  intro m
  rw [PMF.bind_apply,
    boundaryCurrentPMF_apply_eq_parity_factor G beta hbeta interior m]
  symm
  rw [tsum_eq_single (currentParitySupport G m)]
  intro H hne
  by_cases hH : H ⊆ G.edgeFinset
  · have hk : parityCurrentKernel G beta H m = 0 :=
      parityCurrentKernel_eq_zero_of_support_ne G beta H hH m (Ne.symm hne)
    rw [parityCurrentPMF_apply]
    simp [hk]
  · rw [boundaryParityPMF_apply]
    simp [boundaryParityRawMass, boundaryParityAllowed, hH]

theorem boundaryCurrentFiniteMarginal_eq_localParity_bind
    (beta : ℝ) (hbeta : 0 < beta) (interior : Finset V)
    (S : Finset G.edgeFinset) :
    PMF.map (restrictCurrent S)
        (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
          (fun _ => zero_le_one) interior) =
      (PMF.map (restrictParity G S)
        (boundaryParityPMF G beta hbeta.le interior)).bind
          (finiteParityPMF S beta hbeta) := by
  rw [boundaryCurrentPMF_eq_parity_bind G beta hbeta interior, PMF.map_bind]
  rw [PMF.bind_map]
  congr 1
  funext H
  rw [parityCurrentPMF_map_restrictCurrent G beta hbeta H S]
  rfl


end StatMech.FrontierB
