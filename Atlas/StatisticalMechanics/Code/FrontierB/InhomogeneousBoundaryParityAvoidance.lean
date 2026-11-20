/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.NonnegativeBoundaryCurrentConditionalPMF
import Code.FrontierB.InhomogeneousParityAvoidance









open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def inhomogeneousBoundaryParityPartition
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V) : ℝ :=
  ∑ H ∈ G.edgeFinset.powerset,
    if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
      highTempSubgraphWeight beta J H else 0

noncomputable def inhomogeneousBoundaryParityAvoidSum
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V)
    (F : Finset (Sym2 V)) : ℝ :=
  ∑ H ∈ G.edgeFinset.powerset,
    if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ ∧ Disjoint H F then
      highTempSubgraphWeight beta J H else 0

theorem boundaryCurrentSum_eq_cosh_mul_inhomogeneousBoundaryParityPartition
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V) :
    boundaryCurrentSum G beta J interior =
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        inhomogeneousBoundaryParityPartition G beta J interior := by
  have hspin := boundaryPartitionJ_high_temp G beta J interior
  have hcurrent := boundaryPartitionJ_eq_boundaryCurrentSum G beta J interior
  rw [hcurrent] at hspin
  have htwo : (2 : ℝ) ^ interior.card ≠ 0 := by positivity
  apply mul_left_cancel₀ htwo
  simpa only [inhomogeneousBoundaryParityPartition, mul_assoc] using hspin

theorem inhomogeneousBoundaryParityPartition_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (interior : Finset V) :
    0 < inhomogeneousBoundaryParityPartition G beta J interior := by
  unfold inhomogeneousBoundaryParityPartition
  have hempty : (∅ : Finset (Sym2 V)) ∈ G.edgeFinset.powerset := by simp
  have hallowed :
      sources G (edgeIndicatorCurrent (∅ : Finset (Sym2 V))) ∩ interior = ∅ := by
    have hz : Sharpness.sources G (0 : Sharpness.Current V) = ∅ := by
      ext x
      simp [Sharpness.sources, Sharpness.incidentFlux]
    rw [show edgeIndicatorCurrent (∅ : Finset (Sym2 V)) =
        (0 : Sharpness.Current V) by
      ext e
      simp [edgeIndicatorCurrent]]
    rw [hz]
    exact Finset.empty_inter interior
  have hnonneg : ∀ H ∈ G.edgeFinset.powerset,
      0 ≤ if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
        highTempSubgraphWeight beta J H else 0 := by
    intro H hH
    split
    · unfold highTempSubgraphWeight
      exact Finset.prod_nonneg fun e _ ↦
        tanh_nonneg_of_nonneg (mul_nonneg hbeta (hJ e))
    · exact le_rfl
  have hle := Finset.single_le_sum hnonneg hempty
  have hemptyTerm :
      (if sources G (edgeIndicatorCurrent (∅ : Finset (Sym2 V))) ∩ interior = ∅ then
        highTempSubgraphWeight beta J ∅ else 0) = 1 := by
    rw [if_pos hallowed]
    simp [highTempSubgraphWeight]
  rw [hemptyTerm] at hle
  exact Real.zero_lt_one.trans_le hle

open Classical in
theorem boundaryNonnegativeParityPMF_apply_eq_highTemp
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (interior : Finset V)
    (H : Finset (Sym2 V)) :
    boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior H =
      if hvalid : boundaryParityAllowed G interior H then
        ENNReal.ofReal (highTempSubgraphWeight beta J H) *
          (ENNReal.ofReal
            (inhomogeneousBoundaryParityPartition G beta J interior))⁻¹
      else 0 := by
  classical
  rw [boundaryNonnegativeParityPMF_apply G beta hbeta J hJ interior H]
  by_cases hvalid : boundaryParityAllowed G interior H
  · rw [dif_pos hvalid, boundaryNonnegativeParityRawMass, if_pos hvalid,
      inhomogeneousParityFiberMass_eq_cosh_mul_highTemp G beta J H hvalid.1,
      boundaryCurrentSum_eq_cosh_mul_inhomogeneousBoundaryParityPartition]
    let c : ℝ≥0∞ := ENNReal.ofReal
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e))
    let t : ℝ≥0∞ := ENNReal.ofReal (highTempSubgraphWeight beta J H)
    let p : ℝ≥0∞ := ENNReal.ofReal
      (inhomogeneousBoundaryParityPartition G beta J interior)
    have hcReal : 0 ≤ ∏ e ∈ G.edgeFinset,
        Real.cosh (beta * J e) := Finset.prod_nonneg fun e _ ↦
      (Real.cosh_pos _).le
    rw [ENNReal.ofReal_mul hcReal, ENNReal.ofReal_mul hcReal]
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
    change c * t * (c * p)⁻¹ = t * p⁻¹
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hcTop)]
    calc
      c * t * (c⁻¹ * p⁻¹) = (c * c⁻¹) * (t * p⁻¹) := by ac_rfl
      _ = t * p⁻¹ := by rw [ENNReal.mul_inv_cancel hc0 hcTop, one_mul]
  · rw [dif_neg hvalid, boundaryNonnegativeParityRawMass, if_neg hvalid,
      zero_mul]

theorem boundaryNonnegativeParityMeasure_avoid
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (interior : Finset V)
    (F : Finset (Sym2 V)) :
    (boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior).toMeasure
        {H | Disjoint H F} =
      ENNReal.ofReal
        (inhomogeneousBoundaryParityAvoidSum G beta J interior F /
          inhomogeneousBoundaryParityPartition G beta J interior) := by
  classical
  rw [PMF.toMeasure_apply_eq_tsum, tsum_fintype,
    ENNReal.ofReal_div_of_pos
      (inhomogeneousBoundaryParityPartition_pos
        G beta hbeta.le J hJ interior)]
  let p := ENNReal.ofReal
    (inhomogeneousBoundaryParityPartition G beta J interior)
  let r : Finset (Sym2 V) → ℝ := fun H ↦
    if boundaryParityAllowed G interior H ∧ Disjoint H F then
      highTempSubgraphWeight beta J H else 0
  have hrnonneg : ∀ H, 0 ≤ r H := by
    intro H
    simp only [r]
    split
    · unfold highTempSubgraphWeight
      exact Finset.prod_nonneg fun e _ ↦
        tanh_nonneg_of_nonneg (mul_nonneg hbeta.le (hJ e))
    · exact le_rfl
  have hrsum : (∑ H : Finset (Sym2 V), r H) =
      inhomogeneousBoundaryParityAvoidSum G beta J interior F := by
    unfold inhomogeneousBoundaryParityAvoidSum
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
    · intro H hgap
      have hnot : H ∉ G.edgeFinset.powerset := (Finset.mem_sdiff.mp hgap).2
      have hsub : ¬H ⊆ G.edgeFinset := by simpa using hnot
      simp [r, boundaryParityAllowed, hsub]
    · intro H hpow
      have hsub : H ⊆ G.edgeFinset := Finset.mem_powerset.mp hpow
      by_cases hs : sources G (edgeIndicatorCurrent H) ∩ interior = ∅ <;>
        by_cases hd : Disjoint H F <;>
          simp [r, boundaryParityAllowed, hsub, hs, hd]
  have hnum :
      (∑ H : Finset (Sym2 V),
        if Disjoint H F ∧ boundaryParityAllowed G interior H then
          ENNReal.ofReal (highTempSubgraphWeight beta J H) else 0) =
        ENNReal.ofReal
          (inhomogeneousBoundaryParityAvoidSum G beta J interior F) := by
    rw [← hrsum, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro H hH
      by_cases hv : boundaryParityAllowed G interior H <;>
        by_cases hd : Disjoint H F <;> simp [r, hv, hd]
    · intro H hH
      exact hrnonneg H
  calc
    (∑ H : Finset (Sym2 V),
        {H | Disjoint H F}.indicator
          (boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior) H) =
      ∑ H : Finset (Sym2 V),
        (if Disjoint H F ∧ boundaryParityAllowed G interior H then
          ENNReal.ofReal (highTempSubgraphWeight beta J H) else 0) * p⁻¹ := by
        apply Finset.sum_congr rfl
        intro H hH
        by_cases hd : Disjoint H F
        · rw [Set.indicator_of_mem hd,
            boundaryNonnegativeParityPMF_apply_eq_highTemp
              G beta hbeta J hJ interior H]
          by_cases hv : boundaryParityAllowed G interior H <;>
            simp [hd, hv, p]
        · rw [Set.indicator_of_notMem hd]
          simp [hd]
    _ = (∑ H : Finset (Sym2 V),
        if Disjoint H F ∧ boundaryParityAllowed G interior H then
          ENNReal.ofReal (highTempSubgraphWeight beta J H) else 0) * p⁻¹ := by
      rw [Finset.sum_mul]
    _ = ENNReal.ofReal
          (inhomogeneousBoundaryParityAvoidSum G beta J interior F) * p⁻¹ := by
      rw [hnum]

theorem inhomogeneousDeletedCoupling_boundary_highTemp_sum
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V)
    (F : Finset (Sym2 V)) :
    (∑ H ∈ G.edgeFinset.powerset,
      if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
        highTempSubgraphWeight beta (inhomogeneousDeletedCoupling J F) H
      else 0) =
      inhomogeneousBoundaryParityAvoidSum G beta J interior F := by
  unfold inhomogeneousBoundaryParityAvoidSum
  apply Finset.sum_congr rfl
  intro H hH
  by_cases hs : sources G (edgeIndicatorCurrent H) ∩ interior = ∅
  · rw [if_pos hs]
    by_cases hd : Disjoint H F
    · rw [if_pos ⟨hs, hd⟩]
      unfold highTempSubgraphWeight
      apply Finset.prod_congr rfl
      intro e heH
      have heF : e ∉ F := fun hef ↦ Finset.disjoint_left.mp hd heH hef
      simp [inhomogeneousDeletedCoupling, heF]
    · rw [if_neg (fun h ↦ hd h.2)]
      unfold highTempSubgraphWeight
      rw [Finset.not_disjoint_iff_nonempty_inter] at hd
      obtain ⟨e, he⟩ := hd
      apply Finset.prod_eq_zero (Finset.mem_inter.mp he).1
      simp [inhomogeneousDeletedCoupling, (Finset.mem_inter.mp he).2]
  · rw [if_neg hs, if_neg (fun h ↦ hs h.1)]

theorem boundaryPartitionJ_inhomogeneousDeleted_highTemp
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    boundaryPartitionJ G beta (inhomogeneousDeletedCoupling J F) interior =
      (2 : ℝ) ^ interior.card *
        (∏ e ∈ G.edgeFinset \ F, Real.cosh (beta * J e)) *
          inhomogeneousBoundaryParityAvoidSum G beta J interior F := by
  rw [boundaryPartitionJ_high_temp,
    inhomogeneousDeletedCoupling_cosh_prod G beta J F hF,
    inhomogeneousDeletedCoupling_boundary_highTemp_sum]

theorem inhomogeneousBoundaryParityAvoidRatio_eq_spinExpectation
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    inhomogeneousBoundaryParityAvoidSum G beta J interior F /
        inhomogeneousBoundaryParityPartition G beta J interior =
      ((∑ s : ConfigSpace ↑interior,
          boltzmannJ G beta J (extendInteriorPlus interior s) *
            Real.exp (-weightedEdgeSpinSum beta J F
              (extendInteriorPlus interior s))) /
        boundaryPartitionJ G beta J interior) *
          ∏ e ∈ F, Real.cosh (beta * J e) := by
  have hnum :
      (∑ s : ConfigSpace ↑interior,
          boltzmannJ G beta J (extendInteriorPlus interior s) *
            Real.exp (-weightedEdgeSpinSum beta J F
              (extendInteriorPlus interior s))) =
        boundaryPartitionJ G beta
          (inhomogeneousDeletedCoupling J F) interior := by
    unfold boundaryPartitionJ
    apply Finset.sum_congr rfl
    intro s hs
    exact boltzmannJ_mul_exp_neg_weightedEdgeSpinSum
      G beta J F hF (extendInteriorPlus interior s)
  have hden := boundaryPartitionJ_high_temp G beta J interior
  have hden' : boundaryPartitionJ G beta J interior =
      (2 : ℝ) ^ interior.card *
        (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          inhomogeneousBoundaryParityPartition G beta J interior := by
    simpa only [inhomogeneousBoundaryParityPartition, mul_assoc] using hden
  rw [hnum, boundaryPartitionJ_inhomogeneousDeleted_highTemp
    G beta J interior F hF, hden']
  have htwo : (2 : ℝ) ^ interior.card ≠ 0 := by positivity
  have houtside : (∏ e ∈ G.edgeFinset \ F,
      Real.cosh (beta * J e)) ≠ 0 := by positivity
  have hinside : (∏ e ∈ F, Real.cosh (beta * J e)) ≠ 0 := by positivity
  have hpart : inhomogeneousBoundaryParityPartition G beta J interior ≠ 0 := by
    intro hz
    have hpos : 0 < boundaryPartitionJ G beta J interior := by
      unfold boundaryPartitionJ
      exact Finset.sum_pos
        (fun s _ ↦ boltzmannJ_pos G beta J (extendInteriorPlus interior s))
        Finset.univ_nonempty
    rw [hden', hz, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hprod :
      (∏ e ∈ G.edgeFinset \ F, Real.cosh (beta * J e)) *
          ∏ e ∈ F, Real.cosh (beta * J e) =
        ∏ e ∈ G.edgeFinset, Real.cosh (beta * J e) :=
    Finset.prod_sdiff hF
  field_simp
  rw [← hprod]
  ring

theorem boundaryCurrentMeasure_parityAvoid_inhomogeneous
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (interior : Finset V)
    (F : Finset (Sym2 V)) :
    (boundaryCurrentPMF G beta J hbeta.le hJ interior).toMeasure
        {m | Disjoint (currentParitySupport G m) F} =
      ENNReal.ofReal
        (inhomogeneousBoundaryParityAvoidSum G beta J interior F /
          inhomogeneousBoundaryParityPartition G beta J interior) := by
  calc
    (boundaryCurrentPMF G beta J hbeta.le hJ interior).toMeasure
        {m | Disjoint (currentParitySupport G m) F} =
      (boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior).toMeasure
        {H | Disjoint H F} := by
      rw [boundaryNonnegativeParityPMF, PMF.toMeasure_map_apply]
      · rfl
      · exact Measurable.of_discrete
      · exact MeasurableSet.of_discrete
    _ = _ := boundaryNonnegativeParityMeasure_avoid
      G beta hbeta J hJ interior F

end StatMech.FrontierB
