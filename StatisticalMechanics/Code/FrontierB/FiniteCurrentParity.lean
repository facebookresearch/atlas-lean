/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.InfiniteCurrentMeasures
import Code.Sharpness.HighTempSources

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def freeParityPartition (beta : ℝ) : ℝ :=
  ∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
    Real.tanh beta ^ H.card

noncomputable def freeParityAvoidSum (beta : ℝ) (F : Finset (Sym2 V)) : ℝ :=
  ∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
    if Disjoint H F then Real.tanh beta ^ H.card else 0

noncomputable def deletedEdgeCoupling (F : Finset (Sym2 V)) : Sym2 V → ℝ :=
  fun e => if e ∈ F then 0 else 1

noncomputable def edgeSpinSum (F : Finset (Sym2 V)) (s : ConfigSpace V) : ℝ :=
  ∑ e ∈ F, bond s e

theorem tanh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.2 hx) (Real.cosh_pos x).le

noncomputable instance instMeasurableSpaceCurrentParityFinset :
    MeasurableSpace (Finset (Sym2 V)) := ⊤

noncomputable def freeParityRawMass (beta : ℝ)
    (H : Finset (Sym2 V)) : ℝ≥0∞ :=
  ENNReal.ofReal
    (if H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
      Real.tanh beta ^ H.card else 0)

noncomputable def freeParityPMF (beta : ℝ) (_hbeta : 0 ≤ beta) :
    PMF (Finset (Sym2 V)) :=
  PMF.normalize (freeParityRawMass G beta)
    (by
      rw [tsum_fintype]
      have hone : freeParityRawMass G beta ∅ = 1 := by
        simp [freeParityRawMass, IsEvenSubgraph, incCount]
      intro hzero
      have hle : freeParityRawMass G beta ∅ ≤
          ∑ H : Finset (Sym2 V), freeParityRawMass G beta H :=
        Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ ∅)
      rw [hzero, hone] at hle
      exact one_ne_zero (bot_unique hle))
    (by
      rw [tsum_fintype]
      exact ENNReal.sum_ne_top.2 fun H _ => ENNReal.ofReal_ne_top)

noncomputable def freeParityMeasure (beta : ℝ) (hbeta : 0 ≤ beta) :
    ProbabilityMeasure (Finset (Sym2 V)) :=
  ⟨(freeParityPMF G beta hbeta).toMeasure, inferInstance⟩

theorem tsum_freeParityRawMass (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∑' H : Finset (Sym2 V), freeParityRawMass G beta H =
      ENNReal.ofReal (freeParityPartition G beta) := by
  rw [tsum_fintype]
  unfold freeParityRawMass freeParityPartition
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · apply congrArg ENNReal.ofReal
    rw [Finset.sum_filter]
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
    · intro H hgap
      have hnot : H ∉ G.edgeFinset.powerset := (Finset.mem_sdiff.1 hgap).2
      have hsub : ¬ H ⊆ G.edgeFinset := by simpa using hnot
      simp [hsub]
    · intro H hpow
      have hsub : H ⊆ G.edgeFinset := Finset.mem_powerset.1 hpow
      by_cases heven : IsEvenSubgraph H <;> simp [hsub, heven]
  · intro H hH
    split
    · exact pow_nonneg (tanh_nonneg_of_nonneg hbeta) _
    · exact le_rfl

theorem freeParityPMF_apply (beta : ℝ) (hbeta : 0 ≤ beta)
    (H : Finset (Sym2 V)) :
    freeParityPMF G beta hbeta H =
      freeParityRawMass G beta H *
        (ENNReal.ofReal (freeParityPartition G beta))⁻¹ := by
  rw [freeParityPMF, PMF.normalize_apply, tsum_freeParityRawMass G beta hbeta]

theorem freeParityPartition_pos (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < freeParityPartition G beta := by
  unfold freeParityPartition
  have hempty : (∅ : Finset (Sym2 V)) ∈
      G.edgeFinset.powerset.filter IsEvenSubgraph := by
    simp [IsEvenSubgraph, incCount]
  have hnonneg : ∀ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
      0 ≤ Real.tanh beta ^ H.card := fun H _ =>
    pow_nonneg (tanh_nonneg_of_nonneg hbeta) _
  exact lt_of_lt_of_le Real.zero_lt_one (by
    simpa using Finset.single_le_sum hnonneg hempty)

theorem freeParityMeasure_avoid (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 V)) :
    (freeParityMeasure G beta hbeta : Measure (Finset (Sym2 V)))
        {H | Disjoint H F} =
      ENNReal.ofReal
        (freeParityAvoidSum G beta F / freeParityPartition G beta) := by
  change (freeParityPMF G beta hbeta).toMeasure {H | Disjoint H F} = _
  rw [PMF.toMeasure_apply_eq_tsum, tsum_fintype]
  rw [ENNReal.ofReal_div_of_pos (freeParityPartition_pos G beta hbeta)]
  let r : Finset (Sym2 V) → ℝ := fun H =>
    if H ⊆ G.edgeFinset ∧ IsEvenSubgraph H ∧ Disjoint H F then
      Real.tanh beta ^ H.card else 0
  have hrnonneg : ∀ H, 0 ≤ r H := by
    intro H
    simp only [r]
    split
    · exact pow_nonneg (tanh_nonneg_of_nonneg hbeta) _
    · exact le_rfl
  have hrsum : (∑ H : Finset (Sym2 V), r H) =
      freeParityAvoidSum G beta F := by
    unfold freeParityAvoidSum
    rw [Finset.sum_filter]
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
    · intro H hgap
      have hnot : H ∉ G.edgeFinset.powerset := (Finset.mem_sdiff.1 hgap).2
      have hsub : ¬ H ⊆ G.edgeFinset := by simpa using hnot
      simp [r, hsub]
    · intro H hpow
      have hsub : H ⊆ G.edgeFinset := Finset.mem_powerset.1 hpow
      by_cases heven : IsEvenSubgraph H <;>
        by_cases hd : Disjoint H F <;> simp [r, hsub, heven, hd]
  have hnum : (∑ H : Finset (Sym2 V),
      if Disjoint H F then freeParityRawMass G beta H else 0) =
      ENNReal.ofReal (freeParityAvoidSum G beta F) := by
    rw [← hrsum]
    have hof := ENNReal.ofReal_sum_of_nonneg
      (s := (Finset.univ : Finset (Finset (Sym2 V))))
      (fun H _ => hrnonneg H)
    rw [hof]
    apply Finset.sum_congr rfl
    intro H hH
    by_cases hd : Disjoint H F <;>
      by_cases hsub : H ⊆ G.edgeFinset <;>
        by_cases heven : IsEvenSubgraph H <;>
          simp [freeParityRawMass, r, hd, hsub, heven]
  calc
    (∑ H : Finset (Sym2 V),
        {H | Disjoint H F}.indicator (freeParityPMF G beta hbeta) H) =
        ∑ H : Finset (Sym2 V),
          (if Disjoint H F then freeParityRawMass G beta H else 0) *
            (ENNReal.ofReal (freeParityPartition G beta))⁻¹ := by
      apply Finset.sum_congr rfl
      intro H hH
      by_cases hd : Disjoint H F
      · rw [Set.indicator_of_mem hd, freeParityPMF_apply]
        simp [hd]
      · rw [Set.indicator_of_notMem hd]
        simp [hd]
    _ = (∑ H : Finset (Sym2 V),
        if Disjoint H F then freeParityRawMass G beta H else 0) *
          (ENNReal.ofReal (freeParityPartition G beta))⁻¹ := by
      rw [Finset.sum_mul]
    _ = ENNReal.ofReal (freeParityAvoidSum G beta F) *
          (ENNReal.ofReal (freeParityPartition G beta))⁻¹ := by rw [hnum]

theorem boltzmannJ_mul_exp_neg_edgeSpinSum
    (beta : ℝ) (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset)
    (s : ConfigSpace V) :
    boltzmannJ G beta (fun _ => 1) s *
        Real.exp (-beta * edgeSpinSum F s) =
      boltzmannJ G beta (deletedEdgeCoupling F) s := by
  unfold boltzmannJ edgeSpinSum deletedEdgeCoupling
  rw [← Real.exp_add]
  congr 1
  have hsplit :
      (∑ e ∈ G.edgeFinset \ F, bond s e) +
        ∑ e ∈ F, bond s e = ∑ e ∈ G.edgeFinset, bond s e :=
    Finset.sum_sdiff hF
  rw [show (∑ e ∈ G.edgeFinset, (1 : ℝ) * bond s e) =
      ∑ e ∈ G.edgeFinset, bond s e by simp]
  rw [show (∑ e ∈ G.edgeFinset,
      (if e ∈ F then 0 else 1) * bond s e) =
      ∑ e ∈ G.edgeFinset \ F, bond s e by
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.sdiff_subset)
    · intro e heGap
      have heE : e ∈ G.edgeFinset := (Finset.mem_sdiff.1 heGap).1
      have heNot : e ∉ G.edgeFinset \ F := (Finset.mem_sdiff.1 heGap).2
      have heF : e ∈ F := by
        by_contra hef
        exact heNot (Finset.mem_sdiff.2 ⟨heE, hef⟩)
      simp [heF]
    · intro e heDiff
      have heF : e ∉ F := (Finset.mem_sdiff.1 heDiff).2
      simp [heF]]
  rw [← hsplit]
  ring

theorem deletedEdgeCoupling_cosh_prod
    (beta : ℝ) (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    (∏ e ∈ G.edgeFinset,
      Real.cosh (beta * deletedEdgeCoupling F e)) =
      Real.cosh beta ^ (G.edgeFinset.card - F.card) := by
  calc
    (∏ e ∈ G.edgeFinset,
        Real.cosh (beta * deletedEdgeCoupling F e)) =
        ∏ e ∈ G.edgeFinset \ F,
          Real.cosh (beta * deletedEdgeCoupling F e) := by
      symm
      apply Finset.prod_subset (Finset.sdiff_subset)
      intro e heE heNot
      have heF : e ∈ F := by
        by_contra hef
        exact heNot (Finset.mem_sdiff.2 ⟨heE, hef⟩)
      simp [deletedEdgeCoupling, heF]
    _ = ∏ _e ∈ G.edgeFinset \ F, Real.cosh beta := by
      apply Finset.prod_congr rfl
      intro e heDiff
      have heF : e ∉ F := (Finset.mem_sdiff.1 heDiff).2
      simp [deletedEdgeCoupling, heF]
    _ = Real.cosh beta ^ (G.edgeFinset.card - F.card) := by
      rw [Finset.prod_const, Finset.card_sdiff_of_subset hF]

theorem deletedEdgeCoupling_highTemp_sum
    (beta : ℝ) (F : Finset (Sym2 V)) :
    (∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
      highTempSubgraphWeight beta (deletedEdgeCoupling F) H) =
      freeParityAvoidSum G beta F := by
  unfold freeParityAvoidSum
  apply Finset.sum_congr rfl
  intro H hH
  rw [Finset.mem_filter] at hH
  by_cases hd : Disjoint H F
  · rw [if_pos hd]
    unfold highTempSubgraphWeight
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro e heH
    have heF : e ∉ F := fun hef => Finset.disjoint_left.1 hd heH hef
    simp [deletedEdgeCoupling, heF]
  · rw [if_neg hd]
    unfold highTempSubgraphWeight
    have hinter : (H ∩ F).Nonempty := by
      rw [Finset.not_disjoint_iff_nonempty_inter] at hd
      exact hd
    obtain ⟨e, he⟩ := hinter
    have heH : e ∈ H := (Finset.mem_inter.1 he).1
    have heF : e ∈ F := (Finset.mem_inter.1 he).2
    apply Finset.prod_eq_zero heH
    simp [deletedEdgeCoupling, heF]

theorem partitionJ_unit_highTemp
    (beta : ℝ) :
    partitionJ G beta (fun _ => 1) =
      (2 : ℝ) ^ Fintype.card V *
        Real.cosh beta ^ G.edgeFinset.card * freeParityPartition G beta := by
  have h := spinProd_boltzmannJ_high_temp_expansion
    G beta (fun _ => 1) (∅ : Finset V)
  simp only [spinProd_empty, one_mul] at h
  rw [show (∏ e ∈ G.edgeFinset, Real.cosh (beta * (fun _ => (1 : ℝ)) e)) =
      Real.cosh beta ^ G.edgeFinset.card by simp] at h
  simp only [hasOddBoundary_empty, highTempSubgraphWeight] at h
  have hweight : ∀ H : Finset (Sym2 V),
      (∏ e ∈ H, Real.tanh (beta * (fun _ => (1 : ℝ)) e)) =
        Real.tanh beta ^ H.card := by simp
  simp_rw [hweight] at h
  exact h

theorem partitionJ_deleted_highTemp
    (beta : ℝ) (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    partitionJ G beta (deletedEdgeCoupling F) =
      (2 : ℝ) ^ Fintype.card V *
        Real.cosh beta ^ (G.edgeFinset.card - F.card) *
          freeParityAvoidSum G beta F := by
  have h := spinProd_boltzmannJ_high_temp_expansion
    G beta (deletedEdgeCoupling F) (∅ : Finset V)
  simp only [spinProd_empty, one_mul, hasOddBoundary_empty] at h
  rw [deletedEdgeCoupling_cosh_prod G beta F hF,
    deletedEdgeCoupling_highTemp_sum G beta F] at h
  exact h

theorem freeParityAvoidRatio_eq_spinExpectation
    (beta : ℝ) (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    freeParityAvoidSum G beta F / freeParityPartition G beta =
      (∑ s : ConfigSpace V,
        boltzmannJ G beta (fun _ => 1) s *
          Real.exp (-beta * edgeSpinSum F s)) /
          partitionJ G beta (fun _ => 1) *
        Real.cosh beta ^ F.card := by
  have hnum : (∑ s : ConfigSpace V,
        boltzmannJ G beta (fun _ => 1) s *
          Real.exp (-beta * edgeSpinSum F s)) =
      partitionJ G beta (deletedEdgeCoupling F) := by
    unfold partitionJ
    apply Finset.sum_congr rfl
    intro s hs
    exact boltzmannJ_mul_exp_neg_edgeSpinSum G beta F hF s
  rw [hnum, partitionJ_unit_highTemp, partitionJ_deleted_highTemp G beta F hF]
  have htwo : (2 : ℝ) ^ Fintype.card V ≠ 0 := by positivity
  have hcosh : Real.cosh beta ≠ 0 := ne_of_gt (Real.cosh_pos beta)
  have hcard : G.edgeFinset.card - F.card + F.card = G.edgeFinset.card := by
    rw [Nat.sub_add_cancel (Finset.card_le_card hF)]
  have hZ : freeParityPartition G beta ≠ 0 := by
    have hpart := partitionJ_pos G beta (fun _ => 1)
    rw [partitionJ_unit_highTemp] at hpart
    have hfac : 0 < (2 : ℝ) ^ Fintype.card V *
        Real.cosh beta ^ G.edgeFinset.card := by positivity
    exact ne_of_gt (pos_of_mul_pos_right hpart hfac.le)
  field_simp
  calc
    freeParityAvoidSum G beta F * Real.cosh beta ^ G.edgeFinset.card =
        freeParityAvoidSum G beta F *
          Real.cosh beta ^ (G.edgeFinset.card - F.card + F.card) := by rw [hcard]
    _ = freeParityAvoidSum G beta F *
          (Real.cosh beta ^ (G.edgeFinset.card - F.card) *
            Real.cosh beta ^ F.card) := by rw [pow_add]
    _ = freeParityAvoidSum G beta F *
        Real.cosh beta ^ (G.edgeFinset.card - F.card) *
          Real.cosh beta ^ F.card := by ring

theorem freeParityMeasure_avoid_eq_spinExpectation
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    (freeParityMeasure G beta hbeta : Measure (Finset (Sym2 V)))
        {H | Disjoint H F} =
      ENNReal.ofReal
        (((∑ s : ConfigSpace V,
            boltzmannJ G beta (fun _ => 1) s *
              Real.exp (-beta * edgeSpinSum F s)) /
            partitionJ G beta (fun _ => 1)) *
          Real.cosh beta ^ F.card) := by
  rw [freeParityMeasure_avoid]
  exact congrArg ENNReal.ofReal
    (freeParityAvoidRatio_eq_spinExpectation G beta F hF)

end StatMech.FrontierB

