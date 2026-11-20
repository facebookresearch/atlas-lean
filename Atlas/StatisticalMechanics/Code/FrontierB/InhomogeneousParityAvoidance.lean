/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.NonnegativeCurrentConditionalPMF
import Code.FrontierB.FreeBoxEvenLimit










open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def inhomogeneousParityPartition
    (beta : ℝ) (J : Sym2 V → ℝ) : ℝ :=
  ∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
    highTempSubgraphWeight beta J H

noncomputable def inhomogeneousParityAvoidSum
    (beta : ℝ) (J : Sym2 V → ℝ) (F : Finset (Sym2 V)) : ℝ :=
  ∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
    if Disjoint H F then highTempSubgraphWeight beta J H else 0

private theorem sinh_eq_cosh_mul_tanh (x : ℝ) :
    Real.sinh x = Real.cosh x * Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem inhomogeneousParityFiberMass_eq_cosh_mul_highTemp
    (beta : ℝ) (J : Sym2 V → ℝ)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    inhomogeneousParityFiberMass G (fun e => beta * J e) H =
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        highTempSubgraphWeight beta J H := by
  unfold inhomogeneousParityFiberMass highTempSubgraphWeight
  rw [Finset.prod_ite]
  have hprod_mem (f : Sym2 V → ℝ) :
      (∏ x : G.edgeFinset with x.1 ∈ H, f x.1) = ∏ e ∈ H, f e := by
    symm
    apply Finset.prod_bij (fun e he => ⟨e, hH he⟩)
    · intro e he
      simp [he]
    · intro e₁ h₁ e₂ h₂ heq
      exact congrArg Subtype.val heq
    · intro x hx
      refine ⟨x.1, ?_, ?_⟩
      · simpa using hx
      · apply Subtype.ext
        rfl
    · simp
  have hprod_not (f : Sym2 V → ℝ) :
      (∏ x : G.edgeFinset with x.1 ∉ H, f x.1) =
        ∏ e ∈ G.edgeFinset \ H, f e := by
    symm
    apply Finset.prod_bij (fun e he => ⟨e, (Finset.mem_sdiff.mp he).1⟩)
    · intro e he
      simp [(Finset.mem_sdiff.mp he).2]
    · intro e₁ h₁ e₂ h₂ heq
      exact congrArg Subtype.val heq
    · intro x hx
      refine ⟨x.1, ?_, ?_⟩
      · exact Finset.mem_sdiff.mpr ⟨x.2, by simpa using hx⟩
      · apply Subtype.ext
        rfl
    · simp
  rw [show (∏ x : G.edgeFinset with x.1 ∈ H,
      Real.sinh ((fun e => beta * J e) x.1)) =
        ∏ e ∈ H, Real.sinh (beta * J e) from
      hprod_mem (fun e => Real.sinh (beta * J e))]
  rw [show (∏ x : G.edgeFinset with x.1 ∉ H,
      Real.cosh ((fun e => beta * J e) x.1)) =
        ∏ e ∈ G.edgeFinset \ H, Real.cosh (beta * J e) from
      hprod_not (fun e => Real.cosh (beta * J e))]
  simp_rw [sinh_eq_cosh_mul_tanh]
  rw [Finset.prod_mul_distrib]
  calc
    (∏ e ∈ H, Real.cosh (beta * J e)) *
          (∏ e ∈ H, Real.tanh (beta * J e)) *
          ∏ e ∈ G.edgeFinset \ H, Real.cosh (beta * J e) =
        ((∏ e ∈ G.edgeFinset \ H, Real.cosh (beta * J e)) *
          ∏ e ∈ H, Real.cosh (beta * J e)) *
            ∏ e ∈ H, Real.tanh (beta * J e) := by ring
    _ = _ := by rw [Finset.prod_sdiff hH]

theorem partitionJ_eq_cosh_mul_inhomogeneousParityPartition
    (beta : ℝ) (J : Sym2 V → ℝ) :
    partitionJ G beta J =
      (2 : ℝ) ^ Fintype.card V *
        (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          inhomogeneousParityPartition G beta J := by
  unfold partitionJ inhomogeneousParityPartition
  rw [show (∑ s : ConfigSpace V, boltzmannJ G beta J s) =
      ∑ s : ConfigSpace V, spinProd (∅ : Finset V) s *
        boltzmannJ G beta J s by simp]
  rw [spinProd_boltzmannJ_high_temp_expansion G beta J ∅]
  simp only [hasOddBoundary_empty]

theorem currentSum_eq_cosh_mul_inhomogeneousParityPartition
    (beta : ℝ) (J : Sym2 V → ℝ) :
    currentSum G beta J ∅ =
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        inhomogeneousParityPartition G beta J := by
  have h := partitionJ_eq_currentSum G beta J
  rw [partitionJ_eq_cosh_mul_inhomogeneousParityPartition] at h
  rw [mul_assoc] at h
  have htwo : (2 : ℝ) ^ Fintype.card V ≠ 0 := by positivity
  exact (mul_left_cancel₀ htwo h).symm

theorem inhomogeneousParityPartition_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) :
    0 < inhomogeneousParityPartition G beta J := by
  unfold inhomogeneousParityPartition
  have hempty : (∅ : Finset (Sym2 V)) ∈
      G.edgeFinset.powerset.filter IsEvenSubgraph := by
    simp [IsEvenSubgraph, incCount]
  have hnonneg : ∀ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
      0 ≤ highTempSubgraphWeight beta J H := by
    intro H hH
    unfold highTempSubgraphWeight
    exact Finset.prod_nonneg fun e he =>
      tanh_nonneg_of_nonneg (mul_nonneg hbeta (hJ e))
  exact lt_of_lt_of_le Real.zero_lt_one (by
    simpa [highTempSubgraphWeight] using
      Finset.single_le_sum hnonneg hempty)

theorem sourcelessNonnegativeParityPMF_apply_eq_highTemp
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (H : Finset (Sym2 V)) :
    sourcelessNonnegativeParityPMF G beta J hbeta.le hJ H =
      if hvalid : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
        ENNReal.ofReal (highTempSubgraphWeight beta J H) *
          (ENNReal.ofReal (inhomogeneousParityPartition G beta J))⁻¹
      else 0 := by
  rw [sourcelessNonnegativeParityPMF_apply G beta hbeta J hJ H]
  by_cases hvalid : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H
  · rw [dif_pos hvalid, dif_pos hvalid,
      inhomogeneousParityFiberMass_eq_cosh_mul_highTemp G beta J H hvalid.1,
      currentSum_eq_cosh_mul_inhomogeneousParityPartition G beta J]
    let c : ℝ≥0∞ := ENNReal.ofReal
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e))
    let t : ℝ≥0∞ := ENNReal.ofReal (highTempSubgraphWeight beta J H)
    let p : ℝ≥0∞ := ENNReal.ofReal
      (inhomogeneousParityPartition G beta J)
    have hcReal : 0 ≤ ∏ e ∈ G.edgeFinset,
        Real.cosh (beta * J e) := Finset.prod_nonneg fun e _ =>
      (Real.cosh_pos _).le
    have htReal : 0 ≤ highTempSubgraphWeight beta J H := by
      unfold highTempSubgraphWeight
      exact Finset.prod_nonneg fun e _ =>
        tanh_nonneg_of_nonneg (mul_nonneg hbeta.le (hJ e))
    rw [ENNReal.ofReal_mul hcReal, ENNReal.ofReal_mul hcReal]
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
    change c * t * (c * p)⁻¹ = t * p⁻¹
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hcTop)]
    calc
      c * t * (c⁻¹ * p⁻¹) = (c * c⁻¹) * (t * p⁻¹) := by
        ac_rfl
      _ = t * p⁻¹ := by rw [ENNReal.mul_inv_cancel hc0 hcTop, one_mul]
  · rw [dif_neg hvalid, dif_neg hvalid]

theorem sourcelessNonnegativeParityMeasure_avoid
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (F : Finset (Sym2 V)) :
    (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ).toMeasure
        {H | Disjoint H F} =
      ENNReal.ofReal
        (inhomogeneousParityAvoidSum G beta J F /
          inhomogeneousParityPartition G beta J) := by
  classical
  rw [PMF.toMeasure_apply_eq_tsum, tsum_fintype,
    ENNReal.ofReal_div_of_pos
      (inhomogeneousParityPartition_pos G beta hbeta.le J hJ)]
  let p := ENNReal.ofReal (inhomogeneousParityPartition G beta J)
  let r : Finset (Sym2 V) → ℝ := fun H =>
    if H ⊆ G.edgeFinset ∧ IsEvenSubgraph H ∧ Disjoint H F then
      highTempSubgraphWeight beta J H else 0
  have hrnonneg : ∀ H, 0 ≤ r H := by
    intro H
    simp only [r]
    split
    · unfold highTempSubgraphWeight
      exact Finset.prod_nonneg fun e _ =>
        tanh_nonneg_of_nonneg (mul_nonneg hbeta.le (hJ e))
    · exact le_rfl
  have hrsum : (∑ H : Finset (Sym2 V), r H) =
      inhomogeneousParityAvoidSum G beta J F := by
    unfold inhomogeneousParityAvoidSum
    rw [Finset.sum_filter]
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
    · intro H hgap
      have hnot : H ∉ G.edgeFinset.powerset := (Finset.mem_sdiff.mp hgap).2
      have hsub : ¬H ⊆ G.edgeFinset := by simpa using hnot
      simp [r, hsub]
    · intro H hpow
      have hsub : H ⊆ G.edgeFinset := Finset.mem_powerset.mp hpow
      by_cases heven : IsEvenSubgraph H <;>
        by_cases hd : Disjoint H F <;> simp [r, hsub, heven, hd]
  have hnum :
      (∑ H : Finset (Sym2 V),
        if Disjoint H F ∧ H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
          ENNReal.ofReal (highTempSubgraphWeight beta J H) else 0) =
        ENNReal.ofReal (inhomogeneousParityAvoidSum G beta J F) := by
    rw [← hrsum, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro H hH
      by_cases hs : H ⊆ G.edgeFinset <;>
        by_cases he : IsEvenSubgraph H <;>
          by_cases hd : Disjoint H F <;> simp [r, hs, he, hd]
    · intro H hH
      exact hrnonneg H
  calc
    (∑ H : Finset (Sym2 V),
        {H | Disjoint H F}.indicator
          (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ) H) =
      ∑ H : Finset (Sym2 V),
        (if Disjoint H F ∧ H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
          ENNReal.ofReal (highTempSubgraphWeight beta J H) else 0) * p⁻¹ := by
      apply Finset.sum_congr rfl
      intro H hH
      by_cases hd : Disjoint H F
      · rw [Set.indicator_of_mem hd,
          sourcelessNonnegativeParityPMF_apply_eq_highTemp
            G beta hbeta J hJ H]
        by_cases hv : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H
        · simp [hd, hv, p]
        · simp [hd, hv]
      · rw [Set.indicator_of_notMem hd]
        simp [hd]
    _ = (∑ H : Finset (Sym2 V),
        if Disjoint H F ∧ H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
          ENNReal.ofReal (highTempSubgraphWeight beta J H) else 0) * p⁻¹ := by
      rw [Finset.sum_mul]
    _ = ENNReal.ofReal (inhomogeneousParityAvoidSum G beta J F) * p⁻¹ := by
      rw [hnum]


noncomputable def inhomogeneousDeletedCoupling
    (J : Sym2 V → ℝ) (F : Finset (Sym2 V)) : Sym2 V → ℝ :=
  fun e => if e ∈ F then 0 else J e

noncomputable def weightedEdgeSpinSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (s : ConfigSpace V) : ℝ :=
  ∑ e ∈ F, beta * J e * bond s e

theorem boltzmannJ_mul_exp_neg_weightedEdgeSpinSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset)
    (s : ConfigSpace V) :
    boltzmannJ G beta J s *
        Real.exp (-weightedEdgeSpinSum beta J F s) =
      boltzmannJ G beta (inhomogeneousDeletedCoupling J F) s := by
  unfold boltzmannJ weightedEdgeSpinSum inhomogeneousDeletedCoupling
  rw [← Real.exp_add]
  congr 1
  have hsplit :
      (∑ e ∈ G.edgeFinset \ F, J e * bond s e) +
          ∑ e ∈ F, J e * bond s e =
        ∑ e ∈ G.edgeFinset, J e * bond s e :=
    Finset.sum_sdiff hF
  have hdeleted :
      (∑ e ∈ G.edgeFinset,
        (if e ∈ F then 0 else J e) * bond s e) =
        ∑ e ∈ G.edgeFinset \ F, J e * bond s e := by
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.sdiff_subset)
    · intro e heGap
      have heE : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp heGap).1
      have heNot : e ∉ G.edgeFinset \ F := (Finset.mem_sdiff.mp heGap).2
      have heF : e ∈ F := by
        by_contra hef
        exact heNot (Finset.mem_sdiff.mpr ⟨heE, hef⟩)
      simp [heF]
    · intro e heDiff
      have heF : e ∉ F := (Finset.mem_sdiff.mp heDiff).2
      simp [heF]
  rw [hdeleted, ← hsplit, Finset.mul_sum]
  have hmul (S : Finset (Sym2 V)) :
      (∑ e ∈ S, beta * J e * bond s e) =
        beta * ∑ e ∈ S, J e * bond s e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [hmul F]
  have hdiff :
      (∑ e ∈ G.edgeFinset \ F, beta * (J e * bond s e)) =
        beta * ∑ e ∈ G.edgeFinset \ F, J e * bond s e := by
    symm
    rw [Finset.mul_sum]
  rw [hdiff]
  ring

theorem inhomogeneousDeletedCoupling_cosh_prod
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    (∏ e ∈ G.edgeFinset,
      Real.cosh (beta * inhomogeneousDeletedCoupling J F e)) =
      ∏ e ∈ G.edgeFinset \ F, Real.cosh (beta * J e) := by
  calc
    (∏ e ∈ G.edgeFinset,
        Real.cosh (beta * inhomogeneousDeletedCoupling J F e)) =
      ∏ e ∈ G.edgeFinset \ F,
        Real.cosh (beta * inhomogeneousDeletedCoupling J F e) := by
      symm
      apply Finset.prod_subset (Finset.sdiff_subset)
      intro e heE heNot
      have heF : e ∈ F := by
        by_contra hef
        exact heNot (Finset.mem_sdiff.mpr ⟨heE, hef⟩)
      simp [inhomogeneousDeletedCoupling, heF]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro e heDiff
      have heF : e ∉ F := (Finset.mem_sdiff.mp heDiff).2
      simp [inhomogeneousDeletedCoupling, heF]

theorem inhomogeneousDeletedCoupling_highTemp_sum
    (beta : ℝ) (J : Sym2 V → ℝ) (F : Finset (Sym2 V)) :
    (∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
      highTempSubgraphWeight beta (inhomogeneousDeletedCoupling J F) H) =
      inhomogeneousParityAvoidSum G beta J F := by
  unfold inhomogeneousParityAvoidSum
  apply Finset.sum_congr rfl
  intro H hH
  by_cases hd : Disjoint H F
  · rw [if_pos hd]
    unfold highTempSubgraphWeight
    apply Finset.prod_congr rfl
    intro e heH
    have heF : e ∉ F := fun hef => Finset.disjoint_left.mp hd heH hef
    simp [inhomogeneousDeletedCoupling, heF]
  · rw [if_neg hd]
    unfold highTempSubgraphWeight
    have hinter : (H ∩ F).Nonempty := by
      rw [Finset.not_disjoint_iff_nonempty_inter] at hd
      exact hd
    obtain ⟨e, he⟩ := hinter
    have heH : e ∈ H := (Finset.mem_inter.mp he).1
    have heF : e ∈ F := (Finset.mem_inter.mp he).2
    apply Finset.prod_eq_zero heH
    simp [inhomogeneousDeletedCoupling, heF]

theorem partitionJ_inhomogeneousDeleted_highTemp
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    partitionJ G beta (inhomogeneousDeletedCoupling J F) =
      (2 : ℝ) ^ Fintype.card V *
        (∏ e ∈ G.edgeFinset \ F, Real.cosh (beta * J e)) *
          inhomogeneousParityAvoidSum G beta J F := by
  rw [partitionJ_eq_cosh_mul_inhomogeneousParityPartition,
    inhomogeneousDeletedCoupling_cosh_prod G beta J F hF]
  congr 1
  exact inhomogeneousDeletedCoupling_highTemp_sum G beta J F



theorem inhomogeneousParityAvoidRatio_eq_spinExpectation
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    inhomogeneousParityAvoidSum G beta J F /
        inhomogeneousParityPartition G beta J =
      ((∑ s : ConfigSpace V,
          boltzmannJ G beta J s *
            Real.exp (-weightedEdgeSpinSum beta J F s)) /
        partitionJ G beta J) *
          ∏ e ∈ F, Real.cosh (beta * J e) := by
  have hnum :
      (∑ s : ConfigSpace V,
          boltzmannJ G beta J s *
            Real.exp (-weightedEdgeSpinSum beta J F s)) =
        partitionJ G beta (inhomogeneousDeletedCoupling J F) := by
    unfold partitionJ
    apply Finset.sum_congr rfl
    intro s hs
    exact boltzmannJ_mul_exp_neg_weightedEdgeSpinSum
      G beta J F hF s
  rw [hnum, partitionJ_inhomogeneousDeleted_highTemp G beta J F hF,
    partitionJ_eq_cosh_mul_inhomogeneousParityPartition]
  have htwo : (2 : ℝ) ^ Fintype.card V ≠ 0 := by positivity
  have houtside : (∏ e ∈ G.edgeFinset \ F,
      Real.cosh (beta * J e)) ≠ 0 := by positivity
  have hinside : (∏ e ∈ F, Real.cosh (beta * J e)) ≠ 0 := by
    positivity
  have hpart : inhomogeneousParityPartition G beta J ≠ 0 := by
    intro hz
    have hEq := partitionJ_eq_cosh_mul_inhomogeneousParityPartition G beta J
    rw [hz, mul_zero] at hEq
    exact (ne_of_gt (partitionJ_pos G beta J)) hEq
  have hprod :
      (∏ e ∈ G.edgeFinset \ F, Real.cosh (beta * J e)) *
          ∏ e ∈ F, Real.cosh (beta * J e) =
        ∏ e ∈ G.edgeFinset, Real.cosh (beta * J e) :=
    Finset.prod_sdiff hF
  field_simp
  rw [← hprod]
  ring

theorem inhomogeneousParityAvoidRatio_eq_expJ
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    inhomogeneousParityAvoidSum G beta J F /
        inhomogeneousParityPartition G beta J =
      expJ G.edgeFinset (fun e => beta * J e) (fun _ => 0)
          (fun s => Real.exp (-weightedEdgeSpinSum beta J F s)) *
        ∏ e ∈ F, Real.cosh (beta * J e) := by
  rw [inhomogeneousParityAvoidRatio_eq_spinExpectation G beta J F hF]
  congr 1
  unfold expJ ZJ wJ partitionJ boltzmannJ
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  have hexp (s : ConfigSpace V) :
      beta * (∑ e ∈ G.edgeFinset, J e * bond s e) =
        ∑ e ∈ G.edgeFinset, beta * J e * bond s e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  simp_rw [hexp]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  ring



theorem sourcelessCurrentMeasure_parityAvoid_inhomogeneous
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (F : Finset (Sym2 V)) :
    (sourcelessCurrentPMF G beta J hbeta.le hJ).toMeasure
        {m | Disjoint (currentParitySupport G m) F} =
      ENNReal.ofReal
        (inhomogeneousParityAvoidSum G beta J F /
          inhomogeneousParityPartition G beta J) := by
  calc
    (sourcelessCurrentPMF G beta J hbeta.le hJ).toMeasure
        {m | Disjoint (currentParitySupport G m) F} =
      (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ).toMeasure
        {H | Disjoint H F} := by
      rw [sourcelessNonnegativeParityPMF, PMF.toMeasure_map_apply]
      · rfl
      · exact Measurable.of_discrete
      · exact MeasurableSet.of_discrete
    _ = _ := sourcelessNonnegativeParityMeasure_avoid
      G beta hbeta J hJ F

noncomputable def weightedEdgeExpansionCoeff
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F T : Finset (Sym2 V)) : ℝ :=
  (∏ e ∈ T, Real.cosh (-(beta * J e))) *
    ∏ e ∈ F \ T, Real.sinh (-(beta * J e))

theorem exp_neg_weightedEdgeSpinSum_eq_spinProd_sum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬e.IsDiag)
    (s : ConfigSpace V) :
    Real.exp (-weightedEdgeSpinSum beta J F s) =
      ∑ T ∈ F.powerset,
        weightedEdgeExpansionCoeff beta J F T *
          spinProd (edgeBoundary (F \ T)) s := by
  unfold weightedEdgeSpinSum
  rw [show -(∑ e ∈ F, beta * J e * bond s e) =
      ∑ e ∈ F, -(beta * J e) * bond s e by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring]
  rw [Real.exp_sum]
  simp_rw [exp_mul_pm (-(beta * J _)) (bond s _) (bond_eq_pm s _)]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T hT
  unfold weightedEdgeExpansionCoeff
  rw [Finset.prod_mul_distrib,
    prod_bond_eq_spinProd_edgeBoundary (F \ T)]
  · ring
  · intro e he
    exact hF e (Finset.mem_sdiff.mp he).1



theorem expJ_exp_neg_weightedEdgeSpinSum
    (E : Finset (Sym2 V)) (K hfJ : Sym2 V → ℝ)
    (hf : V → ℝ) (beta : ℝ)
    (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬e.IsDiag) :
    expJ E K hf
        (fun s => Real.exp (-weightedEdgeSpinSum beta hfJ F s)) =
      ∑ T ∈ F.powerset,
        weightedEdgeExpansionCoeff beta hfJ F T *
          expJ E K hf (spinProd (edgeBoundary (F \ T))) := by
  unfold expJ
  have hnum :
      (∑ s : ConfigSpace V,
          Real.exp (-weightedEdgeSpinSum beta hfJ F s) * wJ E K hf s) =
        ∑ T ∈ F.powerset,
          weightedEdgeExpansionCoeff beta hfJ F T *
            ∑ s : ConfigSpace V,
              spinProd (edgeBoundary (F \ T)) s * wJ E K hf s := by
    simp_rw [exp_neg_weightedEdgeSpinSum_eq_spinProd_sum beta hfJ F hF]
    calc
      (∑ s : ConfigSpace V,
          (∑ T ∈ F.powerset,
            weightedEdgeExpansionCoeff beta hfJ F T *
              spinProd (edgeBoundary (F \ T)) s) * wJ E K hf s) =
        ∑ s : ConfigSpace V, ∑ T ∈ F.powerset,
          weightedEdgeExpansionCoeff beta hfJ F T *
            (spinProd (edgeBoundary (F \ T)) s * wJ E K hf s) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro T hT
          ring
      _ = ∑ T ∈ F.powerset, ∑ s : ConfigSpace V,
          weightedEdgeExpansionCoeff beta hfJ F T *
            (spinProd (edgeBoundary (F \ T)) s * wJ E K hf s) := by
          rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [← Finset.mul_sum]
  rw [hnum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T hT
  ring

end StatMech.FrontierB
