/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MannWhitneyAUC
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- Measurability of the Mann-Whitney kernel on the product space. -/
theorem mannWhitneyKernel_measurable :
    Measurable fun p : ℝ × ℝ =>
      (if p.2 < p.1 then (1 : ℝ) else if p.2 = p.1 then 1 / 2 else 0) := by
  refine Measurable.ite ?_ measurable_const
    (Measurable.ite ?_ measurable_const measurable_const)
  · exact measurableSet_lt measurable_snd measurable_fst
  · exact measurableSet_eq_fun measurable_snd measurable_fst

/-- The Mann-Whitney kernel is bounded by 1. -/
theorem mannWhitneyKernel_norm_le_one (p : ℝ × ℝ) :
    ‖(if p.2 < p.1 then (1 : ℝ) else if p.2 = p.1 then 1 / 2 else 0)‖ ≤ 1 := by
  split_ifs <;> norm_num

/-- Expected Mann-Whitney count for two independent i.i.d. samples. -/
theorem mannWhitneyU_mean {m n : ℕ}
    (μx μy : Measure ℝ) [IsProbabilityMeasure μx] [IsProbabilityMeasure μy]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Fin m ⊕ Fin n → Ω → ℝ}
    (hIndep : iIndepFun Z μ)
    (hX : ∀ i, HasLaw (Z (Sum.inl i)) μx μ)
    (hY : ∀ j, HasLaw (Z (Sum.inr j)) μy μ) :
    ∫ ω, mannWhitneyU (fun i => Z (Sum.inl i) ω) (fun j => Z (Sum.inr j) ω) ∂μ
      = (m * n : ℝ) * (∫ a, ∫ b,
        (if b < a then (1 : ℝ) else if b = a then 1 / 2 else 0) ∂μy ∂μx) := by
  have hpair_ae : ∀ i j, AEMeasurable (fun ω => (Z (Sum.inl i) ω, Z (Sum.inr j) ω)) μ :=
    fun i j => (hX i).aemeasurable.prodMk (hY j).aemeasurable
  have hinterm : ∀ i j, Integrable (fun ω =>
      (if Z (Sum.inr j) ω < Z (Sum.inl i) ω then (1 : ℝ)
        else if Z (Sum.inr j) ω = Z (Sum.inl i) ω then 1 / 2 else 0)) μ := by
    intro i j
    refine Integrable.of_bound ?_ 1 ?_
    · exact (mannWhitneyKernel_measurable.comp_aemeasurable
        (hpair_ae i j)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω =>
        mannWhitneyKernel_norm_le_one (Z (Sum.inl i) ω, Z (Sum.inr j) ω)
  have hterm : ∀ i j, (∫ ω,
      (if Z (Sum.inr j) ω < Z (Sum.inl i) ω then (1 : ℝ)
        else if Z (Sum.inr j) ω = Z (Sum.inl i) ω then 1 / 2 else 0) ∂μ)
      = ∫ a, ∫ b,
        (if b < a then (1 : ℝ) else if b = a then 1 / 2 else 0) ∂μy ∂μx := by
    intro i j
    have hindep : IndepFun (Z (Sum.inl i)) (Z (Sum.inr j)) μ :=
      hIndep.indepFun (by simp)
    have hmap : μ.map (fun ω => (Z (Sum.inl i) ω, Z (Sum.inr j) ω)) = μx.prod μy := by
      rw [hindep.map_prod_eq_prod_map_map (hX i).aemeasurable (hY j).aemeasurable,
        (hX i).map_eq, (hY j).map_eq]
    have hpair : AEMeasurable (fun ω => (Z (Sum.inl i) ω, Z (Sum.inr j) ω)) μ :=
      hpair_ae i j
    have hint_prod : Integrable (fun p : ℝ × ℝ =>
        (if p.2 < p.1 then (1 : ℝ) else if p.2 = p.1 then 1 / 2 else 0)) (μx.prod μy) :=
      Integrable.of_bound mannWhitneyKernel_measurable.aestronglyMeasurable 1
        (Filter.Eventually.of_forall mannWhitneyKernel_norm_le_one)
    calc ∫ ω, (if Z (Sum.inr j) ω < Z (Sum.inl i) ω then (1 : ℝ)
            else if Z (Sum.inr j) ω = Z (Sum.inl i) ω then 1 / 2 else 0) ∂μ
        = ∫ p, (if p.2 < p.1 then (1 : ℝ) else if p.2 = p.1 then 1 / 2 else 0)
            ∂(μ.map (fun ω => (Z (Sum.inl i) ω, Z (Sum.inr j) ω))) := by
              rw [integral_map hpair
                mannWhitneyKernel_measurable.aestronglyMeasurable]
      _ = ∫ p, (if p.2 < p.1 then (1 : ℝ) else if p.2 = p.1 then 1 / 2 else 0)
            ∂(μx.prod μy) := by rw [hmap]
      _ = ∫ a, ∫ b,
            (if b < a then (1 : ℝ) else if b = a then 1 / 2 else 0) ∂μy ∂μx :=
          integral_prod _ hint_prod
  simp only [mannWhitneyU]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hinterm i j))]
  rw [Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hinterm i j))]
  simp only [hterm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end ProbabilityTheory
