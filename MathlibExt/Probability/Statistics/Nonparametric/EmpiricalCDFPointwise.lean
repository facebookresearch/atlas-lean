/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Indicator

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Empirical CDF over a `Fin n` sample with the `/n` normalization. -/
noncomputable def empCDF {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i => X i ≤ t)).card : ℝ) / (n : ℝ)

lemma empCDF_eq_sum_div {n : ℕ} (X : Fin n → ℝ) (t : ℝ) :
    empCDF X t = (∑ i ∈ Finset.univ, (if X i ≤ t then (1 : ℝ) else 0)) / (n : ℝ) := by
  unfold empCDF
  rw [Finset.card_filter, Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : X i ≤ t <;> simp [h]

/-- Pointwise Hoeffding bound for the empirical CDF at a fixed threshold. -/
theorem abs_empCDF_sub_le {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → ℝ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlaw : ∀ i, HasLaw (X i) ν μ) (hIndep : iIndepFun X μ)
    (x : ℝ) (eps : ℝ) (heps : 0 < eps) :
    μ {ω | eps < |empCDF (fun i => X i ω) x - (ν (Set.Iic x)).toReal|}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * eps ^ 2)) := by
  set F := (ν (Set.Iic x)).toReal
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hg_if : Measurable (fun y : ℝ => if y ≤ x then (1 : ℝ) else 0) := by
    have heq : (fun y : ℝ => if y ≤ x then (1 : ℝ) else 0)
        = Set.indicator (Set.Iic x) (fun _ => (1 : ℝ)) := by
      funext y
      unfold Set.indicator
      by_cases h : y ≤ x
      · simp only [ite_eq_left h, ite_eq_left (Set.mem_Iic.mpr h)]
      · simp only [ite_eq_right h, ite_eq_right (mt Set.mem_Iic.mp h)]
    rw [heq]
    exact Measurable.indicator measurable_const measurableSet_Iic
  have hYeq : ∀ (i : Fin n) (ω : Ω), (if X i ω ≤ x then (1 : ℝ) else 0)
      = Set.indicator (Set.Iic x) (fun _ => (1 : ℝ)) (X i ω) := by
    intro i ω
    unfold Set.indicator
    by_cases h : X i ω ≤ x
    · simp only [ite_eq_left h, ite_eq_left (Set.mem_Iic.mpr h)]
    · simp only [ite_eq_right h, ite_eq_right (mt Set.mem_Iic.mp h)]
  have hYmeas : ∀ i, AEMeasurable (fun ω => if X i ω ≤ x then (1 : ℝ) else 0) μ := by
    intro i
    exact hg_if.comp_aemeasurable (hlaw i).aemeasurable
  have hmean : ∀ i, ∫ ω, (if X i ω ≤ x then (1 : ℝ) else 0) ∂μ = F := by
    intro i
    have hAES : AEStronglyMeasurable (Set.indicator (Set.Iic x) (fun _ => (1 : ℝ))) ν :=
      (Measurable.indicator measurable_const measurableSet_Iic).aestronglyMeasurable
    have h := (hlaw i).integral_comp hAES
    rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one] at h
    have hfun : (fun ω => if X i ω ≤ x then (1 : ℝ) else 0)
        = (Set.indicator (Set.Iic x) (fun _ => (1 : ℝ))) ∘ (X i) := funext (hYeq i)
    rw [hfun]
    exact h
  have hIcc : ∀ i, ∀ᵐ ω ∂μ, (if X i ω ≤ x then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    refine ae_of_all _ fun ω => ?_
    by_cases h : X i ω ≤ x <;> simp [h, Set.mem_Icc]
  have hsubG : ∀ i, HasSubgaussianMGF (fun ω => (if X i ω ≤ x then (1 : ℝ) else 0) - F)
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (hYmeas i) (hIcc i)
    rw [hmean i] at h
    exact h
  have hmeas_sub : Measurable (fun y : ℝ => (if y ≤ x then (1 : ℝ) else 0) - F) :=
    hg_if.sub_const F
  have hIndepY : iIndepFun (fun i ω => (if X i ω ≤ x then (1 : ℝ) else 0) - F) μ := by
    refine iIndepFun.congr
      (f := fun i => (fun y : ℝ => (if y ≤ x then (1 : ℝ) else 0) - F) ∘ (X i))
      (fun i => ae_of_all _ fun ω => rfl) ?_
    exact hIndep.comp _ (fun _ => hmeas_sub)
  have hsubG' : ∀ i, HasSubgaussianMGF (fun ω => F - (if X i ω ≤ x then (1 : ℝ) else 0))
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    intro i
    have h := (hsubG i).neg
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.neg_apply]
    ring
  have hIndepW : iIndepFun (fun i ω => F - (if X i ω ≤ x then (1 : ℝ) else 0)) μ := by
    refine iIndepFun.congr
      (f := fun i => (fun y : ℝ => F - (if y ≤ x then (1 : ℝ) else 0)) ∘ (X i))
      (fun i => ae_of_all _ fun ω => rfl) ?_
    exact hIndep.comp _
      (fun _ => (measurable_const.sub hg_if :
        Measurable (fun y : ℝ => F - (if y ≤ x then (1 : ℝ) else 0))))
  have hε : (0 : ℝ) ≤ (n : ℝ) * eps := mul_nonneg (Nat.cast_nonneg _) heps.le
  have side1 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := Finset.univ)
    hIndepY (fun i _ => hsubG i) hε
  have side2 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := Finset.univ)
    hIndepW (fun i _ => hsubG' i) hε
  have hnn : ‖(1 : ℝ) - 0‖₊ = (1 : NNReal) := by
    rw [sub_zero]
    exact nnnorm_one
  have hquarter : ((1 / 2 : NNReal) ^ 2 : NNReal) = 1 / 4 := by
    ext
    push_cast
    norm_num
  have hsum_c : (↑(∑ i ∈ (Finset.univ : Finset (Fin n)), ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ)
      = (n : ℝ) * (1 / 4 : ℝ) := by
    rw [hnn, hquarter, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hexp : (-((n : ℝ) * eps) ^ 2 / (2 * ((n : ℝ) * (1 / 4)))) = -2 * (n : ℝ) * eps ^ 2 := by
    have hdenom : (2 : ℝ) * ((n : ℝ) * (1 / 4)) ≠ 0 :=
      mul_ne_zero (by norm_num) (mul_ne_zero (ne_of_gt hnpos) (by norm_num))
    rw [div_eq_iff hdenom]
    ring
  have hexp' : (-((n : ℝ) * eps) ^ 2
        / (2 * (↑(∑ i ∈ (Finset.univ : Finset (Fin n)), ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ)))
      = -2 * (n : ℝ) * eps ^ 2 := by
    rw [hsum_c]
    exact hexp
  have hB : μ.real {ω | (n : ℝ) * eps
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), ((if X i ω ≤ x then (1 : ℝ) else 0) - F)}
      ≤ Real.exp (-2 * (n : ℝ) * eps ^ 2) := by
    have hside := side1
    simp only [hexp'] at hside
    exact hside
  have hC : μ.real {ω | (n : ℝ) * eps
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (F - (if X i ω ≤ x then (1 : ℝ) else 0))}
      ≤ Real.exp (-2 * (n : ℝ) * eps ^ 2) := by
    have hside := side2
    simp only [hexp'] at hside
    exact hside
  have hsum : ∀ ω, (∑ i ∈ (Finset.univ : Finset (Fin n)),
        ((if X i ω ≤ x then (1 : ℝ) else 0) - F))
      = (n : ℝ) * (empCDF (fun i => X i ω) x - F) := by
    intro ω
    simp only [Finset.sum_sub_distrib, empCDF_eq_sum_div, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    field_simp
  have hsum' : ∀ ω, (∑ i ∈ (Finset.univ : Finset (Fin n)),
        (F - (if X i ω ≤ x then (1 : ℝ) else 0)))
      = -∑ i ∈ (Finset.univ : Finset (Fin n)), ((if X i ω ≤ x then (1 : ℝ) else 0) - F) := by
    intro ω
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hsub : {ω | eps < |empCDF (fun i => X i ω) x - F|}
      ⊆ {ω | (n : ℝ) * eps
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), ((if X i ω ≤ x then (1 : ℝ) else 0) - F)}
        ∪ {ω | (n : ℝ) * eps
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (F - (if X i ω ≤ x then (1 : ℝ) else 0))} := by
    intro ω h
    simp only [Set.mem_ofPred_eq, Set.mem_union] at h ⊢
    rw [lt_abs] at h
    rcases h with h | h
    · left
      rw [hsum ω]
      exact le_of_lt (mul_lt_mul_of_pos_left h hnpos)
    · right
      rw [hsum' ω, hsum ω]
      have h2 := mul_lt_mul_of_pos_left h hnpos
      have heq : (n : ℝ) * (-(empCDF (fun i => X i ω) x - F))
        = -((n : ℝ) * (empCDF (fun i => X i ω) x - F)) := by ring
      rw [← heq]
      exact le_of_lt h2
  have hunion : μ.real ({ω | (n : ℝ) * eps
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), ((if X i ω ≤ x then (1 : ℝ) else 0) - F)}
        ∪ {ω | (n : ℝ) * eps
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (F - (if X i ω ≤ x then (1 : ℝ) else 0))})
      ≤ 2 * Real.exp (-2 * (n : ℝ) * eps ^ 2) :=
    calc μ.real ({ω | (n : ℝ) * eps
            ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), ((if X i ω ≤ x then (1 : ℝ) else 0) - F)}
          ∪ {ω | (n : ℝ) * eps
            ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (F - (if X i ω ≤ x then (1 : ℝ) else 0))})
        ≤ μ.real {ω | (n : ℝ) * eps
            ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), ((if X i ω ≤ x then (1 : ℝ) else 0) - F)}
          + μ.real {ω | (n : ℝ) * eps
            ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (F - (if X i ω ≤ x then (1 : ℝ) else 0))} :=
          measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-2 * (n : ℝ) * eps ^ 2) := by linarith [hB, hC]
  have hA : μ.real {ω | eps < |empCDF (fun i => X i ω) x - F|}
      ≤ 2 * Real.exp (-2 * (n : ℝ) * eps ^ 2) :=
    (measureReal_mono hsub).trans hunion
  have hfin : μ {ω | eps < |empCDF (fun i => X i ω) x - F|} ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hA
