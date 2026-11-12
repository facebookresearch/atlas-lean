/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import MathlibExt.Probability.HoeffdingBernoulliSumAbsTail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Indicator

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

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
  have hYmeas : ∀ i, AEMeasurable (fun ω => if X i ω ≤ x then (1 : ℝ) else 0) μ :=
    fun i => hg_if.comp_aemeasurable (hlaw i).aemeasurable
  have hmean : ∀ i, ∫ ω, (if X i ω ≤ x then (1 : ℝ) else 0) ∂μ
      = (ν (Set.Iic x)).toReal := by
    intro i
    have hAES : AEStronglyMeasurable (Set.indicator (Set.Iic x) (fun _ => (1 : ℝ))) ν :=
      (Measurable.indicator measurable_const measurableSet_Iic).aestronglyMeasurable
    have h := (hlaw i).integral_comp hAES
    rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one] at h
    have hfun : (fun ω => if X i ω ≤ x then (1 : ℝ) else 0)
        = (Set.indicator (Set.Iic x) (fun _ => (1 : ℝ))) ∘ (X i) := funext (hYeq i)
    rw [hfun]
    exact h
  have hbern : ∀ i, ∀ᵐ ω ∂μ, (if X i ω ≤ x then (1 : ℝ) else 0) = 0
      ∨ (if X i ω ≤ x then (1 : ℝ) else 0) = 1 :=
    fun i => ae_of_all _ fun ω => by by_cases h : X i ω ≤ x <;> simp [h]
  have hIY : iIndepFun (fun i ω => (if X i ω ≤ x then (1 : ℝ) else 0)) μ :=
    hIndep.comp _ (fun _ => hg_if)
  have htail := ProbabilityTheory.hoeffding_bernoulli_sum_abs_tail
    (X := fun i ω => (if X i ω ≤ x then (1 : ℝ) else 0))
    (p := (ν (Set.Iic x)).toReal) (ε := eps)
    hIY hYmeas hbern (fun i => hmean i) heps
  have key : ∀ ω, |∑ i, (if X i ω ≤ x then (1 : ℝ) else 0) - (n : ℝ) * (ν (Set.Iic x)).toReal|
      = (n : ℝ) * |empCDF (fun i => X i ω) x - (ν (Set.Iic x)).toReal| := by
    intro ω
    have e1 : (∑ i, (if X i ω ≤ x then (1 : ℝ) else 0)) - (n : ℝ) * (ν (Set.Iic x)).toReal
        = (n : ℝ) * (empCDF (fun i => X i ω) x - (ν (Set.Iic x)).toReal) := by
      rw [empCDF_eq_sum_div]
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      field_simp
    rw [e1, abs_mul, abs_of_nonneg hnpos.le]
  have hev : {ω | eps < |empCDF (fun i => X i ω) x - (ν (Set.Iic x)).toReal|}
      = {ω | eps * (n : ℝ)
        < |∑ i, (if X i ω ≤ x then (1 : ℝ) else 0) - (n : ℝ) * (ν (Set.Iic x)).toReal|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, key]
    constructor
    · intro h
      calc eps * (n : ℝ)
          < |empCDF (fun i => X i ω) x - (ν (Set.Iic x)).toReal| * (n : ℝ) :=
            mul_lt_mul_of_pos_right h hnpos
        _ = (n : ℝ) * |empCDF (fun i => X i ω) x - (ν (Set.Iic x)).toReal| :=
            mul_comm _ _
    · intro h
      rw [mul_comm eps] at h
      exact lt_of_mul_lt_mul_left h (le_of_lt hnpos)
  have hexp_eq : (-2 * eps ^ 2 * (n : ℝ)) = -2 * (n : ℝ) * eps ^ 2 := by ring
  have hA : μ.real {ω | eps < |empCDF (fun i => X i ω) x - (ν (Set.Iic x)).toReal|}
      ≤ 2 * Real.exp (-2 * eps ^ 2 * (n : ℝ)) := by
    rw [hev]
    exact htail
  rw [hexp_eq] at hA
  have hfin : μ {ω | eps < |empCDF (fun i => X i ω) x - (ν (Set.Iic x)).toReal|} ≠ ⊤ :=
    measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hA

end ProbabilityTheory
