/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Classical.InfinitesimalLimit
import Mathlib.Probability.Independence.InfinitePi

/-! Tests for the segregation Berry–Esseen bound: the public statements restated, a
non-vacuity instance on an explicit product space, the `σ = 0` counterexample showing the
positivity hypothesis is needed, and the one-locus law at concrete parental genotypes. -/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.InfinitesimalLimit

open MathlibExt.Biology.PopulationGenetics.Classical.InfinitesimalLimit

variable {Ω : Type*} [MeasurableSpace Ω]

instance : IsProbabilityMeasure (mendelLaw 1 0) :=
  isProbabilityMeasure_mendelLaw (by norm_num) (by norm_num)

/-- The segregation variance, restated. -/
example {P : Measure Ω} [IsProbabilityMeasure P] {M : ℕ} {a : ℕ → ℝ} {X : ℕ → Ω → ℝ}
    (hXm : ∀ l, Measurable (X l)) (hind : iIndepFun X P)
    (hX : ∀ l, ∀ᵐ ω ∂P, X l ω ∈ Set.Icc (0 : ℝ) 2) :
    Var[segregationDeviation P M a X; P] = ∑ l ∈ range M, a l ^ 2 * Var[X l; P] :=
  variance_segregationDeviation hXm hind hX

/-- The Berry–Esseen bound with constant `336`, restated. -/
example {P : Measure Ω} [IsProbabilityMeasure P] {M : ℕ} {B σ : ℝ} {a : ℕ → ℝ}
    {X : ℕ → Ω → ℝ} (hXm : ∀ l, Measurable (X l)) (hind : iIndepFun X P)
    (hX : ∀ l, ∀ᵐ ω ∂P, X l ω ∈ Set.Icc (0 : ℝ) 2) (ha : ∀ l < M, |a l| ≤ B / √M)
    (hσ : 0 < σ) (hvar : Var[segregationDeviation P M a X; P] = σ ^ 2) (x : ℝ) :
    |P.real {ω | segregationDeviation P M a X ω ≤ x} -
        (gaussianReal 0 1).real (Set.Iic (x / σ))| ≤ 336 * B ^ 3 / (σ ^ 3 * √M) :=
  abs_segregation_cdf_sub_le hXm hind hX ha hσ hvar x

/-- The Mendelian specialization, restated. -/
example {P : Measure Ω} [IsProbabilityMeasure P] {M : ℕ} {B σ : ℝ} {a : ℕ → ℝ}
    {X : ℕ → Ω → ℝ} {g₁ g₂ : ℕ → ℕ} (hXm : ∀ l, Measurable (X l)) (hind : iIndepFun X P)
    (hlaw : ∀ l, P.map (X l) = mendelLaw (g₁ l) (g₂ l)) (ha : ∀ l < M, |a l| ≤ B / √M)
    (hσ : 0 < σ) (hvar : Var[segregationDeviation P M a X; P] = σ ^ 2) (x : ℝ) :
    |P.real {ω | segregationDeviation P M a X ω ≤ x} -
        (gaussianReal 0 1).real (Set.Iic (x / σ))| ≤ 336 * B ^ 3 / (σ ^ 3 * √M) :=
  abs_mendelian_segregation_cdf_sub_le hXm hind hlaw ha hσ hvar x

/-- The explicit-variance Mendelian form, restated: the variance premise is the explicit
sum of per-locus Mendelian variances. -/
example {P : Measure Ω} [IsProbabilityMeasure P] {M : ℕ} {B σ : ℝ} {a : ℕ → ℝ}
    {X : ℕ → Ω → ℝ} {g₁ g₂ : ℕ → ℕ} (hXm : ∀ l, Measurable (X l)) (hind : iIndepFun X P)
    (hlaw : ∀ l, P.map (X l) = mendelLaw (g₁ l) (g₂ l)) (hg₁ : ∀ l, g₁ l ≤ 2)
    (hg₂ : ∀ l, g₂ l ≤ 2) (ha : ∀ l < M, |a l| ≤ B / √M) (hσ : 0 < σ)
    (hvar : ∑ l ∈ range M, a l ^ 2 * ((g₁ l : ℝ) / 2 * (1 - (g₁ l : ℝ) / 2) +
      (g₂ l : ℝ) / 2 * (1 - (g₂ l : ℝ) / 2)) = σ ^ 2) (x : ℝ) :
    |P.real {ω | segregationDeviation P M a X ω ≤ x} -
        (gaussianReal 0 1).real (Set.Iic (x / σ))| ≤ 336 * B ^ 3 / (σ ^ 3 * √M) :=
  abs_mendelian_segregation_cdf_sub_le_of_variance_eq hXm hind hlaw hg₁ hg₂ ha hσ hvar x

/-- Two heterozygous parents (`g₁ = g₂ = 1`): mean count `1`, variance `1 / 2`. -/
example : ∫ x, x ∂(mendelLaw 1 1) = 1 := by
  rw [integral_mendelLaw _ (by norm_num) (by norm_num)]
  norm_num
example : Var[id; mendelLaw 1 1] = 1 / 2 := by
  rw [variance_mendelLaw (by norm_num) (by norm_num)]
  norm_num

/-- Homozygous opposite parents (`g₁ = 2`, `g₂ = 0`): mean `1`, variance `0`. -/
example : ∫ x, x ∂(mendelLaw 2 0) = 1 := by
  rw [integral_mendelLaw _ (by norm_num) (by norm_num)]
  norm_num
example : Var[id; mendelLaw 2 0] = 0 := by
  rw [variance_mendelLaw (by norm_num) (by norm_num)]
  norm_num

/-- Non-vacuity: the bound on the explicit product space of `mendelLaw 1 0` loci with
effects `1 / √M` (so `σ = 1 / 2`). -/
example (M : ℕ) (hM : 0 < M) (x : ℝ) :
    |(Measure.infinitePi fun _ : ℕ => mendelLaw 1 0).real
        {ω | segregationDeviation (Measure.infinitePi fun _ : ℕ => mendelLaw 1 0) M
          (fun _ => 1 / √M) (fun l ω => ω l) ω ≤ x} -
        (gaussianReal 0 1).real (Set.Iic (x / (1 / 2)))| ≤
      336 * 1 ^ 3 / ((1 / 2) ^ 3 * √M) := by
  set P := Measure.infinitePi fun _ : ℕ => mendelLaw 1 0 with hP
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hXm : ∀ l, Measurable (fun ω : ℕ → ℝ => ω l) := fun l => measurable_pi_apply l
  have hind : iIndepFun (fun l (ω : ℕ → ℝ) => ω l) P :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hlaw : ∀ l, P.map (fun ω : ℕ → ℝ => ω l) = mendelLaw 1 0 := fun l =>
    Measure.infinitePi_map_eval _ l
  have hX : ∀ l, ∀ᵐ ω ∂P, (fun l (ω : ℕ → ℝ) => ω l) l ω ∈ Set.Icc (0 : ℝ) 2 := fun l => by
    have h := mendelLaw_compl_Icc 1 0
    rw [← hlaw l, Measure.map_apply (hXm l) measurableSet_Icc.compl] at h
    exact ae_iff.2 h
  refine abs_mendelian_segregation_cdf_sub_le (g₁ := fun _ => 1) (g₂ := fun _ => 0) hXm hind
    hlaw (fun l _ => ?_) (by norm_num) ?_ x
  · rw [abs_of_pos (by positivity)]
  · rw [variance_segregationDeviation hXm hind hX]
    have hv : ∀ l, Var[(fun l (ω : ℕ → ℝ) => ω l) l; P] = 1 / 4 := fun l => by
      rw [← variance_id_map (hXm l).aemeasurable, hlaw l, variance_mendelLaw (by norm_num)
        (by norm_num)]
      norm_num
    simp only [hv, Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_pow, one_pow,
      Real.sq_sqrt hMr.le]
    field_simp
    ring

/-- The degenerate case `σ = 0` must be excluded: with zero effects the deviation is
identically `0`, its variance is `0 = 0²`, every other hypothesis holds (with `B = 0`), and
the conclusion fails at `x = 0`. -/
example :
    Var[segregationDeviation (Measure.infinitePi fun _ : ℕ => mendelLaw 1 0) 1 (fun _ => 0)
        (fun l ω => ω l); Measure.infinitePi fun _ : ℕ => mendelLaw 1 0] = 0 ^ 2 ∧
      ¬ |(Measure.infinitePi fun _ : ℕ => mendelLaw 1 0).real
          {ω | segregationDeviation (Measure.infinitePi fun _ : ℕ => mendelLaw 1 0) 1
            (fun _ => 0) (fun l ω => ω l) ω ≤ 0} -
          (gaussianReal 0 1).real (Set.Iic (0 / 0))| ≤ 336 * 0 ^ 3 / (0 ^ 3 * √1) := by
  have hR : segregationDeviation (Measure.infinitePi fun _ : ℕ => mendelLaw 1 0) 1 (fun _ => 0)
      (fun l ω => ω l) = 0 := by
    funext ω; simp [segregationDeviation]
  have hΦ : (gaussianReal 0 1).real (Set.Iic 0) = 1 / 2 := by
    have hv : (1 : NNReal) ≠ 0 := one_ne_zero
    have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) hv
    have hsymm : gaussianReal 0 1 (Set.Iic 0) = gaussianReal 0 1 (Set.Ici 0) := by
      have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
      rw [neg_zero] at h
      conv_lhs => rw [← h]
      rw [Measure.map_apply measurable_neg measurableSet_Iic]
      congr 1
      ext x
      simp
    have hIci : gaussianReal 0 1 (Set.Ici 0) = gaussianReal 0 1 (Set.Ioi 0) := by
      refine le_antisymm ?_ (measure_mono Set.Ioi_subset_Ici_self)
      calc gaussianReal 0 1 (Set.Ici 0) = gaussianReal 0 1 ({0} ∪ Set.Ioi 0) := by
            rw [Set.singleton_union, Set.Ioi_insert]
        _ ≤ gaussianReal 0 1 {0} + gaussianReal 0 1 (Set.Ioi 0) := measure_union_le _ _
        _ = gaussianReal 0 1 (Set.Ioi 0) := by rw [measure_singleton, zero_add]
    have htot : gaussianReal 0 1 (Set.Iic 0) + gaussianReal 0 1 (Set.Ioi 0) = 1 := by
      rw [← measure_union (Set.disjoint_left.2 fun x hx hy => by
        simp only [Set.mem_Iic, Set.mem_Ioi] at hx hy; linarith) measurableSet_Ioi,
        Set.Iic_union_Ioi, measure_univ]
    have h2 : 2 * gaussianReal 0 1 (Set.Iic 0) = 1 := by
      rw [two_mul]
      conv_lhs => arg 2; rw [hsymm, hIci]
      exact htot
    rw [Measure.real]
    have h2' := congrArg ENNReal.toReal h2
    rw [ENNReal.toReal_mul, ENNReal.toReal_one] at h2'
    simp only [ENNReal.toReal_ofNat] at h2'
    linarith
  rw [hR]
  refine ⟨by simp [variance_zero], ?_⟩
  simp only [Pi.zero_apply, le_refl, Set.ofPred_true, probReal_univ, div_zero, hΦ]
  norm_num

end MathlibExtTest.Biology.PopulationGenetics.Classical.InfinitesimalLimit
