/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace ProbabilityTheory

private lemma pdf_le {u x : ℝ} (hu : 0 ≤ u) (hx : u ≤ x) :
    gaussianPDFReal 0 1 x ≤ Real.exp (-u ^ 2 / 2) * gaussianPDFReal u 1 x := by
  have hsq : u ^ 2 + (x - u) ^ 2 ≤ x ^ 2 := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hx)]
  rw [gaussianPDFReal, gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hC : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hexp : Real.exp (-x ^ 2 / 2)
      ≤ Real.exp (-u ^ 2 / 2) * Real.exp (-(x - u) ^ 2 / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hsq]
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)
      ≤ (Real.sqrt (2 * Real.pi))⁻¹
          * (Real.exp (-u ^ 2 / 2) * Real.exp (-(x - u) ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hexp hC
    _ = Real.exp (-u ^ 2 / 2)
          * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x - u) ^ 2 / 2)) := by
        ring

private lemma integral_le {u : ℝ} (hu : 0 ≤ u) :
    gaussianReal 0 1 (Set.Ioi u)
      ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / 2)) * gaussianReal u 1 (Set.Ioi u) := by
  have h1 : (1 : ℝ≥0) ≠ 0 := by simp
  rw [gaussianReal_apply 0 h1, gaussianReal_apply u h1,
    ← lintegral_const_mul _ (measurable_gaussianPDF u 1)]
  apply setLIntegral_mono' measurableSet_Ioi
  intro x hx
  rw [Set.mem_Ioi] at hx
  have hle := pdf_le hu (le_of_lt hx)
  simp only [gaussianPDF] at hle ⊢
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

private lemma translate_eq {u : ℝ} :
    gaussianReal u 1 (Set.Ioi u) = gaussianReal 0 1 (Set.Ioi 0) := by
  have hmap := gaussianReal_map_const_add (μ := u) (v := 1) (-u)
  rw [add_neg_cancel] at hmap
  have hpre : (fun x : ℝ => -u + x) ⁻¹' Set.Ioi 0 = Set.Ioi u := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  calc gaussianReal u 1 (Set.Ioi u)
      = gaussianReal u 1 ((fun x : ℝ => -u + x) ⁻¹' Set.Ioi 0) := by rw [hpre]
    _ = Measure.map (fun x : ℝ => -u + x) (gaussianReal u 1) (Set.Ioi 0) :=
        (Measure.map_apply (measurable_const_add _) measurableSet_Ioi).symm
    _ = gaussianReal 0 1 (Set.Ioi 0) := by rw [hmap]

private lemma half_eq : gaussianReal 0 1 (Set.Ioi 0) = ENNReal.ofReal (1 / 2 : ℝ) := by
  have hmap := gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  rw [neg_zero] at hmap
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi 0 = Set.Iio 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, neg_pos]
  have hsym : gaussianReal 0 1 (Set.Ioi 0) = gaussianReal 0 1 (Set.Iio 0) := by
    calc gaussianReal 0 1 (Set.Ioi 0)
        = Measure.map (fun x : ℝ => -x) (gaussianReal 0 1) (Set.Ioi 0) := by rw [hmap]
      _ = gaussianReal 0 1 ((fun x : ℝ => -x) ⁻¹' Set.Ioi 0) :=
          Measure.map_apply measurable_neg measurableSet_Ioi
      _ = gaussianReal 0 1 (Set.Iio 0) := by rw [hpre]
  have hnull := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (show (1 : ℝ≥0) ≠ 0 by simp)
  have hsing : gaussianReal 0 1 {(0 : ℝ)} = 0 := hnull.measure_singleton 0
  have hunion : Set.Ioi (0 : ℝ) ∪ Set.Iio 0 ∪ {(0 : ℝ)} = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iio, Set.mem_singleton_iff, Set.mem_univ,
      iff_true]
    obtain h | h | h := lt_trichotomy x 0
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
  have hdisj1 : Disjoint (Set.Ioi (0 : ℝ)) (Set.Iio 0) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Ioi, Set.mem_Iio] at hx1 hx2
    linarith
  have hdisj2 : Disjoint (Set.Ioi (0 : ℝ) ∪ Set.Iio 0) ({(0 : ℝ)} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hx hmem
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iio, Set.mem_singleton_iff] at hx hmem
    rw [hmem] at hx
    simp at hx
  have htot : gaussianReal 0 1 (Set.Ioi 0) + gaussianReal 0 1 (Set.Iio 0) = 1 := by
    have h := measure_union (μ := gaussianReal 0 1) hdisj2 (MeasurableSet.singleton 0)
    rw [hunion, measure_univ, measure_union hdisj1 measurableSet_Iio, hsing, add_zero] at h
    exact h.symm
  have h2 : gaussianReal 0 1 (Set.Ioi 0) + gaussianReal 0 1 (Set.Ioi 0) = 1 := by
    rw [← hsym] at htot
    exact htot
  have hle : gaussianReal 0 1 (Set.Ioi 0) ≤ 1 :=
    calc gaussianReal 0 1 (Set.Ioi 0) ≤ gaussianReal 0 1 Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hfin : gaussianReal 0 1 (Set.Ioi 0) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have hTo : (gaussianReal 0 1 (Set.Ioi 0)).toReal = 1 / 2 := by
    have h := congrArg ENNReal.toReal h2
    rw [ENNReal.toReal_add hfin hfin, ENNReal.toReal_one] at h
    linarith
  rw [← hTo, ENNReal.ofReal_toReal hfin]

theorem gaussianReal_Ioi_le_half_exp {u : ℝ} (hu : 0 ≤ u) :
    gaussianReal 0 1 (Set.Ioi u) ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / 2) / 2) := by
  have hE : (0 : ℝ) ≤ Real.exp (-u ^ 2 / 2) := Real.exp_nonneg _
  calc gaussianReal 0 1 (Set.Ioi u)
      ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / 2)) * gaussianReal u 1 (Set.Ioi u) :=
        integral_le hu
    _ = ENNReal.ofReal (Real.exp (-u ^ 2 / 2)) * gaussianReal 0 1 (Set.Ioi 0) := by
        rw [translate_eq]
    _ = ENNReal.ofReal (Real.exp (-u ^ 2 / 2)) * ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [half_eq]
    _ = ENNReal.ofReal (Real.exp (-u ^ 2 / 2) / 2) := by
        rw [← ENNReal.ofReal_mul hE]
        congr 1
        ring
