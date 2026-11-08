/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.BerryEsseenConstant
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory Set BerryEsseenModel BerryEsseenConstant
open scoped ENNReal NNReal

namespace MathlibExtTest.BerryEsseenSourceCorrection

noncomputable def sparseLaw : Measure ℝ :=
  ((9999 / 10000 : ℝ≥0) : ENNReal) • Measure.dirac 0 +
    ((1 / 20000 : ℝ≥0) : ENNReal) • Measure.dirac 100 +
    ((1 / 20000 : ℝ≥0) : ENNReal) • Measure.dirac (-100)

instance sparseLaw_probability : IsProbabilityMeasure sparseLaw where
  measure_univ := by
    simp only [sparseLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    norm_cast
    norm_num

lemma sparseLaw_bound : ∀ᵐ x ∂sparseLaw, ‖x‖ ≤ 100 := by
  rw [sparseLaw, ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩,
    Measure.ae_smul_measure ?_ _⟩ <;> simp

lemma sparseLaw_memLp (p : ENNReal) : MemLp id p sparseLaw :=
  MemLp.of_bound measurable_id.aestronglyMeasurable 100 sparseLaw_bound

lemma sparseLaw_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂sparseLaw) =
      (9999 / 10000) * f 0 + (1 / 20000) * f 100 + (1 / 20000) * f (-100) := by
  have h0 : Integrable f (Measure.dirac 0) := integrable_dirac (by simp)
  have h1 : Integrable f (Measure.dirac 100) := integrable_dirac (by simp)
  have h2 : Integrable f (Measure.dirac (-100)) := integrable_dirac (by simp)
  have h0s := h0.smul_measure (c := ((9999 / 10000 : ℝ≥0) : ENNReal)) ENNReal.coe_ne_top
  have h1s := h1.smul_measure (c := ((1 / 20000 : ℝ≥0) : ENNReal)) ENNReal.coe_ne_top
  have h2s := h2.smul_measure (c := ((1 / 20000 : ℝ≥0) : ENNReal)) ENNReal.coe_ne_top
  rw [sparseLaw, integral_add_measure (h0s.add_measure h1s) h2s,
    integral_add_measure h0s h1s]
  simp [integral_smul_measure, integral_dirac]

lemma sparseLaw_mean : (∫ x, x ∂sparseLaw) = 0 := by
  change (∫ x, id x ∂sparseLaw) = 0
  rw [sparseLaw_integral]
  norm_num

lemma sparseLaw_variance : variance id sparseLaw = 1 := by
  rw [variance_eq_sub (sparseLaw_memLp 2)]
  change (∫ x, x ^ 2 ∂sparseLaw) - (∫ x, x ∂sparseLaw) ^ 2 = 1
  rw [sparseLaw_mean, sparseLaw_integral]
  norm_num

lemma sparseLaw_thirdMoment : (∫ x, |x| ^ 3 ∂sparseLaw) = 100 := by
  rw [sparseLaw_integral]
  norm_num

lemma sparseLaw_zero : sparseLaw {0} = ((9999 / 10000 : ℝ≥0) : ENNReal) := by
  norm_num [sparseLaw, Measure.add_apply, Measure.smul_apply]

lemma allZero_probability :
    (Measure.infinitePi (fun _ : ℕ ↦ sparseLaw))
      (Set.pi (Finset.range 100) (fun _ ↦ ({0} : Set ℝ))) =
        ((9999 / 10000 : ℝ≥0) : ENNReal) ^ 100 := by
  rw [Measure.infinitePi_pi _ (fun _ _ ↦ measurableSet_singleton 0)]
  simp [sparseLaw_zero]

lemma allZero_probability_lower :
    (99 / 100 : ℝ) ≤
      (Measure.infinitePi (fun _ : ℕ ↦ sparseLaw)).real
        (Set.pi (Finset.range 100) (fun _ ↦ ({0} : Set ℝ))) := by
  rw [Measure.real, allZero_probability]
  norm_num [ENNReal.toReal_pow, ENNReal.toReal_div]

lemma standardGaussian_cdf_zero : cdf (gaussianReal 0 1) 0 = (1 / 2 : ℝ) := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hsame : (gaussianReal 0 1).real (Iio (0 : ℝ)) =
      (gaussianReal 0 1).real (Iic 0) := by
    have hset : Iic (0 : ℝ) = Iio 0 ∪ {0} := by ext x; simp [le_iff_lt_or_eq]
    have hdisjoint : Disjoint (Iio (0 : ℝ)) ({0} : Set ℝ) := by
      rw [Set.disjoint_left]
      intro x hx hzero
      have hz : x = 0 := mem_singleton_iff.mp hzero
      subst x
      exact (lt_irrefl (0 : ℝ)) hx
    rw [hset, measureReal_union hdisjoint (measurableSet_singleton 0)
      (measure_ne_top _ _) (measure_ne_top _ _)]
    simp [Measure.real]
  have hsym : (gaussianReal 0 1).real (Iic (0 : ℝ)) =
      (gaussianReal 0 1).real (Ici 0) := by
    have hm : (gaussianReal 0 1).map (fun x : ℝ ↦ -x) = gaussianReal 0 1 := by
      rw [gaussianReal_map_neg]
      simp
    calc
      (gaussianReal 0 1).real (Iic (0 : ℝ)) =
          ((gaussianReal 0 1).map (fun x : ℝ ↦ -x)).real (Iic 0) := by rw [hm]
      _ = (gaussianReal 0 1).real (Ici 0) := by
        rw [map_measureReal_apply measurable_neg measurableSet_Iic]
        congr 1
        ext x
        simp
  have hcompl : (gaussianReal 0 1).real (Ici (0 : ℝ)) =
      1 - (gaussianReal 0 1).real (Iio 0) := by
    rw [← Set.compl_Iio]
    exact probReal_compl_eq_one_sub measurableSet_Iio
  rw [cdf_eq_real]
  linarith

abbrev hundredSamples : ℕ+ := ⟨100, by decide⟩

noncomputable abbrev sample100 : (ℕ → ℝ) → ℝ := normalizedSum hundredSamples

lemma measurable_sample100 : Measurable sample100 := normalizedSum_measurable hundredSamples

lemma sparse_cdf_lower : (99 / 100 : ℝ) ≤
    cdf ((Measure.infinitePi (fun _ : ℕ ↦ sparseLaw)).map sample100) 0 := by
  have hsubset : Set.pi (Finset.range 100) (fun _ ↦ ({0} : Set ℝ)) ⊆
      {ω : ℕ → ℝ | sample100 ω ≤ 0} := by
    intro ω hω
    have hsum : (∑ i ∈ Finset.range 100, ω i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact mem_singleton_iff.mp (hω i hi)
    simp [sample100, normalizedSum, hsum]
  calc
    (99 / 100 : ℝ) ≤
        (Measure.infinitePi (fun _ : ℕ ↦ sparseLaw)).real
          (Set.pi (Finset.range 100) (fun _ ↦ ({0} : Set ℝ))) := allZero_probability_lower
    _ ≤ (Measure.infinitePi (fun _ : ℕ ↦ sparseLaw)).real
        {ω : ℕ → ℝ | sample100 ω ≤ 0} := measureReal_mono hsubset (measure_ne_top _ _)
    _ = cdf ((Measure.infinitePi (fun _ : ℕ ↦ sparseLaw)).map sample100) 0 := by
      rw [cdf_eq_real, map_measureReal_apply measurable_sample100 measurableSet_Iic]
      rfl

lemma sparse_catalogue_min_violation :
    ¬ (|cdf ((Measure.infinitePi (fun _ : ℕ ↦ sparseLaw)).map sample100) 0 -
        cdf (gaussianReal 0 1) 0| ≤
      (1 / Real.sqrt 100) * min (4690 / 10000 : ℝ)
        (min (∫ x, |x| ^ 3 ∂sparseLaw)
          (min ((3322 / 10000) * ((∫ x, |x| ^ 3 ∂sparseLaw) + 429 / 1000))
            ((3031 / 10000) * ((∫ x, |x| ^ 3 ∂sparseLaw) + 646 / 1000))))) := by
  intro h
  rw [standardGaussian_cdf_zero, sparseLaw_thirdMoment] at h
  rw [show (100 : ℝ) = (10 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  norm_num at h
  have hb := sparse_cdf_lower
  have ha := le_abs_self
    (cdf ((Measure.infinitePi (fun _ : ℕ ↦ sparseLaw)).map sample100) 0 - (1 / 2 : ℝ))
  linarith

theorem sparse_isStandardized : IsStandardizedLaw sparseLaw :=
  ⟨inferInstance, sparseLaw_mean, sparseLaw_variance, sparseLaw_memLp 3⟩

theorem sparse_error_lower : (49 / 100 : ℝ) ≤ kolmogorovError sparseLaw hundredSamples := by
  have hb : (99 / 100 : ℝ) ≤ cdf (normalizedLaw sparseLaw hundredSamples) 0 := sparse_cdf_lower
  have hn : normalCDF 0 = (1 / 2 : ℝ) := standardGaussian_cdf_zero
  have hd : (49 / 100 : ℝ) ≤ cdf (normalizedLaw sparseLaw hundredSamples) 0 - normalCDF 0 := by
    rw [hn]
    linarith
  exact hd.trans ((le_abs_self _).trans
    (pointwise_le_kolmogorovError sparseLaw hundredSamples 0))

theorem sparse_value_lower : (49 / 1000 : ℝ) ≤ value := by
  have hb := value_bound sparseLaw sparse_isStandardized hundredSamples
  have hroot : Real.sqrt (100 : ℝ) = 10 := by
    rw [show (100 : ℝ) = (10 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [thirdMoment, sparseLaw_thirdMoment, hundredSamples, Nat.cast_ofNat, hroot] at hb
  have he := sparse_error_lower
  linarith

theorem not_isAdmissible_zero : ¬ IsAdmissible 0 := by
  intro h
  have hu := value_le_of_isAdmissible h
  have hl := sparse_value_lower
  linarith

end MathlibExtTest.BerryEsseenSourceCorrection

#eval "C19 actual sparse law, literal-min contradiction and positive optimizer bound elaborated"
