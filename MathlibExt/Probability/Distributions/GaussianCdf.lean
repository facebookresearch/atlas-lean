/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CdfContinuityPoints
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Continuity of the Gaussian cdf

For every real mean and every nonzero variance, the cumulative distribution
function of the Gaussian law is continuous. The degenerate zero-variance case
is a Dirac mass whose cdf jumps, so the nonzero hypothesis cannot be dropped.
The cdf also standardizes: `cdf (gaussianReal μ v) x` is the standard normal cdf
at `(x - μ) / √v`. The standard normal cdf is symmetric: `Φ(-x) = 1 - Φ(x)`,
hence `Φ 0 = 1 / 2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ProbabilityTheory ENNReal NNReal

namespace MathlibExt.Probability.BerryEsseenWanted

private lemma map_neg_gaussianReal_std :
    Measure.map (fun x : ℝ => -x) (gaussianReal 0 (1 : ℝ≥0)) = gaussianReal 0 1 := by
  rw [gaussianReal_map_neg]
  simp

private lemma neg_preimage_Iic_neg (w : ℝ) :
    (fun x : ℝ => -x) ⁻¹' (Set.Iic (-w)) = Set.Ici w := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici, neg_le_neg_iff]

private lemma gaussianReal_Iio_eq_Iic (w : ℝ) :
    (gaussianReal 0 (1 : ℝ≥0)).real (Set.Iio w)
      = (gaussianReal 0 1).real (Set.Iic w) := by
  have h1 : Set.Iic w = Set.Iio w ∪ {w} := by
    ext x
    simp only [Set.mem_Iic, Set.mem_Iio, Set.mem_union, Set.mem_singleton_iff,
      le_iff_lt_or_eq]
  have hnull : (gaussianReal 0 (1 : ℝ≥0)).real {w} = 0 := by
    have h0 : (gaussianReal 0 (1 : ℝ≥0)) {w} = 0 :=
      @NullSingletonClass.measure_singleton _ _ _
        (nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) one_ne_zero) w
    unfold Measure.real
    rw [h0]
    exact ENNReal.toReal_zero
  have hdisj : Disjoint (Set.Iio w) ({w} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_Iio] at hx1
    rw [Set.mem_singleton_iff] at hx2
    rw [hx2] at hx1
    exact absurd hx1 (lt_irrefl _)
  have h2 : (gaussianReal 0 (1 : ℝ≥0)).real (Set.Iio w ∪ {w})
      = (gaussianReal 0 1).real (Set.Iio w) := by
    rw [measureReal_union hdisj (measurableSet_singleton w)
      (measure_ne_top _ _) (measure_ne_top _ _), hnull, add_zero]
  rw [← h1] at h2
  exact h2.symm

end MathlibExt.Probability.BerryEsseenWanted

namespace ProbabilityTheory

/-- The cdf of a Gaussian law with nonzero variance is continuous. -/
theorem continuous_cdf_gaussianReal (μ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Continuous (cdf (gaussianReal μ v)) := by
  have hnull := nullSingletonClass_gaussianReal (μ := μ) hv
  rw [continuous_iff_continuousAt]
  intro x
  rw [MathlibExt.Probability.CdfContinuityPoints.continuousAt_cdf_iff_measure_singleton_eq_zero]
  exact @measure_singleton _ _ _ hnull x

/-- Standardization: the cdf of `N(μ, v)` is the standard normal cdf at `(x - μ) / √v`. -/
theorem cdf_gaussianReal_eq_std (μ x : ℝ) {v : NNReal} (hv : v ≠ 0) :
    cdf (gaussianReal μ v) x
      = cdf (gaussianReal 0 1) ((x - μ) / Real.sqrt (v : ℝ)) := by
  have hvr : (0:ℝ) < (v:ℝ) := by
    have h : (0:NNReal) < v := pos_iff_ne_zero.mpr hv
    exact_mod_cast h
  have hc : 0 < Real.sqrt (v:ℝ) := Real.sqrt_pos.mpr hvr
  have hsub : Measurable (fun y : ℝ => y - μ) := measurable_id.sub_const _
  have hdiv : Measurable (fun z : ℝ => z / Real.sqrt (v:ℝ)) := measurable_id.div_const _
  have hmeas : Measurable (fun y : ℝ => (y - μ) / Real.sqrt (v:ℝ)) :=
    (measurable_id.sub_const _).div_const _
  have hsq : Real.sqrt (v:ℝ) ^ 2 = (v:ℝ) := Real.sq_sqrt (le_of_lt hvr)
  have hmk : ∀ h : 0 ≤ Real.sqrt (v:ℝ) ^ 2, NNReal.mk (Real.sqrt (v:ℝ) ^ 2) h = v :=
    fun h => Subtype.ext hsq
  have hmap : Measure.map (fun y : ℝ => (y - μ) / Real.sqrt (v:ℝ)) (gaussianReal μ v)
      = gaussianReal 0 1 := by
    rw [show (fun y : ℝ => (y - μ) / Real.sqrt (v:ℝ))
        = (fun z : ℝ => z / Real.sqrt (v:ℝ)) ∘ (fun y : ℝ => y - μ) from rfl,
      ← Measure.map_map hdiv hsub, gaussianReal_map_sub_const, gaussianReal_map_div_const,
      sub_self, zero_div, hmk _, div_self hv]
  have hpre : (fun y : ℝ => (y - μ) / Real.sqrt (v:ℝ)) ⁻¹'
      (Set.Iic ((x - μ) / Real.sqrt (v:ℝ))) = Set.Iic x := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [div_le_iff₀ hc, div_mul_cancel₀ _ (ne_of_gt hc)]
    exact sub_le_sub_iff_right μ
  simp only [cdf_eq_real]
  rw [← hmap, map_measureReal_apply hmeas measurableSet_Iic, hpre]

/-- Symmetry of the standard normal cdf. -/
theorem cdf_gaussianReal_neg (x : ℝ) :
    cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  rw [cdf_eq_real, cdf_eq_real]
  have hmap := MathlibExt.Probability.BerryEsseenWanted.map_neg_gaussianReal_std
  have hpre := MathlibExt.Probability.BerryEsseenWanted.neg_preimage_Iic_neg x
  have hIio := MathlibExt.Probability.BerryEsseenWanted.gaussianReal_Iio_eq_Iic x
  have hmeas : Measurable (fun x : ℝ => -x) := by fun_prop
  have hIic : MeasurableSet (Set.Iic (-x)) := measurableSet_Iic
  have hIio_meas : MeasurableSet (Set.Iio x) := measurableSet_Iio
  calc (gaussianReal 0 1).real (Set.Iic (-x))
      = (Measure.map (fun x : ℝ => -x) (gaussianReal 0 1)).real (Set.Iic (-x)) := by
          rw [hmap]
    _ = (gaussianReal 0 1).real ((fun x : ℝ => -x) ⁻¹' (Set.Iic (-x))) := by
          rw [map_measureReal_apply hmeas hIic]
    _ = (gaussianReal 0 1).real (Set.Ici x) := by rw [hpre]
    _ = (gaussianReal 0 1).real (Set.Iio x)ᶜ := by rw [Set.compl_Iio]
    _ = (gaussianReal 0 1).real Set.univ - (gaussianReal 0 1).real (Set.Iio x) := by
          rw [measureReal_compl hIio_meas]
    _ = 1 - (gaussianReal 0 1).real (Set.Iio x) := by rw [probReal_univ]
    _ = 1 - (gaussianReal 0 1).real (Set.Iic x) := by rw [hIio]

/-- Corollary: the standard normal cdf at `0` is `1 / 2`. -/
theorem cdf_gaussianReal_zero :
    cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have h := cdf_gaussianReal_neg 0
  simp at h
  linarith

end ProbabilityTheory
