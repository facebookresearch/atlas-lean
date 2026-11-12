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

/-!
# Continuity of the Gaussian cdf

For every real mean and every nonzero variance, the cumulative distribution
function of the Gaussian law is continuous. The degenerate zero-variance case
is a Dirac mass whose cdf jumps, so the nonzero hypothesis cannot be dropped.
The cdf also standardizes: `cdf (gaussianReal μ v) x` is the standard normal cdf
at `(x - μ) / √v`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

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

end ProbabilityTheory
