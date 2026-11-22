/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianShift

/-!
# Tests for translates and affine images of the standard Gaussian

* Half-space law: `P(⟪Z, v⟫ ≤ 0) = 1/2`; at `v = 0` the formula fails (`1 ≠ Φ(1 / 0) = 1/2`), so
  `v ≠ 0` is necessary.
* The shift bound is sharp: for a unit vector `u`, the half-space `A = {⟪z, u⟫ ≤ s}` and the
  shift `v = r u` (`r ≥ 0`), `P(Z + v ∈ A) = Φ(Φ⁻¹ P(Z ∈ A) - ‖v‖)`.
* Both shift bounds instantiated at `p = 1/2` on `{⟪z, u⟫ ≤ 0}`.
* Affine law: `x = 0`, `σ = 1` recovers Mathlib's `multivariateGaussian 0 1 = stdGaussian`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExtTest.Probability.Distributions.GaussianShift

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

variable {ι : Type*} [Fintype ι]

/-- Use: a half-space through the origin has probability `1/2`. -/
example {v : EuclideanSpace ℝ ι} (hv : v ≠ 0) :
    (stdGaussian (EuclideanSpace ℝ ι)).real {z | ⟪z, v⟫ ≤ 0} = 1 / 2 := by
  rw [stdGaussian_real_inner_le hv, zero_div, cdf_gaussianReal_zero]

/-- Boundary: for `v = 0` the half-space `{⟪z, 0⟫ ≤ 1}` is everything, while the formula would
give `Φ(1 / ‖0‖) = Φ 0 = 1/2`; `v ≠ 0` cannot be dropped. -/
example : (stdGaussian (EuclideanSpace ℝ ι)).real {z | ⟪z, (0 : EuclideanSpace ℝ ι)⟫ ≤ 1} ≠
    cdf (gaussianReal 0 1) (1 / ‖(0 : EuclideanSpace ℝ ι)‖) := by
  simp [cdf_gaussianReal_zero]

/-- **Sharpness**: half-spaces attain `stdGaussian_shift_lower`. -/
theorem shift_halfSpace {u : EuclideanSpace ℝ ι} (hu : ‖u‖ = 1) (s : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (stdGaussian (EuclideanSpace ℝ ι)).real {z | z + r • u ∈ {w | ⟪w, u⟫ ≤ s}} =
      cdf (gaussianReal 0 1) (cdfQuantile (gaussianReal 0 1)
        ((stdGaussian (EuclideanSpace ℝ ι)).real {w | ⟪w, u⟫ ≤ s}) - ‖r • u‖) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hset : {z | z + r • u ∈ {w | ⟪w, u⟫ ≤ s}} = {z : EuclideanSpace ℝ ι | ⟪z, u⟫ ≤ s - r} := by
    ext z
    simp only [mem_ofPred_eq, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
    constructor <;> intro h <;> linarith
  rw [hset, stdGaussian_real_inner_le hu0, stdGaussian_real_inner_le hu0, hu, div_one, div_one,
    cdfQuantile_cdf_of_strictMono _ (strictMono_cdf_gaussianReal 0 one_ne_zero), norm_smul, hu,
    mul_one, Real.norm_of_nonneg hr]

private theorem cdfQuantile_half : cdfQuantile (gaussianReal 0 1) (1 / 2) = 0 := by
  rw [← cdf_gaussianReal_zero,
    cdfQuantile_cdf_of_strictMono _ (strictMono_cdf_gaussianReal 0 one_ne_zero)]

/-- Use: both shift bounds on the half-space `{⟪z, u⟫ ≤ 0}` of probability `1/2`:
`Φ(-‖v‖) ≤ P(Z + v ∈ A) ≤ Φ(‖v‖)`. -/
example {u : EuclideanSpace ℝ ι} (hu : u ≠ 0) (v : EuclideanSpace ℝ ι) :
    cdf (gaussianReal 0 1) (-‖v‖) ≤
        (stdGaussian (EuclideanSpace ℝ ι)).real {z | z + v ∈ {w | ⟪w, u⟫ ≤ 0}} ∧
      (stdGaussian (EuclideanSpace ℝ ι)).real {z | z + v ∈ {w | ⟪w, u⟫ ≤ 0}} ≤
        cdf (gaussianReal 0 1) ‖v‖ := by
  have hA : MeasurableSet {w : EuclideanSpace ℝ ι | ⟪w, u⟫ ≤ 0} :=
    measurableSet_le (by fun_prop) measurable_const
  have hP : (stdGaussian (EuclideanSpace ℝ ι)).real {w | ⟪w, u⟫ ≤ 0} = 1 / 2 := by
    rw [stdGaussian_real_inner_le hu, zero_div, cdf_gaussianReal_zero]
  have hp : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hlo := stdGaussian_shift_lower hA v hp hP.ge
  have hhi := stdGaussian_shift_upper hA v hp hP.le
  rw [cdfQuantile_half, zero_sub] at hlo
  rw [cdfQuantile_half, zero_add] at hhi
  exact ⟨hlo, hhi⟩

/-- Use: `x = 0`, `σ = 1` recovers `multivariateGaussian 0 1 = stdGaussian`. -/
example [DecidableEq ι] :
    multivariateGaussian (0 : EuclideanSpace ℝ ι) 1 = stdGaussian (EuclideanSpace ℝ ι) := by
  have h := stdGaussian_map_const_add_smul (0 : EuclideanSpace ℝ ι) 1
  simp only [zero_add, one_smul, one_pow, Measure.map_id'] at h
  exact h.symm

end MathlibExtTest.Probability.Distributions.GaussianShift

#print axioms ProbabilityTheory.stdGaussian_map_const_add_smul
#print axioms ProbabilityTheory.stdGaussian_real_inner_le
#print axioms ProbabilityTheory.stdGaussian_shift_lower
#print axioms ProbabilityTheory.stdGaussian_shift_upper
#print axioms MathlibExtTest.Probability.Distributions.GaussianShift.shift_halfSpace
