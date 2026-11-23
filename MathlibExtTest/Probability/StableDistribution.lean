/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.StableDistribution

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal
open MathlibExt.Probability.StableDistribution

namespace MathlibExtTest.Probability.StableDistribution

/-- The Dirac measure at `0` satisfies the degenerate index-one rescaling identity. -/
example : IsStable (dirac (0 : ℝ)) 1 :=
  isStable_dirac 0 one_pos (by norm_num)

/-- The Dirac measure at `3` satisfies the degenerate index-two rescaling identity. -/
example : IsStable (dirac (3 : ℝ)) 2 :=
  isStable_dirac 3 (by norm_num) (by norm_num)

/-- The standard Gaussian is stable of index `2`. -/
example : IsStable (gaussianReal 0 1) 2 :=
  isStable_gaussianReal 0 1

/-- A general Gaussian `N(μ, v)` is stable of index `2`. -/
example (μ : ℝ) (v : ℝ≥0) : IsStable (gaussianReal μ v) 2 :=
  isStable_gaussianReal μ v

/-- The two-fold convolution power of `δ_a` is `δ_{2a}`. -/
example (a : ℝ) : Measure.convPow (dirac a) 2 = dirac (2 * a) := by
  rw [Measure.convPow_dirac]
  simp only [nsmul_eq_mul]
  norm_num

/-- The two-fold convolution power of `N(μ, v)` is `N(2μ, 2v)`. -/
example (μ : ℝ) (v : ℝ≥0) :
    Measure.convPow (gaussianReal μ v) 2 = gaussianReal (2 * μ) (2 * v) := by
  rw [convPow_gaussianReal]
  norm_num

/-- The standard Gaussian is nondegenerate. -/
example : IsNondegenerate (gaussianReal 0 1) :=
  isNondegenerate_gaussianReal one_ne_zero

/-- A Gaussian with variance `2` is nondegenerate. -/
example : IsNondegenerate (gaussianReal (-1 : ℝ) 2) :=
  isNondegenerate_gaussianReal (by norm_num)

/-- The Dirac measure is degenerate: it is a point mass. -/
example (a : ℝ) : ¬ IsNondegenerate (dirac a) :=
  not_isNondegenerate_dirac a

/-- The zero-variance Gaussian is a Dirac measure, hence degenerate. -/
example (μ : ℝ) : ¬ IsNondegenerate (gaussianReal μ 0) := by
  rw [gaussianReal_zero_var]
  exact not_isNondegenerate_dirac μ

/-- The Dirac measure is in its own domain of attraction. -/
example (a : ℝ) : InDomainOfAttraction (dirac a) (dirac a) :=
  inDomainOfAttraction_dirac a

/-- The old chosen Dirac limit cannot witness index one after nondegeneracy is required. -/
example (a : ℝ) :
    ¬ (IsStable (dirac a) 1 ∧ IsNondegenerate (dirac a) ∧
      InDomainOfAttraction (dirac a) (dirac a)) :=
  fun h => not_isNondegenerate_dirac a h.2.1

/-- The same old chosen witness is excluded at index two. -/
example (a : ℝ) :
    ¬ (IsStable (dirac a) 2 ∧ IsNondegenerate (dirac a) ∧
      InDomainOfAttraction (dirac a) (dirac a)) :=
  fun h => not_isNondegenerate_dirac a h.2.1

/-- Independent exact n=4 convolution control for the standard Gaussian. -/
theorem characterization_gaussian_convolution_four :
    Measure.convPow (gaussianReal 0 1) 4 = gaussianReal 0 4 := by
  rw [convPow_gaussianReal]
  norm_num

/-- Fixed dilation four gives variance sixteen for every centering. -/
theorem characterization_gaussian_affine_four (b : ℝ) :
    (gaussianReal 0 1).map (fun x => 4 * x + b) = gaussianReal b 16 := by
  have hmap : (gaussianReal 0 1).map (fun x => 4 * x + b) =
      ((gaussianReal 0 1).map (fun x => 4 * x)).map (fun y => y + b) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmap, gaussianReal_map_const_mul, gaussianReal_map_add_const]
  norm_num
  congr 1

/-- The two exact laws differ, independently of the old stability definition. -/
theorem characterization_gaussian_four_not_affine_one (b : ℝ) :
    Measure.convPow (gaussianReal 0 1) 4 ≠
      (gaussianReal 0 1).map (fun x => 4 * x + b) := by
  rw [characterization_gaussian_convolution_four, characterization_gaussian_affine_four]
  intro h
  have hv := (gaussianReal_ext_iff.mp h).2
  norm_num at hv

end MathlibExtTest.Probability.StableDistribution
