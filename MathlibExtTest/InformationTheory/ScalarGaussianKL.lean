/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ScalarGaussianKL
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open MathlibExt.InformationTheory.ScalarGaussianKL
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.ScalarGaussianKL

/-- Equal laws: `KL(N(3, 2) ‖ N(3, 2)) = 0`, and the closed form agrees. -/
example :
    klDiv (gaussianReal 3 2) (gaussianReal 3 2) = 0 ∧
      ENNReal.ofReal (scalarGaussianKLReal 3 3 2 2) = 0 :=
  klDiv_gaussianReal_self 3 2 (by norm_num)

/-- Shifted equal variance: `KL(N(1, 3) ‖ N(4, 3)) = (1 - 4)² / (2 · 3) = 3 / 2`. -/
example : klDiv (gaussianReal 1 3) (gaussianReal 4 3) = ENNReal.ofReal (3 / 2) := by
  rw [klDiv_gaussianReal_same_variance 1 4 3 (by norm_num)]
  norm_num

/-- The general formula at a common variance agrees with the shifted equal-variance value. -/
example : klDiv (gaussianReal 1 3) (gaussianReal 4 3) =
    ENNReal.ofReal (scalarGaussianKLReal 1 4 3 3) :=
  klDiv_gaussianReal 1 4 3 3 (by norm_num) (by norm_num)

/-- Different variances: `KL(N(0, 1) ‖ N(0, 2)) = (log 2 - 1 / 2) / 2`. -/
example :
    klDiv (gaussianReal 0 1) (gaussianReal 0 2) = ENNReal.ofReal ((Real.log 2 - 1 / 2) / 2) := by
  rw [klDiv_gaussianReal 0 0 1 2 (by norm_num) (by norm_num)]
  norm_num [scalarGaussianKLReal]
  congr 1
  ring

/-- The value `(log 2 - 1 / 2) / 2` of `KL(N(0, 1) ‖ N(0, 2))` is strictly positive. -/
example : 0 < scalarGaussianKLReal 0 0 1 2 := by
  have h := Real.log_two_gt_d9
  norm_num [scalarGaussianKLReal]
  linarith

/-- Real-parameter form at `N(0, 1)` and `N(0, 2)`, in the form `(log 2 - 1 + 1 / 2) / 2` that the
vector closed form gives at dimension one. -/
example :
    klDiv (gaussianReal 0 ⟨1, zero_lt_one.le⟩) (gaussianReal 0 ⟨2, zero_lt_two.le⟩) =
      ENNReal.ofReal ((Real.log 2 - 1 + 1 / 2) / 2) := by
  rw [klDiv_gaussianReal_of_pos 0 0 1 2 zero_lt_one zero_lt_two]
  norm_num [scalarGaussianKLReal]
  congr 1
  ring

/-- Zero first variance: `KL(N(0, 0) ‖ N(0, 1)) = ∞`, while the closed form is finite. -/
example :
    klDiv (gaussianReal 0 0) (gaussianReal 0 1) = ∞ ∧
      klDiv (gaussianReal 0 0) (gaussianReal 0 1) ≠
        ENNReal.ofReal (scalarGaussianKLReal 0 0 0 1) :=
  ⟨klDiv_gaussianReal_zero_variance 0 0 1 (by norm_num),
    klDiv_gaussianReal_zero_variance_ne 0 0 1 (by norm_num)⟩

end MathlibExtTest.InformationTheory.ScalarGaussianKL
