/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Laplace

/-!
# Tests for the Laplace distribution

* The density at the location is `1 / (2 b)`.
* The standard Laplace law has total mass one, and so does every translate and rescaling.
* Moving the location by `1` with scale `2` changes the law by a factor at most `exp (1 / 2)`.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Distributions.Laplace

open MeasureTheory ProbabilityTheory

example (m b : ℝ) : laplacePDFReal m b m = 1 / (2 * b) := by
  simp [laplacePDFReal]

example : laplaceMeasure 0 1 Set.univ = 1 :=
  (isProbabilityMeasure_laplaceMeasure one_pos 0).measure_univ

example (m : ℝ) : ∫ z, laplacePDFReal m 3 z = 1 :=
  integral_laplacePDFReal (by norm_num) m

example : laplaceMeasure 1 2 ≤ ENNReal.ofReal (Real.exp (1 / 2)) • laplaceMeasure 0 2 := by
  simpa using laplaceMeasure_le_smul (b := 2) two_pos 1 0

end MathlibExtTest.Probability.Distributions.Laplace
