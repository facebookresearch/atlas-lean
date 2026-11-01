/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDOutlierTest

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.LDOutlierTest

namespace MathlibExtTest.Biology.StatisticalGenetics.LDOutlierTest

/-- A variant in LD `r = 0.6` with a lead variant of `z_c = 5`, observed at `z_i = 3`: exactly the
expected association `r z_c`, so `T = 0`. -/
example : dentistS 0.6 3 5 = 0 := by
  norm_num [dentistS]

/-- Observed `z_i = 1` instead: `T = (1 - 3)² / (1 - 0.36) = 6.25`. -/
example : dentistS 0.6 1 5 = 6.25 := by
  norm_num [dentistS]

/-- Junk value outside the domain: for `r² = 1` the denominator vanishes and `T = 0`. -/
example (zi zc : ℝ) : dentistS 1 zi zc = 0 := by
  simp [dentistS]

/-- With the right reference LD the standardized difference has unit variance and mean zero. -/
example : dentistVariance 0.6 0.6 = 1 ∧ dentistMean 0.6 0.6 5 = 0 :=
  ⟨(dentistVariance_eq_one_iff (by norm_num)).mpr (Or.inr rfl),
    (dentistMean_eq_zero_iff (by norm_num)).mpr (Or.inl rfl)⟩

/-- A wrong reference LD (`r = 0.8` for true `ρ = 0.6`) inflates the variance:
`(1 - 0.96 + 0.64) / (1 - 0.64) = 17/9`. -/
example : dentistVariance 0.6 0.8 = 17 / 9 := by
  norm_num [dentistVariance]

/-- Unit variance also at `r = 0` (an unlinked reference), where the mean is `ρ λ ≠ 0`. -/
example : dentistVariance 0.6 0 = 1 ∧ dentistMean 0.6 0 5 ≠ 0 := by
  refine ⟨(dentistVariance_eq_one_iff (by norm_num)).mpr (Or.inl rfl), ?_⟩
  rw [Ne, dentistMean_eq_zero_iff (by norm_num)]
  norm_num

/-- The chi-square identity. -/
example : (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) = chiSquareMeasure 1 :=
  map_sq_stdGaussian_eq_chiSquare

end MathlibExtTest.Biology.StatisticalGenetics.LDOutlierTest
