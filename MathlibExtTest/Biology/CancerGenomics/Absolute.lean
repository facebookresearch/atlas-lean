/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.CancerGenomics.Absolute
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Tests for the ABSOLUTE copy-ratio algebra: concrete copy ratios and allelic fractions, the
mean-one calibration, the slope/intercept inversion, ploidy-scaling non-identifiability, and the
junk value of a zero sample ploidy. -/

namespace MathlibExtTest.Biology.CancerGenomics.Absolute

open MathlibExt.Biology.CancerGenomics.Absolute

/-! ### Concrete values (purity `1/2`, ploidy `2`) -/

/-- A diploid locus in a diploid tumor has copy ratio `1`. -/
example : copyRatio (1 / 2) 2 2 = 1 := by norm_num [copyRatio, mixCopy]

/-- A four-copy locus: `(2 + 1) / 2 = 3 / 2`. -/
example : copyRatio (1 / 2) 2 4 = 3 / 2 := by norm_num [copyRatio, mixCopy]

/-- Slope `α / D = 1 / 4` and intercept `2 (1 - α) / D = 1 / 2`. -/
example : slope (1 / 2) 2 = 1 / 4 := by norm_num [slope, mixCopy]

example : intercept (1 / 2) 2 = 1 / 2 := by norm_num [intercept, mixCopy]

/-- A clonal single-copy mutation at a diploid locus: allelic fraction `1 / 4` (Eq. 10). -/
example : somaticAF (1 / 2) 2 1 = 1 / 4 := by norm_num [somaticAF, mixCopy]

/-- A heterozygous germline variant at a diploid locus stays at `1 / 2` (Eq. 11). -/
example : germlineAF (1 / 2) 2 1 = 1 / 2 := by norm_num [germlineAF, mixCopy]

/-- Eq. 1 recovered from the slope and intercept. -/
example : copyRatio (1 / 2) 2 4 = slope (1 / 2) 2 * 4 + intercept (1 / 2) 2 :=
  copyRatio_eq_slope_mul_add_intercept _ _ _

/-! ### Calibration: two equal segments of copy number `1` and `3` -/

example : ∑ i : Fin 2, (1 / 2 : ℝ) * copyRatio (1 / 2) (∑ j : Fin 2, (1 / 2 : ℝ) * ![1, 3] j)
    (![1, 3] i) = 1 :=
  sum_mul_copyRatio_eq_one Finset.univ (fun _ => 1 / 2) ![1, 3] (by norm_num)
    (by norm_num [mixCopy, Fin.sum_univ_two])

/-! ### Inversion of Eq. 1 -/

example : (1 / 2 : ℝ) = 2 * slope (1 / 2) 2 / (2 * slope (1 / 2) 2 + intercept (1 / 2) 2) :=
  purity_eq (by norm_num) (by norm_num) (by norm_num)

example : (2 : ℝ) = (1 - intercept (1 / 2) 2) / slope (1 / 2) 2 :=
  ploidy_eq (by norm_num) (by norm_num) (by norm_num)

/-- The image point `(1/4, 1/2)` lies in the target set of the bijection. -/
example : ((slope (1 / 2) 2, intercept (1 / 2) 2) : ℝ × ℝ) ∈
    {x : ℝ × ℝ | 0 < x.1 ∧ 0 ≤ x.2 ∧ x.2 < 1} :=
  bijOn_slope_intercept.mapsTo (show ((1 / 2 : ℝ), (2 : ℝ)) ∈ _ by norm_num)

/-! ### Genome doubling -/

/-- Purity `1/2`, ploidy `2`, copy number `3` and purity `1/3`, ploidy `4`, copy number `6`
give the same copy ratio `5 / 4`. -/
example : copyRatio (1 / 3) 4 6 = copyRatio (1 / 2) 2 3 := by
  norm_num [copyRatio, mixCopy]

example : copyRatio (1 / 2 / (2 - 1 / 2)) (2 * 2) (2 * 3) = copyRatio (1 / 2) 2 3 :=
  copyRatio_doubling (by norm_num) (by norm_num) 2 3

example : somaticAF (scaledPurity 2 (1 / 2)) (2 * 3) (2 * 1) = somaticAF (1 / 2) 3 1 :=
  somaticAF_scale two_pos (by norm_num) (by norm_num) 3 1

example : germlineAF (scaledPurity 3 (1 / 2)) (3 * 2) (3 * 1) = germlineAF (1 / 2) 2 1 :=
  germlineAF_scale (by norm_num) (by norm_num) (by norm_num) 2 1

/-- The doubled solution has a different purity, `1/3 ≠ 1/2`. -/
example : scaledPurity 2 (1 / 2) ≠ 1 / 2 :=
  scaledPurity_ne two_pos (by norm_num) (by norm_num) (by norm_num)

example : scaledPurity 2 (1 / 2) = 1 / 3 := by norm_num [scaledPurity]

/-! ### Monotonicity and boundary cases -/

example : somaticAF (1 / 4) 2 1 ≤ somaticAF (1 / 2) 2 1 :=
  somaticAF_mono_purity (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A pure tumor (`α = 1`): a heterozygous clonal mutation at copy number `2` has fraction
`1 / 2`. -/
example : somaticAF 1 2 1 = 1 / 2 := by norm_num [somaticAF, mixCopy]

/-- Outside the domain (`α = 1`, `τ = 0`) the sample ploidy is `0` and Lean's `x / 0 = 0` makes
the copy ratio a junk `0`; every theorem above excludes this case. -/
example : copyRatio 1 0 3 = 0 := by norm_num [copyRatio, mixCopy]

end MathlibExtTest.Biology.CancerGenomics.Absolute
