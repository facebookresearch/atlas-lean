/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp

/-!
# Sound intensity levels

## i. Overview

Sound intensity level in decibels is `10 * log10 (I / Iref)` against a
reference intensity. Levels are physically meaningful only for positive
intensities in the same unit; outside that domain the totalized
`Real.logb` values have no physical interpretation. Level differences are independent of the reference,
and `N` equal incoherent sources (total intensity the sum of the equal
intensities, as a stated premise) raise the level by `10 * log10 N`.

## ii. Key results

- `Acoustics.intensityLevel_sub_eq`: referenced level differences equal
  the direct level difference.
- `Acoustics.intensityLevelDifference_equal_sources`: equal-source
  level increase.

## iii. Table of contents

- A. Levels and level differences

## iv. References

- L. E. Kinsler, A. R. Frey, A. B. Coppens and J. V. Sanders,
  *Fundamentals of Acoustics*, 4th edition, Wiley, 2000.
-/

@[expose] public section

namespace Acoustics

/-! ## A. Levels and level differences -/

/-- Sound intensity level of intensity `I` against reference intensity
`Iref`, in decibels: `10 * log10 (I / Iref)`. Physically meaningful only
for positive `Iref` and `I` in the same unit; the totalized `Real.logb`
value outside that domain (for example at `I = 0`) is not a level. -/
noncomputable def intensityLevel (Iref I : ℝ) : ℝ :=
  10 * Real.logb 10 (I / Iref)

/-- Sound intensity level difference in decibels between intensities
`I2` and `I1`: `10 * log10 (I2 / I1)`, for positive intensities in the
same unit. -/
noncomputable def intensityLevelDifference (I1 I2 : ℝ) : ℝ :=
  10 * Real.logb 10 (I2 / I1)

/-- The referenced level difference is the difference of referenced
levels, independent of the reference. -/
theorem intensityLevel_sub_eq {Iref I1 I2 : ℝ}
    (hIref : 0 < Iref) (hI1 : 0 < I1) (hI2 : 0 < I2) :
    intensityLevel Iref I2 - intensityLevel Iref I1
      = intensityLevelDifference I1 I2 := by
  unfold intensityLevel intensityLevelDifference
  have hIref' : Iref ≠ 0 := ne_of_gt hIref
  have hI1' : I1 ≠ 0 := ne_of_gt hI1
  have hI2' : I2 ≠ 0 := ne_of_gt hI2
  have ha : I2 / Iref ≠ 0 := div_ne_zero hI2' hIref'
  have hb : I1 / Iref ≠ 0 := div_ne_zero hI1' hIref'
  have hdiv : (I2 / Iref) / (I1 / Iref) = I2 / I1 := by field_simp
  rw [← hdiv, Real.logb_div ha hb]
  ring

/-- Level increase from `N` equal incoherent sources, where incoherent
addition of the equal intensities is the stated total `Itot`. -/
theorem intensityLevelDifference_equal_sources {I Itot : ℝ} {N : ℕ}
    (hI : 0 < I) (hN : 0 < N)
    (hsum : Itot = ∑ _i ∈ Finset.range N, I) :
    intensityLevelDifference I Itot = 10 * Real.logb 10 (N : ℝ) := by
  unfold intensityLevelDifference
  have _hN : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hI' : I ≠ 0 := ne_of_gt hI
  have hsum' : Itot = (N : ℝ) * I := by
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hdiv : Itot / I = (N : ℝ) := by
    rw [hsum']
    field_simp
  rw [hdiv]

end Acoustics
