/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.ClassicalMechanics.Acoustics.Levels

/-!
# Pressure and intensity level compatibility

## i. Overview

With intensity `I = p_rms ^ 2 / Z` and reference intensity
`I_ref = p_ref ^ 2 / Z` at the same positive impedance `Z`, the
intensity level `10 * log10 (I / I_ref)` equals the pressure level
`20 * log10 (p_rms / p_ref)`: the impedance cancels and the square
contributes the factor of two. Both the measurement and reference
relations are required; a mismatched reference impedance breaks
the identity.

## ii. Key results

- `Acoustics.intensityLevel_eq_pressureLevel`: intensity level
  equals the 20-log pressure level at matched impedance.

## iii. Table of contents

- A. Pressure and intensity levels

## iv. References

- L. E. Kinsler, A. R. Frey, A. B. Coppens and J. V. Sanders,
  *Fundamentals of Acoustics*, 4th edition, Wiley, 2000
  (intensity level and sound pressure level at a common
  characteristic impedance).
-/

@[expose] public section

namespace Acoustics

/-! ## A. Pressure and intensity levels -/

/-- Intensity level equals the 20-log pressure level at matched
impedance. -/
theorem intensityLevel_eq_pressureLevel {p_rms p_ref Z : ℝ}
    (hp : 0 < p_rms) (hpref : 0 < p_ref) (hZ : 0 < Z) :
    intensityLevel (p_ref ^ 2 / Z) (p_rms ^ 2 / Z)
      = 20 * Real.logb 10 (p_rms / p_ref) := by
  unfold intensityLevel
  have hZ' : Z ≠ 0 := ne_of_gt hZ
  have hpref' : p_ref ≠ 0 := ne_of_gt hpref
  have hsq : p_ref ^ 2 ≠ 0 := pow_ne_zero 2 hpref'
  have hden : p_ref ^ 2 / Z ≠ 0 := div_ne_zero hsq hZ'
  have hdiv : (p_rms ^ 2 / Z) / (p_ref ^ 2 / Z) = (p_rms / p_ref) ^ 2 := by
    field_simp
  rw [hdiv, Real.logb_pow]
  push_cast
  ring

end Acoustics
