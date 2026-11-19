/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.InfiniteSlope
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Infinite-slope safety-ratio checks

Concrete consumers of the safety-ratio admission in
`PhyslibExt.EarthScience.Geotechnical.InfiniteSlope`: the
textbook dry-slope factor `c / τd + tan φ / tan β`, sign
controls off the genuine-slope domain, and the effective
normal stress on a non-unit normal.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Safety ratio and controls

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.InfiniteSlope`
-/

open EarthScience
open scoped Matrix

namespace PhyslibExtTest.EarthScience.Geotechnical.InfiniteSlope

/-! ## A. Safety ratio and controls -/

/-- Textbook dry-slope form at zero pore pressure: the
Mohr–Coulomb safety ratio is `c / τd + tan φ / tan β`. -/
example {c phi gamma z beta : ℝ} (hgamma : 0 < gamma) (hz : 0 < z)
    (hbeta0 : 0 < beta) (hbeta : beta < Real.pi / 2) :
    infiniteSlopeSafetyRatio
        (infiniteSlopeResistingStress c phi gamma z beta 0) gamma z beta
      = c / infiniteSlopeDrivingStress gamma z beta
        + Real.tan phi / Real.tan beta := by
  have hpos := infiniteSlopeDrivingStress_pos hgamma hz hbeta0 hbeta
  have htan := infiniteSlopeDriving_eq_normal_mul_tan hbeta0 hbeta
    (gamma := gamma) (z := z)
  unfold infiniteSlopeSafetyRatio infiniteSlopeResistingStress
  rw [sub_zero, add_div, htan]
  have hγz : gamma * z ≠ 0 := mul_ne_zero hgamma.ne' hz.ne'
  have hcos : Real.cos beta ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hbeta⟩).ne'
  have hsin : Real.sin beta ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hbeta0 (by linarith [Real.pi_pos])).ne'
  have hN : infiniteSlopeNormalStress gamma z beta ≠ 0 := by
    unfold infiniteSlopeNormalStress
    exact mul_ne_zero hγz (pow_ne_zero 2 hcos)
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  field_simp [hN]

/-- Sign control: with negative unit weight the driving
stress at `β = π / 4` is negative, off the admission domain. -/
example : infiniteSlopeDrivingStress (-1) 1 (Real.pi / 4) < 0 := by
  unfold infiniteSlopeDrivingStress
  have hsin : 0 < Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]
    positivity
  have hcos : 0 < Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four]
    positivity
  nlinarith [mul_pos hsin hcos]

/-- Endpoint control: at `β = 0` there is no driving stress. -/
example (gamma z : ℝ) : infiniteSlopeDrivingStress gamma z 0 = 0 := by
  simp [infiniteSlopeDrivingStress]

/-- The bridge on a non-unit normal scales: for `v = (2, 0)`
the identity with `hv : v ⬝ᵥ v = 4` is not the unit-normal
statement; the unit normal `(1, 0)` recovers `σn - u`. -/
example (u : ℝ) :
    (![1, 0] : Fin 2 → ℝ) ⬝ᵥ
        (effectiveStressCompressionPositive
          (!![10, 3; 5, 7] : Matrix (Fin 2) (Fin 2) ℝ) u *ᵥ ![1, 0])
      = 10 - u := by
  have h := effectiveNormalStress_eq
    (!![10, 3; 5, 7] : Matrix (Fin 2) (Fin 2) ℝ) u ![1, 0] (by
      simp [dotProduct, Fin.sum_univ_two])
  rw [h]
  simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.of_apply]

#print axioms EarthScience.infiniteSlopeDrivingStress_pos
#print axioms EarthScience.infiniteSlopeSafetyRatio_admission
#print axioms EarthScience.infiniteSlope_mohrCoulomb_admission
#print axioms EarthScience.effectiveNormalStress_eq

end PhyslibExtTest.EarthScience.Geotechnical.InfiniteSlope
