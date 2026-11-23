/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Declared Friis link

## i. Overview

A declared far-field free-space link: flux
`S = Pt Gt / (4π r²)`, receiving aperture `Ae = Gr λ² / (4π)`,
and matched received power `Pr = S Ae`. Composing the three
declared relations gives the Friis formula
`Pr = Pt Gt Gr (λ / (4π r))²`. The ratio form is stated only for
positive transmit power.

## ii. Key results

- `receivedPower_eq_friis`: the Friis received-power formula.
- `receivedPower_div_transmitPower_eq_friis`: the ratio form
  for `Pt > 0`.

## iii. Table of contents

- A. The declared Friis link

## iv. References

- C. A. Balanis, *Antenna Theory: Analysis and Design*, fourth
  edition, Wiley, 2016: the Friis transmission equation.

## A. The declared Friis link

-/

@[expose] public section

open Real
namespace PhyslibExt.Electromagnetism.DeclaredFriisLink

/-! ### Headline -/

/-- **Declared Friis link.** From the declared far-field free-space flux `S = Pt Gt / (4π r²)`, the
effective aperture `Ae = Gr λ² / (4π)` and the polarization-matched, impedance-matched received
power `Pr = S Ae`, the received power is `Pr = Pt Gt Gr (λ / (4π r))²`. -/
lemma receivedPower_eq_friis {Pt Gt Gr r lam S Ae Pr : ℝ} (hr : 0 < r) (hlam : 0 < lam)
    (hPt : 0 ≤ Pt) (hGt : 0 ≤ Gt) (hGr : 0 ≤ Gr) (hS : S = Pt * Gt / (4 * π * r ^ 2))
    (hAe : Ae = Gr * lam ^ 2 / (4 * π)) (hPr : Pr = S * Ae) :
    Pr = Pt * Gt * Gr * (lam / (4 * π * r)) ^ 2 := by
  have hd1 : (4 : ℝ) * π * r ^ 2 ≠ 0 := by positivity
  have hd2 : (4 : ℝ) * π ≠ 0 := by positivity
  have hd3 : (4 : ℝ) * π * r ≠ 0 := by positivity
  rw [hPr, hS, hAe, div_pow]
  field_simp

/-- **Declared Friis power ratio**, stated only for `Pt > 0`:
`Pr / Pt = Gt Gr (λ / (4π r))²`. -/
lemma receivedPower_div_transmitPower_eq_friis {Pt Gt Gr r lam S Ae Pr : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hPt : 0 < Pt) (hGt : 0 ≤ Gt) (hGr : 0 ≤ Gr)
    (hS : S = Pt * Gt / (4 * π * r ^ 2)) (hAe : Ae = Gr * lam ^ 2 / (4 * π))
    (hPr : Pr = S * Ae) :
    Pr / Pt = Gt * Gr * (lam / (4 * π * r)) ^ 2 := by
  have h := receivedPower_eq_friis hr hlam (le_of_lt hPt) hGt hGr hS hAe hPr
  have hPt0 : Pt ≠ 0 := ne_of_gt hPt
  rw [h]
  field_simp

/-! ### Validation -/

/-- Validation, `Pt = 0` in the multiplicative formula: no transmitted power, no received power. -/
lemma receivedPower_eq_zero_of_transmitPower_eq_zero {Gt Gr r lam S Ae Pr : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hGt : 0 ≤ Gt) (hGr : 0 ≤ Gr) (hS : S = 0 * Gt / (4 * π * r ^ 2))
    (hAe : Ae = Gr * lam ^ 2 / (4 * π)) (hPr : Pr = S * Ae) :
    Pr = 0 := by
  rw [hPr, hS]
  simp

/-- Validation, `Pt = 0` excludes the ratio form: with unit gains and the declared premises,
`Pr / Pt` is Lean's junk `0 / 0 = 0`, not the positive free-space factor `(λ / (4π r))²`. -/
lemma div_ne_friis_at_zero_transmitPower {r lam S Ae Pr : ℝ} (hr : 0 < r) (hlam : 0 < lam)
    (hS : S = 0 * 1 / (4 * π * r ^ 2)) (hAe : Ae = 1 * lam ^ 2 / (4 * π)) (hPr : Pr = S * Ae) :
    Pr / 0 ≠ 1 * 1 * (lam / (4 * π * r)) ^ 2 := by
  have hPr0 : Pr = 0 := by
    rw [hPr, hS]
    simp
  rw [hPr0, zero_div]
  have hpos : (0 : ℝ) < 1 * 1 * (lam / (4 * π * r)) ^ 2 := by positivity
  exact ne_of_lt hpos

/-- Validation, near-field use violates the model: under the aperture and matching premises with
`Gr > 0`, the Friis value holds exactly when the flux is the declared far-field flux. -/
lemma receivedPower_eq_friis_iff_flux {Pt Gt Gr r lam S Ae Pr : ℝ} (hr : 0 < r) (hlam : 0 < lam)
    (hGr : 0 < Gr) (hAe : Ae = Gr * lam ^ 2 / (4 * π)) (hPr : Pr = S * Ae) :
    Pr = Pt * Gt * Gr * (lam / (4 * π * r)) ^ 2 ↔ S = Pt * Gt / (4 * π * r ^ 2) := by
  have hd1 : (4 : ℝ) * π * r ^ 2 ≠ 0 := by positivity
  have hd2 : (4 : ℝ) * π ≠ 0 := by positivity
  have hd3 : (4 : ℝ) * π * r ≠ 0 := by positivity
  have hAe0 : Ae ≠ 0 := by
    rw [hAe]
    positivity
  have hC : Pt * Gt * Gr * (lam / (4 * π * r)) ^ 2
      = Pt * Gt / (4 * π * r ^ 2) * Ae := by
    rw [hAe, div_pow]
    field_simp
  rw [hPr, hC]
  constructor
  · intro h
    exact mul_right_cancel₀ hAe0 h
  · intro h
    rw [h]

/-- Validation, mismatch violates the model: with a polarization/impedance loss factor `p`
(`Pr = p S Ae`) and `Pt, Gt, Gr > 0`, the Friis value holds exactly when `p = 1`. -/
lemma mismatchedPower_eq_friis_iff {Pt Gt Gr r lam S Ae p : ℝ} (hr : 0 < r) (hlam : 0 < lam)
    (hPt : 0 < Pt) (hGt : 0 < Gt) (hGr : 0 < Gr) (hS : S = Pt * Gt / (4 * π * r ^ 2))
    (hAe : Ae = Gr * lam ^ 2 / (4 * π)) :
    p * S * Ae = Pt * Gt * Gr * (lam / (4 * π * r)) ^ 2 ↔ p = 1 := by
  have hd1 : (4 : ℝ) * π * r ^ 2 ≠ 0 := by positivity
  have hd2 : (4 : ℝ) * π ≠ 0 := by positivity
  have hd3 : (4 : ℝ) * π * r ≠ 0 := by positivity
  have hS0 : S ≠ 0 := by
    rw [hS]
    positivity
  have hAe0 : Ae ≠ 0 := by
    rw [hAe]
    positivity
  have hSA0 : S * Ae ≠ 0 := mul_ne_zero hS0 hAe0
  have hSA : S * Ae = Pt * Gt * Gr * (lam / (4 * π * r)) ^ 2 := by
    rw [hS, hAe, div_pow]
    field_simp
  have h1 : Pt * Gt * Gr * (lam / (4 * π * r)) ^ 2 = 1 * (S * Ae) := by
    rw [one_mul]
    exact hSA.symm
  rw [mul_assoc p S Ae, h1]
  constructor
  · intro h
    exact mul_right_cancel₀ hSA0 h
  · intro h
    rw [h]

end PhyslibExt.Electromagnetism.DeclaredFriisLink
