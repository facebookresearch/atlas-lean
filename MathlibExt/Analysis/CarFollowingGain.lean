/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Car-following frequency-gain reduction

## i. Overview

For the car-following transfer function
`H(s) = lam e^{-sT} / (s + lam e^{-sT})`, unit-gain reduction at
frequency `w` is exactly `w > 2 lam sin (wT)`, and the strict
inequality excludes the pole.

## ii. Key results

- `CarFollowingGain.gain_lt_one_iff`: the guarded equivalence.
- `CarFollowingGain.denom_ne_zero_of`: pole exclusion.

## iii. Table of contents

- A. Gain reduction

## iv. References

- R. E. Chandler, R. Herman and E. W. Montroll, *Traffic
  dynamics: studies in car following*, Operations Research 6(2),
  1958: the delayed car-following law whose linearization gives
  `H(s) = lam e^{-sT} / (s + lam e^{-sT})`.
- M. Treiber and A. Kesting, *Traffic Flow Dynamics*, Springer,
  2013, string-stability chapter: the frequency criterion
  `|H(iw)| < 1` for all `w > 0`.

## A. Gain reduction
-/

@[expose] public section

namespace CarFollowingGain

/-- The frequency denominator `iω + λ e^{-iωT}`. -/
noncomputable def denom (lam T w : ℝ) : ℂ :=
  Complex.I * w + lam * Complex.exp (-(Complex.I * w * T))

/-- The strict frequency inequality `ω > 2λ sin(ωT)` excludes the
pole: the denominator is nonzero. -/
theorem denom_ne_zero_of {lam T w : ℝ} (hlam : 0 < lam) (hw : 0 < w)
    (h : w > 2 * lam * Real.sin (w * T)) :
    denom lam T w ≠ 0 := by
  have hEre : (Complex.exp (-(Complex.I * w * T))).re = Real.cos (w * T) := by
    have harg : (-(Complex.I * w * T) : ℂ) = (((-(w * T) : ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have hEim : (Complex.exp (-(Complex.I * w * T))).im = -Real.sin (w * T) := by
    have harg : (-(Complex.I * w * T) : ℂ) = (((-(w * T) : ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  have hre : (denom lam T w).re = lam * Real.cos (w * T) := by
    simp [denom, hEre, hEim, Complex.add_re, Complex.mul_re]
  have him : (denom lam T w).im = w - lam * Real.sin (w * T) := by
    simp [denom, hEre, hEim, Complex.add_im, Complex.mul_im]
    ring
  have htrig := Real.sin_sq_add_cos_sq (w * T)
  have hnormSq : Complex.normSq (denom lam T w)
      = lam ^ 2 + w ^ 2 - 2 * lam * w * Real.sin (w * T) := by
    rw [Complex.normSq_apply, hre, him]
    linear_combination lam ^ 2 * htrig
  apply Complex.normSq_pos.mp
  rw [hnormSq]
  have hpos : 0 < w - 2 * lam * Real.sin (w * T) := by linarith
  have hmul : 0 < w * (w - 2 * lam * Real.sin (w * T)) := mul_pos hw hpos
  have hlam2 : 0 < lam ^ 2 := by positivity
  have heq : lam ^ 2 + w ^ 2 - 2 * lam * w * Real.sin (w * T)
      = lam ^ 2 + w * (w - 2 * lam * Real.sin (w * T)) := by ring
  rw [heq]
  linarith

/-- Guarded gain reduction: for `λ > 0`, `ω > 0`,
`|λ e^{-iωT}| < |iω + λ e^{-iωT}|` (unit-gain reduction of the
car-following transfer function `H(iω)`) iff `ω > 2λ sin(ωT)`. -/
theorem gain_lt_one_iff {lam T w : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    ‖(lam : ℂ) * Complex.exp (-(Complex.I * w * T))‖
        < ‖denom lam T w‖
      ↔ w > 2 * lam * Real.sin (w * T) := by
  have hEre : (Complex.exp (-(Complex.I * w * T))).re = Real.cos (w * T) := by
    have harg : (-(Complex.I * w * T) : ℂ) = (((-(w * T) : ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have hEim : (Complex.exp (-(Complex.I * w * T))).im = -Real.sin (w * T) := by
    have harg : (-(Complex.I * w * T) : ℂ) = (((-(w * T) : ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  have hre : (denom lam T w).re = lam * Real.cos (w * T) := by
    simp [denom, hEre, hEim, Complex.add_re, Complex.mul_re]
  have him : (denom lam T w).im = w - lam * Real.sin (w * T) := by
    simp [denom, hEre, hEim, Complex.add_im, Complex.mul_im]
    ring
  have htrig := Real.sin_sq_add_cos_sq (w * T)
  have hnormSq : Complex.normSq (denom lam T w)
      = lam ^ 2 + w ^ 2 - 2 * lam * w * Real.sin (w * T) := by
    rw [Complex.normSq_apply, hre, him]
    linear_combination lam ^ 2 * htrig
  have harg : (-(Complex.I * w * T) : ℂ) = (((-(w * T) : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  have hEnorm : ‖Complex.exp (-(Complex.I * w * T))‖ = 1 := by
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have hA : ‖(lam : ℂ) * Complex.exp (-(Complex.I * w * T))‖ = lam := by
    rw [norm_mul, hEnorm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
  have hB2 : ‖denom lam T w‖ ^ 2
      = lam ^ 2 + w ^ 2 - 2 * lam * w * Real.sin (w * T) := by
    rw [← Complex.normSq_eq_norm_sq, hnormSq]
  rw [hA, (sq_lt_sq₀ hlam.le (norm_nonneg _)).symm, hB2]
  constructor
  · intro h
    have h2 : (2 * lam * Real.sin (w * T)) * w < w * w := by
      have e1 : (2 * lam * Real.sin (w * T)) * w = 2 * lam * w * Real.sin (w * T) := by ring
      have e2 : w * w = w ^ 2 := by ring
      rw [e1, e2]
      linarith
    exact lt_of_mul_lt_mul_right h2 hw.le
  · intro h
    have h2 : (2 * lam * Real.sin (w * T)) * w < w * w :=
      mul_lt_mul_of_pos_right h hw
    have e1 : (2 * lam * Real.sin (w * T)) * w = 2 * lam * w * Real.sin (w * T) := by ring
    have e2 : w * w = w ^ 2 := by ring
    rw [e1, e2] at h2
    linarith

end CarFollowingGain
