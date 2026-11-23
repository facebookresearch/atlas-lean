/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Signals.FourierConventions
import Mathlib.Tactic.NormNum

open MeasureTheory
open scoped FourierTransform
open ControlTheory

-- At zero frequency the two conventions agree on the nose: an importing
-- client rewriting with `fourierAngular_eq` at `ω = 0` gets `𝓕 f 0`.
example {f : ℝ → ℂ} (hf : Integrable f) : fourierAngular f 0 = 𝓕 f 0 := by
  rw [fourierAngular_eq hf]
  norm_num

-- Modulation by `a = 0` is the identity operation on the transform.
example {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    𝓕 (fun t => Complex.exp (↑(2 * Real.pi * (0 : ℝ) * t) * Complex.I) * f t) ξ =
      𝓕 f ξ := by
  rw [fourier_modulation hf]
  norm_num

-- Shifting by `a = 0` multiplies the transform by the phase `1`.
example {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    𝓕 (fun t => f (t - (0 : ℝ))) ξ = 𝓕 f ξ := by
  rw [fourier_shift hf]
  simp

-- For a real signal the transform at zero frequency is real: it equals its
-- own conjugate, by conjugate symmetry at `ξ = 0`.
example {f : ℝ → ℝ} (hf : Integrable (fun t => ((f t : ℝ) : ℂ))) :
    starRingEnd ℂ (𝓕 (fun t => ((f t : ℝ) : ℂ)) 0) =
      𝓕 (fun t => ((f t : ℝ) : ℂ)) 0 := by
  have h := fourier_neg_eq_conj_of_real hf (0 : ℝ)
  simpa using h.symm

-- Nonzero normalization: at `ω = 2πξ` the angular form is the hertz form at
-- `ξ`. This pins the `2π` factor: any other constant in `fourierAngular_eq`
-- would fail here.
example {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    fourierAngular f (2 * Real.pi * ξ) = 𝓕 f ξ := by
  rw [fourierAngular_eq hf,
    mul_div_cancel_left₀ ξ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]

-- Nonzero hertz delay phase: delaying by `1` at `ξ = 1/2` multiplies by
-- `e^{-2πi·1·(1/2)} = e^{-πi} = -1`. This pins both the `2π` factor and the
-- sign of the shift phase.
example {f : ℝ → ℂ} (hf : Integrable f) :
    𝓕 (fun t => f (t - (1 : ℝ))) (1 / 2 : ℝ) = -𝓕 f (1 / 2 : ℝ) := by
  have hphase : Complex.exp (↑(-2 * Real.pi * (1 : ℝ) * (1 / 2 : ℝ)) *
      Complex.I) = -1 := by
    have h1 : (-2 * Real.pi * (1 : ℝ) * (1 / 2 : ℝ)) = -Real.pi := by ring
    rw [h1, Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  rw [fourier_shift hf, hphase, neg_mul, one_mul]

-- Nonzero angular delay phase: delaying by `1` at `ω = π` multiplies by
-- `e^{-i·1·π} = -1`, pinning the angular convention's phase and sign.
example {f : ℝ → ℂ} (hf : Integrable f) :
    fourierAngular (fun t => f (t - (1 : ℝ))) Real.pi =
      -fourierAngular f Real.pi := by
  have hphase : Complex.exp (↑(-((1 : ℝ) * Real.pi)) * Complex.I) = -1 := by
    rw [one_mul, Complex.ofReal_neg, neg_mul, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    simp
  rw [fourierAngular_shift hf, hphase, neg_mul, one_mul]

-- Nonzero modulation: multiplying by `e^{2πit}` shifts the hertz argument
-- down by `1`, so the value at `3/2` is the original value at `1/2`.
example {f : ℝ → ℂ} (hf : Integrable f) :
    𝓕 (fun t => Complex.exp (↑(2 * Real.pi * (1 : ℝ) * t) * Complex.I) * f t)
        (3 / 2 : ℝ) = 𝓕 f (1 / 2 : ℝ) := by
  rw [fourier_modulation hf]
  norm_num

-- Conjugate symmetry at a nonzero frequency, fixing which side carries the
-- negation: value at `-1` is the conjugate of the value at `1`.
example {f : ℝ → ℝ} (hf : Integrable (fun t => ((f t : ℝ) : ℂ))) :
    𝓕 (fun t => ((f t : ℝ) : ℂ)) (-1 : ℝ) =
      starRingEnd ℂ (𝓕 (fun t => ((f t : ℝ) : ℂ)) (1 : ℝ)) :=
  fourier_neg_eq_conj_of_real hf 1

#print axioms fourierAngular_eq
#print axioms fourier_neg_eq_conj_of_real
#print axioms fourier_shift
#print axioms fourier_modulation
#print axioms fourierAngular_shift
