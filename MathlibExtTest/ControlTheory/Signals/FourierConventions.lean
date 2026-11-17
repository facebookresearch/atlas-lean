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

#print axioms fourierAngular_eq
#print axioms fourier_neg_eq_conj_of_real
#print axioms fourier_shift
#print axioms fourier_modulation
#print axioms fourierAngular_shift
