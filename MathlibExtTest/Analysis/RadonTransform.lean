/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.RadonTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory
open MathlibExt.Analysis.RadonTransformWanted.Analysis.RadonTransform

-- A quarter turn takes the normal to the second coordinate axis.
example (f : ℝ × ℝ → ℂ) (p : ℝ) :
    radon f (p, Real.pi / 2) = ∫ t : ℝ, f (-t, p) := by
  simp [radon, Real.cos_pi_div_two, Real.sin_pi_div_two]

-- Integrating the planar Gaussian along the central vertical line gives a nonzero value.
example :
    radon (fun x => (Real.exp (-(x.1 ^ 2 + x.2 ^ 2)) : ℂ)) (0, 0) =
      (Real.sqrt Real.pi : ℂ) := by
  simp only [radon, Real.cos_zero, Real.sin_zero, mul_zero, zero_sub, neg_zero,
    mul_one, zero_add, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  exact (integral_ofReal (f := fun t : ℝ => Real.exp (-(t ^ 2)))).trans
    (congrArg Complex.ofReal (by simpa using integral_gaussian 1))

example (g : ℝ → ℂ) : fourier1 g 0 = ∫ p : ℝ, g p := by
  simp [fourier1]

-- The zero-frequency slice is the same planar integral in every direction.
example (φ : SchwartzMap (ℝ × ℝ) ℂ) (θ : ℝ) :
    (∫ p : ℝ, radon φ (p, θ)) = ∫ x : ℝ × ℝ, φ x := by
  simpa [fourier1, fourier2] using
    radon_can_be_diagonalized_and_pseudo_inverted.1 φ θ 0

example (φ ψ : SchwartzMap (ℝ × ℝ) ℂ) (h : ∀ p θ : ℝ, radon φ (p, θ) = radon ψ (p, θ)) :
    φ = ψ := by
  obtain ⟨Rinv, hRinv⟩ := radon_can_be_diagonalized_and_pseudo_inverted.2
  apply SchwartzMap.ext
  have hR : radon φ = radon ψ := funext fun x => h x.1 x.2
  rw [← hRinv φ, ← hRinv ψ, hR]
  exact fun _ => rfl
