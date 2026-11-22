/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.PeriodicConvolution
public import Mathlib.Analysis.Complex.Basic

open MeasureTheory

-- Real-valued factors.
example {T : ℝ} {f g : ℝ → ℝ} (hg : Function.Periodic g T) :
    Function.Periodic (fun x ↦ ∫ t in (0 : ℝ)..T, f t * g (x - t)) T :=
  MathlibExt.Analysis.Fourier.periodic_convolution hg

-- Complex-valued factors, as in Fourier-series arguments.
example {T : ℝ} {f g : ℝ → ℂ} (hg : Function.Periodic g T) :
    Function.Periodic (fun x ↦ ∫ t in (0 : ℝ)..T, f t * g (x - t)) T :=
  MathlibExt.Analysis.Fourier.periodic_convolution hg

-- A concrete complex kernel: convolution with `x ↦ exp (i x)` over `[0, 2π]`.
example (f : ℝ → ℂ) :
    Function.Periodic
      (fun x ↦ ∫ t in (0 : ℝ)..(2 * Real.pi),
        f t * Complex.exp (Complex.I * ((x - t : ℝ) : ℂ)))
      (2 * Real.pi) :=
  MathlibExt.Analysis.Fourier.periodic_convolution
    (g := fun y : ℝ ↦ Complex.exp (Complex.I * (y : ℂ))) (fun y ↦ by
      have h : Complex.I * ((y + 2 * Real.pi : ℝ) : ℂ) =
          Complex.I * (y : ℂ) + 2 * Real.pi * Complex.I := by
        push_cast; ring
      simp only [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one])
