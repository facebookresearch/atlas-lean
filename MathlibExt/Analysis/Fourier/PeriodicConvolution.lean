/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.Ring.Periodic

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.Fourier

/-- **Periodic convolution.** Let $A$ be a normed ring that is a normed algebra over
$\mathbb{R}$ (for example $\mathbb{R}$ or $\mathbb{C}$), let $T$ be a real number, and let
$f, g : \mathbb{R} \to A$ with $g$ periodic of period $T$, that is, $g(x + T) = g(x)$ for all
real $x$. Then the function $x \mapsto \int_0^T f(t)\, g(x - t)\, dt$ is periodic of period
$T$. The function $f$ need not be periodic or integrable. -/
theorem periodic_convolution {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {T : ℝ} {f g : ℝ → A} (hg : Function.Periodic g T) :
    Function.Periodic (fun x ↦ ∫ t in (0 : ℝ)..T, f t * g (x - t)) T := by
  intro x
  apply intervalIntegral.integral_congr
  intro t _
  change f t * g (x + T - t) = f t * g (x - t)
  rw [show x + T - t = (x - t) + T by ring, hg]

end MathlibExt.Analysis.Fourier
