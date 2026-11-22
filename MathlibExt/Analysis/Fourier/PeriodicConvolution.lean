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

/-- Convolution over one period, `x ↦ ∫ t in 0..T, f t * g (x - t)`, with a `T`-periodic second
factor is `T`-periodic. The values lie in any normed ring that is a normed real algebra (for
example `ℝ` or `ℂ`); `f` need not be periodic or integrable. -/
theorem periodic_convolution {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {T : ℝ} {f g : ℝ → A} (hg : Function.Periodic g T) :
    Function.Periodic (fun x ↦ ∫ t in (0 : ℝ)..T, f t * g (x - t)) T := by
  intro x
  apply intervalIntegral.integral_congr
  intro t _
  change f t * g (x + T - t) = f t * g (x - t)
  rw [show x + T - t = (x - t) + T by ring, hg]

end MathlibExt.Analysis.Fourier
