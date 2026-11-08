/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Algebra.Ring.Periodic

@[expose] public section

open MeasureTheory Complex Set Filter
open scoped ENNReal ComplexConjugate Real BigOperators

namespace MathlibExt.Analysis.Fourier.DirichletTheoremWanted

/-- Dirichlet–Jordan theorem on pointwise convergence of Fourier series: for a
`2π`-periodic function of bounded variation on `[-π, π]`, the one-sided limits
exist at every point and the symmetric Fourier partial sums converge to their
average. The coefficients are Mathlib's `fourierCoeffOn Real.two_pi_pos f n` on `[0, 2π]`, which
by periodicity equal the coefficients over `[-π, π]`.

This is the bounded-variation (Dirichlet-Jordan) form. It is distinct from
`MathlibExt.Analysis.FourierConvergenceWanted.Analysis.dirichlet_pointwise`, which assumes
`f` is `C¹` and concludes convergence to `f x`; here `f` may be discontinuous and the limit
is the average of the one-sided limits.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Measures and integral calculus /
  Fourier analysis", entry "Dirichlet theorem" (currently missing: empty entry,
  no Mathlib declaration).
- Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Ch. I, §5
  (functions of bounded variation; Dirichlet–Jordan test).
- https://en.wikipedia.org/wiki/Dirichlet%27s_theorem_on_Fourier_series
-/
public theorem_wanted dirichlet_pointwise_convergence
    (f : ℝ → ℂ)
    (hf_periodic : Function.Periodic f (2 * Real.pi))
    (hf_bv : BoundedVariationOn f (Icc (-Real.pi) Real.pi)) :
    ∀ x : ℝ, ∃ lPlus lMinus : ℂ,
      Tendsto f (nhdsWithin x (Ioi x)) (nhds lPlus) ∧
      Tendsto f (nhdsWithin x (Iio x)) (nhds lMinus) ∧
      Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          fourierCoeffOn Real.two_pi_pos f n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)))
        atTop (nhds ((lPlus + lMinus) / 2))

end MathlibExt.Analysis.Fourier.DirichletTheoremWanted
