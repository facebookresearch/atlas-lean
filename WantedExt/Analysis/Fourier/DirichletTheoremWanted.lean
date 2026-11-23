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

/-- **Dirichlet–Jordan theorem on pointwise convergence of Fourier series.** Let
$f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of bounded variation on $[-\pi, \pi]$,
and for $n \in \mathbb{Z}$ let $c_n = \frac{1}{2\pi} \int_0^{2\pi} f(t) e^{-int}\,dt$ be its
Fourier coefficients. Then at every $x \in \mathbb{R}$ the one-sided limits
$f(x^+) = \lim_{y \to x,\, y > x} f(y)$ and $f(x^-) = \lim_{y \to x,\, y < x} f(y)$ exist, and
the symmetric partial sums of the Fourier series converge to their average:
$$\lim_{N \to \infty} \sum_{n=-N}^{N} c_n e^{inx} = \frac{f(x^+) + f(x^-)}{2}.$$
By periodicity, the coefficients $c_n$ equal the corresponding integrals over $[-\pi, \pi]$.

This is the bounded-variation (Dirichlet–Jordan) form. It is distinct from the version of
Dirichlet's theorem that assumes $f$ continuously differentiable and concludes convergence to
$f(x)$; here $f$ may be discontinuous and the limit is the average of the one-sided limits.

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
