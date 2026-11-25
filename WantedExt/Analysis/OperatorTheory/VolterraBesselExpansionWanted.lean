/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.Algebra.Polynomial.BesselPolynomial

/-!
# Expansion of `(XV)^n` with Bessel numbers

Statement from Abdelhay Benmoussa, *On the Expansion of `(XV)^n` and Bessel Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.5. `X` is multiplication by `x` and `V` is
the Volterra operator `V f x = ∫_0^x f t dt`; the Bessel numbers are
`a(n, k) = [x^k] y_n(x)`, the coefficients of `MetaMathlibExt.besselPolynomial`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Expansion of $(XV)^n$ in Bessel numbers.** Let $X$ and $V$ be the operators on functions
$\mathbb{R} \to \mathbb{R}$ given by $(Xg)(y) = y \, g(y)$ and $(Vg)(y) = \int_0^y g(t) \, dt$,
write $(XV)^n$ and $V^m$ for iterated composition, and let $a(m, k)$ be the coefficient of $x^k$
in the Bessel polynomial $y_m$. For every natural number $n \ge 1$, every continuous function
$f : \mathbb{R} \to \mathbb{R}$ and every real number $x$,

$$(XV)^n f(x) = \sum_{k=0}^{n-1} (-1)^k \, a(n-1, k) \, x^{n-k} \, (V^{n+k} f)(x).$$

Source: Abdelhay Benmoussa, *On the Expansion of `(XV)^n` and Bessel Numbers*, Journal of
Integer Sequences 29 (2026), Article 26.3.5, Theorem 1 (`jis-2026-26.3.5-thm-1`). -/
public theorem_wanted xMul_volterra_iterate_eq_sum_bessel (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ)
    (hf : Continuous f) (x : ℝ) :
    (fun g : ℝ → ℝ => fun y => y * ∫ t in (0 : ℝ)..y, g t)^[n] f x =
      ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * ((besselPolynomial (n - 1)).coeff k : ℝ) *
        x ^ (n - k) * (fun g : ℝ → ℝ => fun y => ∫ t in (0 : ℝ)..y, g t)^[n + k] f x

end

end MetaMathlibExt
