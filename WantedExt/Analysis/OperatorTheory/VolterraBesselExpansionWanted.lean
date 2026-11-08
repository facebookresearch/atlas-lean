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

/-- Theorem 1 (main result): for `n ≥ 1`,
`(XV)^n = ∑_{k=0}^{n-1} (-1)^k a(n-1, k) X^{n-k} V^{n+k}`, where `X` is multiplication by
`x`, `V f x = ∫_0^x f t dt` and `a(n, k) = [x^k] y_n(x)` is the coefficient of the Bessel
polynomial. The operator identity is stated pointwise on continuous `f : ℝ → ℝ`.

Source: Abdelhay Benmoussa, *On the Expansion of `(XV)^n` and Bessel Numbers*, Journal of
Integer Sequences 29 (2026), Article 26.3.5, Theorem 1 (`jis-2026-26.3.5-thm-1`). -/
public theorem_wanted xMul_volterra_iterate_eq_sum_bessel (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ)
    (hf : Continuous f) (x : ℝ) :
    (fun g : ℝ → ℝ => fun y => y * ∫ t in (0 : ℝ)..y, g t)^[n] f x =
      ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * ((besselPolynomial (n - 1)).coeff k : ℝ) *
        x ^ (n - k) * (fun g : ℝ → ℝ => fun y => ∫ t in (0 : ℝ)..y, g t)^[n + k] f x

end

end MetaMathlibExt
