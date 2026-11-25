/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Exp
public import MathlibExt.Algebra.PowerSeries.CatalanTypeKernelDecomposition
public import MathlibExt.Algebra.PowerSeries.CatalanTypeMatrixDeterminant
public import MathlibExt.Algebra.PowerSeries.UnifiedCatalanTypePolynomials

/-!
# Unified Catalan-type polynomials

Statements from M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105.

Every family in the paper is defined by a generating function of the shape
`numerator(t) / (c - α t + β t^m)^λ` with a real exponent `λ`. The denominator factor
`(c - α t + β t^m)^(-λ)` is `trinomialNegPowSeries λ c α β m`, built from Mathlib's binomial
series; the paper's polynomials are coefficients of products of power series in `t`, with
all variables `x, y, z` fixed real numbers. The paper's `P^λ_{r,m}(z)` and `h^λ_{r,m}(z)`
in Theorems 2 and 3 are read as the coefficients of `(1 - m t + z t^m)^(-λ)` and
`(1 - m z t + t^m)^(-λ)` (Definition 5 with `A = 0`), as in the proof of Theorem 2.
The paper's Hermite polynomials `H_n(x)` have the generating function `e^(2xt - t²)`
(Section 1), and `H_n(x, y)` are the Kampé de Fériet polynomials `H^2_n(x, y)` of
Equation (2).

Proved in `MathlibExt.Algebra.PowerSeries.UnifiedCatalanTypePolynomials`, which this module
imports: `coeff_nietoHermiteSeries_mul_trinomialNegPowSeries` and `det_catalanTypeHankel_eq_zero`.

The lower-triangular determinant formula is proved in and re-exported from
`MathlibExt.Algebra.PowerSeries.CatalanTypeMatrixDeterminant`.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **Hermite-shifted Catalan-type polynomials as convolutions.** Write $H_n(x, y) = H^2_n(x, y)$
for the Kampé de Fériet polynomials. For a natural number $m$ and real numbers $\lambda, z$,
write $(1 - m t + z t^m)^{-\lambda}$ and $(1 - m z t + t^m)^{-\lambda}$ for the negative real
powers of the trinomials $1 - m t + z t^m$ and $1 - m z t + t^m$ with exponent $\lambda$ as
power series in $t$ (for $m \ge 1$ these are their expansions in powers of $t$), and let
$P^\lambda_{r,m}(z)$ and $h^\lambda_{r,m}(z)$ be their coefficients of $t^r$. For all natural
numbers $k, m, n$ and real numbers $\lambda, x, y, z$, as formal power series in $t$ (with
$e^{xt + yt^2}$ the exponential series and $H_k(x + 2yt, y)$ evaluated in power series), the
coefficient of $t^n$ in $e^{xt + yt^2} H_k(x + 2yt, y) (1 - m t + z t^m)^{-\lambda}$ is
$\sum_{r=0}^{n} H_{n-r+k}(x, y) P^\lambda_{r,m}(z) / (n - r)!$, and the coefficient of $t^n$
in $e^{xt + yt^2} H_k(x + 2yt, y) (1 - m z t + t^m)^{-\lambda}$ is
$\sum_{r=0}^{n} H_{n-r+k}(x, y) h^\lambda_{r,m}(z) / (n - r)!$.

These coefficients are the paper's $H^{k;\lambda}_{n,m}(x, y, z)$ and
$h^{k;\lambda}_{n,m}(x, y, z)$ (Definition 3, Equations (8) and (9)).

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 2
(`integers-2026-A105-thm-2`). -/
public theorem_wanted coeff_hermiteShift_mul_trinomialNegPowSeries (k m n : ℕ)
    (lam x y z : ℝ) :
    let G : PowerSeries ℝ := ((exp ℝ).subst (C x * X + C y * X ^ 2 : PowerSeries ℝ) :
        PowerSeries ℝ) * kampeDeFerietHermite 2 k (C x + C (2 * y) * X) (C y)
    coeff n (G * trinomialNegPowSeries lam 1 m z m) =
        ∑ r ∈ Finset.range (n + 1), kampeDeFerietHermite 2 (n - r + k) x y /
          ((n - r).factorial : ℝ) * coeff r (trinomialNegPowSeries lam 1 m z m) ∧
      coeff n (G * trinomialNegPowSeries lam 1 (m * z) 1 m) =
        ∑ r ∈ Finset.range (n + 1), kampeDeFerietHermite 2 (n - r + k) x y /
          ((n - r).factorial : ℝ) * coeff r (trinomialNegPowSeries lam 1 (m * z) 1 m)

end

end MetaMathlibExt
