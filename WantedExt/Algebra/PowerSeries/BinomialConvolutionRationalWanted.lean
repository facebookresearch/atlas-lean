/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Algebra.PowerSeries.BinomialConvolutionCubicDenominator
public import MathlibExt.Algebra.PowerSeries.BinomialConvolutionLucas
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.LinearAlgebra.OrthogonalDescent
public import MathlibExt.RingTheory.Polynomial.PairwiseSumResultant
public import MathlibExt.RingTheory.PowerSeries.BinomialProductGeometric
public import MathlibExt.RingTheory.PowerSeries.BinomialProductMonomial
public import MathlibExt.RingTheory.PowerSeries.BinomialProductRationalGeneral
public import MathlibExt.RingTheory.PowerSeries.HadamardProductRational
public import MathlibExt.RingTheory.PowerSeries.RationalityDescent

/-!
# Binomial convolutions for rational power series

Statements from Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3 (arXiv `2304.10426`).

The binomial product `A ⊙ B` is `binomialProduct A B`
(`MathlibExt.RingTheory.PowerSeries.BinomialProduct`), with `n`-th coefficient
`∑_k binom(n, k) a_k b_{n-k}`; the Hadamard product `A * B` is written out coefficientwise.
The paper works over a field of characteristic `0`; the zeros `αᵢ`, `βⱼ` of the
denominators, which the paper takes in an extension field, are taken here in the coefficient
field `K` itself (map the series to a splitting field to recover the paper's setting).
Resultants are Mathlib's `Polynomial.resultant` with explicit formal degrees.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **Resultant identity for pairwise products.** Let $K$ be a field of characteristic $0$, let
$m, n \ge 0$ be integers, and let $\alpha_1, \dots, \alpha_m$ and $\beta_1, \dots, \beta_n$ be
elements of $K$. Regard $f(y) = \prod_{i=1}^{m} (1 - \alpha_i y)$ and
$g(y) = \prod_{j=1}^{n} (y - \beta_j x)$ as polynomials in $y$ with coefficients in $K[x]$,
and let $\operatorname{Res}_{m,n}(f, g)$ be the determinant of their Sylvester matrix formed with
the formal degrees $m$ and $n$. Then in $K[x]$

$$
\prod_{i=1}^{m} \prod_{j=1}^{n} (1 - \alpha_i \beta_j x) = (-1)^{mn} \operatorname{Res}_{m,n}(f, g).
$$

With $U(x) = \prod_{i=1}^{m} (1 - \alpha_i x)$ and $V(x) = \prod_{j=1}^{n} (1 - \beta_j x)$, these
are $f(y) = U(y)$ and $g(y) = y^n V(x / y)$, the form used in the source.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 14 (`jis-2024-24.1.3-thm-14`). -/
public theorem_wanted prod_one_sub_mul_eq_resultant {K : Type*} [Field K] [CharZero K] (m n : ℕ)
    (α : Fin m → K) (β : Fin n → K) :
    ∏ i, ∏ j, (1 - Polynomial.C (α i * β j) * Polynomial.X) =
      (-1) ^ (m * n) * Polynomial.resultant
        (∏ i, (1 - Polynomial.C (Polynomial.C (α i)) * Polynomial.X))
        (∏ j, (Polynomial.X - Polynomial.C (Polynomial.C (β j) * Polynomial.X))) m n

end

end MetaMathlibExt
