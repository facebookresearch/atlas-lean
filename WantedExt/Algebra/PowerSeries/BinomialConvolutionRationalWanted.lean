/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.LinearAlgebra.OrthogonalDescent
public import MathlibExt.RingTheory.Polynomial.PairwiseSumResultant
public import MathlibExt.RingTheory.PowerSeries.BinomialProductGeometric
public import MathlibExt.RingTheory.PowerSeries.BinomialProductMonomial
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

/-- **Binomial products of proper rational series.** Let $K$ be a field of characteristic $0$, let
$\alpha_1, \dots, \alpha_m, \beta_1, \dots, \beta_n \in K$, not necessarily distinct or nonzero,
and let $R$, $S$ be polynomials over $K$ with $\deg R < m$ and $\deg S < n$. If $A$, $B$ are power
series over $K$ with $A(x) \prod_{i=1}^m (1 - \alpha_i x) = R(x)$ and
$B(x) \prod_{j=1}^n (1 - \beta_j x) = S(x)$, then there is a polynomial $T$ over $K$ with
$\deg T < mn$ such that

$$(A \odot B)(x) \prod_{i=1}^m \prod_{j=1}^n \bigl(1 - (\alpha_i + \beta_j) x\bigr) = T(x),$$

where $\odot$ is the binomial product.

Here $\deg 0 = -\infty$, so $T = 0$ when $mn = 0$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 6 (`jis-2024-24.1.3-thm-6`). -/
public theorem_wanted binomialProduct_rational {K : Type*} [Field K] [CharZero K] (m n : ℕ)
    (α : Fin m → K) (β : Fin n → K) (R S : Polynomial K) (hR : R.degree < m) (hS : S.degree < n)
    (A B : PowerSeries K) (hA : A * ∏ i, (1 - C (α i) * X) = (R : PowerSeries K))
    (hB : B * ∏ j, (1 - C (β j) * X) = (S : PowerSeries K)) :
    ∃ T : Polynomial K, T.degree < (m * n : ℕ) ∧
      binomialProduct A B * ∏ i, ∏ j, (1 - C (α i + β j) * X) = (T : PowerSeries K)

/-- **Binomial products of arbitrary rational series.** Let $K$ be a field of characteristic $0$,
let $\alpha_1, \dots, \alpha_m$ and $\beta_1, \dots, \beta_n$ be nonzero elements of $K$, and let
$R$, $S$ be polynomials over $K$. Let $A$, $B$ be power series over $K$ with
$A(x) \prod_{i=1}^m (1 - \alpha_i x) = R(x)$ and $B(x) \prod_{j=1}^n (1 - \beta_j x) = S(x)$.
Put $u = \max(d_R + 1 - m, 0)$ and $v = \max(d_S + 1 - n, 0)$, where $d_R$ and $d_S$ are the
degrees of $R$ and $S$, the zero polynomial counting as degree $0$. Then there is a polynomial
$T$ over $K$ of degree less than $(u + m)(v + n)$ such that

$$(A \odot B)(x) \Big(\prod_{i=1}^m (1 - \alpha_i x)\Big)^{v}
\Big(\prod_{j=1}^n (1 - \beta_j x)\Big)^{u} \prod_{i=1}^m \prod_{j=1}^n (1 - (\alpha_i + \beta_j) x)
= T(x),$$

where $\odot$ is the binomial product.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Corollary 7 (`jis-2024-24.1.3-cor-7`). -/
public theorem_wanted binomialProduct_rational_general {K : Type*} [Field K] [CharZero K]
    (m n : ℕ) (α : Fin m → K) (β : Fin n → K) (hα : ∀ i, α i ≠ 0) (hβ : ∀ j, β j ≠ 0)
    (R S : Polynomial K) (A B : PowerSeries K) (hA : A * ∏ i, (1 - C (α i) * X) = (R : PowerSeries K))
    (hB : B * ∏ j, (1 - C (β j) * X) = (S : PowerSeries K)) :
    ∃ T : Polynomial K, T.degree < (((R.natDegree + 1 - m) + m) * ((S.natDegree + 1 - n) + n) : ℕ) ∧
      binomialProduct A B * ((∏ i, (1 - C (α i) * X)) ^ (S.natDegree + 1 - n) *
        (∏ j, (1 - C (β j) * X)) ^ (R.natDegree + 1 - m) *
        ∏ i, ∏ j, (1 - C (α i + β j) * X)) = (T : PowerSeries K)

/-- **Binomial square of the Lucas generating function.** Let $K$ be a field of characteristic
$0$, let $a, b \in K$, and let $g(x) = \sum_{n \ge 0} G_n x^n$ be a power series over $K$ with
$g(x)(1 - ax - bx^2) = 2 - ax$. Then

$$g \odot g = \frac{2}{1 - ax} + g(2x),$$

where $\odot$ is the binomial product, and
$\sum_{k=0}^{n} \binom{n}{k} G_k G_{n-k} = 2a^n + 2^n G_n$ for every $n \ge 0$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 11 (`jis-2024-24.1.3-thm-11`). -/
public theorem_wanted binomialProduct_lucasV_generatingFunction {K : Type*} [Field K]
    [CharZero K] (a b : K) (g : PowerSeries K)
    (hg : g * (1 - C a * X - C b * X ^ 2) = 2 - C a * X) :
    binomialProduct g g = 2 * (1 - C a * X)⁻¹ + PowerSeries.rescale 2 g ∧
      ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1),
          (n.choose k : K) * PowerSeries.coeff k g * PowerSeries.coeff (n - k) g =
        2 * a ^ n + 2 ^ n * PowerSeries.coeff n g

/-- **Binomial products of series with a cubic denominator.** Let $K$ be a field of characteristic
$0$, let $A, B, C \in K$ with $C \ne 0$, and let $D(x) = 1 + Ax + Bx^2 + Cx^3$. Suppose that
$D(x) = \prod_{i=1}^{3} (1 - \alpha_i x)$ with $\alpha_1, \alpha_2, \alpha_3 \in K$ and that
$2\alpha_i \ne \alpha_j + \alpha_k$ whenever $i, j, k \in \{1, 2, 3\}$ are not all equal. Let $r$
and $s$ be power series over $K$ such that $r D$ and $s D$ are polynomials of degree less than $3$.
Then there are polynomials $u$, $v$ over $K$ of degree at most $2$ such that

$$r \odot s = \frac{u(x)}{D(2x)} + \frac{1}{1 + Ax} \odot \frac{v(x)}{D(-x)},$$

where $\odot$ is the binomial product.

The second term uses the factor $1/(1 + Ax)$; with $1/(1 - Ax)$ in its place the statement already
fails for the tribonacci series $x/(1 - x - x^2 - x^3)$, where $A = -1$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 12 (`jis-2024-24.1.3-thm-12`). -/
public theorem_wanted binomialProduct_cubic_denominator {K : Type*} [Field K] [CharZero K]
    (A B C' : K) (hC : C' ≠ 0) (α : Fin 3 → K)
    (hD : 1 + C A * X + C B * X ^ 2 + C C' * X ^ 3 = ∏ i, (1 - C (α i) * X))
    (hα : ∀ i j k, ¬(i = j ∧ j = k) → 2 * α i ≠ α j + α k)
    (r s : PowerSeries K) (pr ps : Polynomial K) (hpr : pr.degree < 3) (hps : ps.degree < 3)
    (hr : r * (1 + C A * X + C B * X ^ 2 + C C' * X ^ 3) = (pr : PowerSeries K))
    (hs : s * (1 + C A * X + C B * X ^ 2 + C C' * X ^ 3) = (ps : PowerSeries K)) :
    ∃ u v : Polynomial K, u.natDegree ≤ 2 ∧ v.natDegree ≤ 2 ∧
      binomialProduct r s =
        (u : PowerSeries K) * (1 + C (2 * A) * X + C (4 * B) * X ^ 2 + C (8 * C') * X ^ 3)⁻¹ +
          binomialProduct (1 + C A * X)⁻¹
            ((v : PowerSeries K) * (1 - C A * X + C B * X ^ 2 - C C' * X ^ 3)⁻¹)

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
