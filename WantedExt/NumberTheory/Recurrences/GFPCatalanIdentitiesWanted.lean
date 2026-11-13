/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Catalan identities for generalized Fibonacci polynomials

Statements from Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero
Rojas, *Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62
(2024), Article florez11012023.

A generalized Fibonacci polynomial (GFP) of Fibonacci type is `F_0 = 0`, `F_1 = 1`,
`F_n = d F_{n-1} + g F_{n-2}`; one of Lucas type is `L_0 = p₀`, `L_1 = p₁`, same recurrence,
where `α p₀ = 2` for an integer `α` (so `|p₀| ∈ {1, 2}`) and `d = α p₁` (paper, (2.1), (2.2)).
Both are the existing `generalizedFibonacciPolynomial` over `ℤ[X]`, so the paper's `ℚ[x]`
coefficients are restricted to `ℤ[x]`; the identities hold without the paper's nonzero
assumptions on `p₁`, `d`, `g`, except Proposition 5.2, whose negative-index terms need
`g(x) ≠ 0`. Identities with a factor `1/2^{n-1}` or `1/α` are stated with
cleared denominators. Section 5 evaluates the polynomials at a real `x` with
`d(x)² + 4 g(x) ≥ 0`, so that the square root is real.

Section 4 uses the sums `T_ℓ(n; t) = ∑_i C(n, i) t^{⌊i/ℓ⌋}` and
`T_{ℓ,s}(n; t) = ∑_i C(n, ℓ i + s) t^i` ((4.1), (4.2)) for `t` in a commutative ring; they are
written inline, with `i` ranging over `0, …, n`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial

namespace MetaMathlibExt

open Polynomial Finset

@[expose] public section

/-- **Explicit formula for Fibonacci-type generalized Fibonacci polynomials.** Let $d$ and $g$ be
polynomials with integer coefficients, and let $F_n$ be the generalized Fibonacci polynomials
defined by $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = d F_{n+1} + g F_n$. Then for every $n \ge 1$,
$$F_n = \sum_{i=0}^{\lfloor (n-1)/2 \rfloor} \binom{n-i-1}{i} d^{n-2i-1} g^i.$$

The source quotes this formula from Flórez and Saunders.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.1 (1) (`fq-2024-florez11012023-lem-3.1`). -/
public theorem_wanted gfp_fib_eq_sum_choose (d g : ℤ[X]) {n : ℕ} (hn : 1 ≤ n) :
    generalizedFibonacciPolynomial 0 1 d g n =
      ∑ i ∈ range ((n - 1) / 2 + 1), ((n - i - 1).choose i : ℤ[X]) * d ^ (n - 2 * i - 1) * g ^ i

/-- **Explicit formula for Lucas-type generalized Fibonacci polynomials.** Let $\alpha$ and $p_0$
be integers with $\alpha p_0 = 2$, let $p_1$ and $g$ be polynomials with integer coefficients, and
put $d = \alpha p_1$. Let $L_n$ be the generalized Fibonacci polynomials defined by $L_0 = p_0$,
$L_1 = p_1$ and $L_{n+2} = d L_{n+1} + g L_n$. Then for every $n \ge 1$, writing
$c_i = \lfloor n \binom{n-i}{i} / (n-i) \rfloor$,
$$\alpha L_n = \sum_{i=0}^{\lfloor n/2 \rfloor} c_i \, d^{n-2i} g^i.$$

The quotient $n \binom{n-i}{i} / (n-i)$ is always an integer, so the floor does not change it;
the source writes the coefficient as $\frac{n}{n-i} \binom{n-i}{i}$ and quotes the formula from
Flórez and Saunders.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.1 (2) (`fq-2024-florez11012023-lem-3.1`). -/
public theorem_wanted gfp_lucas_eq_sum_choose {α p₀ : ℤ} (hα : α * p₀ = 2) {p₁ d : ℤ[X]}
    (hd : d = C α * p₁) (g : ℤ[X]) {n : ℕ} (hn : 1 ≤ n) :
    C α * generalizedFibonacciPolynomial (C p₀) p₁ d g n =
      ∑ i ∈ range (n / 2 + 1),
        ((n * (n - i).choose i / (n - i) : ℕ) : ℤ[X]) * d ^ (n - 2 * i) * g ^ i

/-- **Webb–Parberry binomial identity.** For natural numbers $m < n$,
$$\binom{n-m-1}{m} = 2^{2m-n+1} \sum_{j=m}^{\lfloor (n-1)/2 \rfloor} \binom{j}{m} \binom{n}{2j+1},$$
an identity of rational numbers in which the exponent $2m-n+1$ may be negative.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.2 (1) (`fq-2024-florez11012023-lem-3.2`). -/
public theorem_wanted choose_sub_sub_one_eq_two_zpow_mul_sum {m n : ℕ} (hmn : m < n) :
    ((n - m - 1).choose m : ℚ) =
      (2 : ℚ) ^ (2 * (m : ℤ) - n + 1) *
        ∑ j ∈ Icc m ((n - 1) / 2), (j.choose m : ℚ) * (n.choose (2 * j + 1) : ℚ)

/-- **Binomial coefficients of odd lower index as an alternating sum.** For natural numbers $n$
and $k$ with $k < \lfloor (n-1)/2 \rfloor$,
$$\binom{n}{2k+1} = \sum_{i=k}^{\lfloor (n-1)/2 \rfloor} (-1)^{i-k} \, 2^{n-2i-1}
  \binom{n-i-1}{i} \binom{i}{k}.$$

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.2 (2) (`fq-2024-florez11012023-lem-3.2`). -/
public theorem_wanted choose_two_mul_add_one_eq_alternating_sum {n k : ℕ}
    (hk : k < (n - 1) / 2) :
    (n.choose (2 * k + 1) : ℤ) =
      ∑ i ∈ Icc k ((n - 1) / 2),
        (-1) ^ (i - k) * 2 ^ (n - 2 * i - 1) * ((n - i - 1).choose i : ℤ) * (i.choose k : ℤ)

/-- **Binomial coefficients of even lower index as an alternating sum.** For natural numbers $n$
and $k$ with $k < \lfloor n/2 \rfloor$,
$$\binom{n}{2k} = n \sum_{i=k}^{\lfloor n/2 \rfloor} \frac{(-1)^{i-k}}{n-i} \, 2^{n-2i-1}
  \binom{n-i}{i} \binom{i}{k},$$
an identity of rational numbers in which the exponent $n-2i-1$ may be $-1$.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.2 (3) (`fq-2024-florez11012023-lem-3.2`). -/
public theorem_wanted choose_two_mul_eq_alternating_sum {n k : ℕ} (hk : k < n / 2) :
    (n.choose (2 * k) : ℚ) =
      n * ∑ i ∈ Icc k (n / 2),
        (-1) ^ (i - k) / ((n : ℚ) - i) * (2 : ℚ) ^ ((n : ℤ) - 2 * i - 1) *
          ((n - i).choose i : ℚ) * (i.choose k : ℚ)

/-- **Catalan identity for Fibonacci-type generalized Fibonacci polynomials.** Let $d$ and $g$ be
polynomials with integer coefficients, and let $F_n$ be the generalized Fibonacci polynomials
defined by $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = d F_{n+1} + g F_n$. Then for every natural number
$n$ (for $n = 0$ both sides are $0$),
$$2^{n-1} F_n = \sum_{i=0}^{\lfloor (n-1)/2 \rfloor} \binom{n}{2i+1} d^{n-2i-1} (4g + d^2)^i.$$

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 3.3 (1) (`fq-2024-florez11012023-thm-3.3`). -/
public theorem_wanted gfp_fib_catalan (d g : ℤ[X]) (n : ℕ) :
    2 ^ (n - 1) * generalizedFibonacciPolynomial 0 1 d g n =
      ∑ i ∈ range ((n - 1) / 2 + 1),
        (n.choose (2 * i + 1) : ℤ[X]) * d ^ (n - 2 * i - 1) * (4 * g + d ^ 2) ^ i

/-- **Catalan identity for Lucas-type generalized Fibonacci polynomials.** Let $\alpha$ and $p_0$
be integers with $\alpha p_0 = 2$, let $p_1$ and $g$ be polynomials with integer coefficients, and
put $d = \alpha p_1$. Let $L_n$ be the generalized Fibonacci polynomials defined by $L_0 = p_0$,
$L_1 = p_1$ and $L_{n+2} = d L_{n+1} + g L_n$. Then for every natural number $n$,
$$2^n \alpha L_n = 2 \sum_{i=0}^{\lfloor n/2 \rfloor} \binom{n}{2i} d^{n-2i} (4g + d^2)^i.$$

Dividing both sides by $2$ gives the source's form, with $\alpha 2^{n-1} L_n$ on the left; the
factor $2$ is cleared so that $n = 0$ is included.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 3.3 (2) (`fq-2024-florez11012023-thm-3.3`). -/
public theorem_wanted gfp_lucas_catalan {α p₀ : ℤ} (hα : α * p₀ = 2) {p₁ d : ℤ[X]}
    (hd : d = C α * p₁) (g : ℤ[X]) (n : ℕ) :
    2 ^ n * C α * generalizedFibonacciPolynomial (C p₀) p₁ d g n =
      2 * ∑ i ∈ range (n / 2 + 1), (n.choose (2 * i) : ℤ[X]) * d ^ (n - 2 * i) * (4 * g + d ^ 2) ^ i

/-- **Alternating sum of shifted binomial coefficients.** Let $\ell$, $n$, $j$ and $s$ be natural
numbers with $1 \le \ell \le n$, $j \ge 1$ and $\ell j + s \le n$. Then
$$\sum_{i=0}^{\ell} (-1)^i \binom{\ell}{i} \binom{n-i}{\ell j+s} = \binom{n-\ell}{\ell(j-1)+s}.$$

The paper states this for $\lfloor (1-s)/\ell \rfloor \le j \le \lfloor (n-s)/\ell \rfloor$; only
$j \ge 1$ is stated here, since for $j \le 0$ the right side can have a negative lower index. For
$j \ge 1$ the bound $j \le \lfloor (n-s)/\ell \rfloor$ is the condition $\ell j + s \le n$.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 4.1 (`fq-2024-florez11012023-lem-4.1`). -/
public theorem_wanted alternating_sum_choose_mul_choose_sub {ℓ n j s : ℕ} (hℓ : 1 ≤ ℓ)
    (hℓn : ℓ ≤ n) (hj : 1 ≤ j) (hjn : ℓ * j + s ≤ n) :
    ∑ i ∈ range (ℓ + 1), (ℓ.choose i : ℤ) * (-1) ^ i * ((n - i).choose (ℓ * j + s) : ℤ) =
      ((n - ℓ).choose (ℓ * (j - 1) + s) : ℤ)

/-- **Recurrence for the floor-exponent binomial sums.** Let $R$ be a commutative ring, $t \in R$
and $\ell \ge 1$ an integer, and for $m \ge 0$ let
$T_\ell(m; t) = \sum_{j=0}^{m} \binom{m}{j} t^{\lfloor j/\ell \rfloor}$. Then for every integer
$n \ge 0$,
$$\sum_{i=0}^{\ell} (-1)^i \binom{\ell}{i} T_\ell(n+\ell-i; t) - t\, T_\ell(n; t) = 0.$$

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 4.2 (`fq-2024-florez11012023-thm-4.2`). -/
public theorem_wanted floorPowBinomialSum_recurrence {R : Type*} [CommRing R] (t : R) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (n : ℕ) :
    ∑ i ∈ range (ℓ + 1), (ℓ.choose i : R) * (-1) ^ i *
        ∑ j ∈ range (n + ℓ - i + 1), ((n + ℓ - i).choose j : R) * t ^ (j / ℓ) -
      t * ∑ j ∈ range (n + 1), (n.choose j : R) * t ^ (j / ℓ) = 0

/-- **Alternating sum of binomial row sums.** For all natural numbers $\ell$ and $n$,
$$\sum_{i=0}^{n} (-1)^i \binom{\ell}{i} \sum_{j=0}^{n-i} \binom{n-i}{j}
  = \sum_{i=0}^{n} (-1)^i \binom{i+\ell-n-1}{i},$$
where on the right $\binom{a}{i} = a(a-1)\cdots(a-i+1)/i!$ is the binomial coefficient with
integer upper index $a$. For $n < \ell$ the upper index $i + \ell - n - 1$ is nonnegative and this
is the ordinary binomial coefficient, the case used in Theorem 4.4.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 4.3 (`fq-2024-florez11012023-lem-4.3`). -/
public theorem_wanted alternating_choose_mul_sum_choose (ℓ n : ℕ) :
    ∑ i ∈ range (n + 1), (ℓ.choose i : ℤ) * (-1) ^ i *
        ∑ j ∈ range (n - i + 1), ((n - i).choose j : ℤ) =
      ∑ i ∈ range (n + 1), (-1) ^ i * Ring.choose ((i : ℤ) + ℓ - n - 1) i

/-- **Generating function of the floor-exponent binomial sums.** Let $R$ be a commutative ring,
$t \in R$ and $\ell \ge 1$ an integer, and for $n \ge 0$ let
$T_\ell(n; t) = \sum_{i=0}^{n} \binom{n}{i} t^{\lfloor i/\ell \rfloor}$. Then in the ring $R[[x]]$
of formal power series,
$$\Big(\sum_{n \ge 0} T_\ell(n; t)\, x^n\Big) \big((1-x)^\ell - t x^\ell\big)
  = \sum_{k=0}^{\ell-1} \Big(\sum_{i=0}^{k} (-1)^i \binom{i+\ell-k-1}{i}\Big) x^k.$$

So the generating function of the $T_\ell(n; t)$ is this polynomial divided by the series
$(1-x)^\ell - t x^\ell$, which is invertible since its constant term is $1$.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 4.4 (`fq-2024-florez11012023-thm-4.4`). -/
public theorem_wanted floorPowBinomialSum_generatingFunction {R : Type*} [CommRing R] (t : R)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    PowerSeries.mk (fun n => ∑ i ∈ range (n + 1), (n.choose i : R) * t ^ (i / ℓ)) *
        ((1 - PowerSeries.X) ^ ℓ - PowerSeries.C t * PowerSeries.X ^ ℓ) =
      ∑ k ∈ range ℓ, PowerSeries.C (∑ i ∈ range (k + 1),
        (-1 : R) ^ i * ((i + ℓ - k - 1).choose i : R)) * PowerSeries.X ^ k

/-- **Generating function of the binomial section sums.** Let $R$ be a commutative ring, $t \in R$,
and let $\ell$ and $s$ be natural numbers with $s < \ell$. Put
$T_{\ell,s}(n; t) = \sum_{i=0}^{n} \binom{n}{\ell i + s} t^i$. Then, as formal power series in $x$
over $R$,
$$\Big( \sum_{n \ge 0} T_{\ell,s}(n; t) x^n \Big) \big( (1-x)^\ell - t x^\ell \big) =
\sum_{k=0}^{\ell-1} \Big( \sum_{i=0}^{k} (-1)^i \binom{\ell}{i} \sum_{r=0}^{k} \binom{k-i}{r\ell+s}
t^r \Big) x^k.$$
That is, the generating function of $T_{\ell,s}(n; t)$ is this polynomial divided by
$(1-x)^\ell - t x^\ell$.

The printed numerator in the source has $t^t$, a typo for $t^r$ ($r$ is the summation index), and
the range $s < \ell$ is the one of (4.4). For $s \ge \ell$ the identity fails: for $\ell = 1$,
$s = 1$, $t = 2$ the left side is $x/(1-x)$ and the right side is $0$.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 4.5 (`fq-2024-florez11012023-thm-4.5`). -/
public theorem_wanted sectionBinomialSum_generatingFunction {R : Type*} [CommRing R] (t : R)
    {ℓ s : ℕ} (hs : s < ℓ) :
    PowerSeries.mk (fun n => ∑ i ∈ range (n + 1), (n.choose (ℓ * i + s) : R) * t ^ i) *
        ((1 - PowerSeries.X) ^ ℓ - PowerSeries.C t * PowerSeries.X ^ ℓ) =
      ∑ k ∈ range ℓ, PowerSeries.C (∑ i ∈ range (k + 1), (-1 : R) ^ i * (ℓ.choose i : R) *
        ∑ r ∈ range (k + 1), ((k - i).choose (r * ℓ + s) : R) * t ^ r) * PowerSeries.X ^ k

/-- **Integral representation of Fibonacci-type generalized Fibonacci polynomials.** Let $d$ and
$g$ be polynomials with integer coefficients, and let $F_n$ be the generalized Fibonacci
polynomials defined by $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = d F_{n+1} + g F_n$. If $x$ is a real
number with $d(x)^2 + 4 g(x) \ge 0$, then for every $n \ge 2$,
$$F_n(x) = \frac{n}{2^n} \int_{-1}^{1} \left( d(x) + y \sqrt{d(x)^2 + 4 g(x)} \right)^{n-1} dy.$$

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Proposition 5.1 (`fq-2024-florez11012023-prop-5.1`). -/
public theorem_wanted gfp_fib_eval_eq_integral (d g : ℤ[X]) (x : ℝ)
    (hx : 0 ≤ aeval x d ^ 2 + 4 * aeval x g) {n : ℕ} (hn : 2 ≤ n) :
    aeval x (generalizedFibonacciPolynomial 0 1 d g n) =
      n / 2 ^ n * ∫ y in (-1 : ℝ)..1,
        (aeval x d + y * Real.sqrt (aeval x d ^ 2 + 4 * aeval x g)) ^ (n - 1)

/-- **Stewart's integral formula for the Fibonacci numbers.** For every integer $n \ge 1$, the
$n$-th Fibonacci number $F_n$ (with $F_0 = 0$ and $F_1 = 1$) satisfies
$$F_n = \frac{n}{2^n} \int_{-1}^{1} \left(1 + y\sqrt{5}\right)^{n-1} dy.$$

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Corollary 5.1 (`fq-2024-florez11012023-cor-5.1`). -/
public theorem_wanted fib_eq_integral_one_add_mul_sqrt_five {n : ℕ} (hn : 1 ≤ n) :
    (Nat.fib n : ℝ) = n / 2 ^ n * ∫ y in (-1 : ℝ)..1, (1 + y * Real.sqrt 5) ^ (n - 1)

/-- **Binomial sum of generalized Fibonacci polynomials as an integral.** Let $d$ and $g$ be
polynomials with integer coefficients, let $F_m$ be the generalized Fibonacci polynomials with
$F_0 = 0$, $F_1 = 1$ and $F_{m+2} = d F_{m+1} + g F_m$, and let $x$ be a real number with
$d(x)^2 + 4 g(x) \ge 0$ and $g(x) \ne 0$. Let $\Phi \colon \mathbb{Z} \to \mathbb{R}$ satisfy
$\Phi(m) = F_m(x)$ for $m \ge 0$ and $\Phi(m+2) = d(x) \Phi(m+1) + g(x) \Phi(m)$ for every integer
$m$. Then for every real $k \ge 2$ and every integer $n \ge 1$,
$$\sum_{i=0}^{n} (-1)^{n+1} \binom{n}{i} (k+1)^i (k-1)^{n-i} g(x)^i \, \Phi(n-2i)
  = n \int_{-k}^{k} \Big(y \sqrt{d(x)^2 + 4 g(x)} + d(x)\Big)^{n-1} dy.$$

The extension $\Phi$ of $m \mapsto F_m(x)$ to negative indices exists only when $g(x) \ne 0$: if
$g(x) = 0$, the recurrence at $m = -1$ forces $F_1(x) = d(x) F_0(x) = 0$.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Proposition 5.2 (`fq-2024-florez11012023-prop-5.2`). -/
public theorem_wanted gfp_fib_binomial_sum_eq_integral (d g : ℤ[X]) (x : ℝ)
    (hx : 0 ≤ aeval x d ^ 2 + 4 * aeval x g) (hg : aeval x g ≠ 0) (F : ℤ → ℝ)
    (hF : ∀ m : ℕ, F m = aeval x (generalizedFibonacciPolynomial 0 1 d g m))
    (hrec : ∀ m : ℤ, F (m + 2) = aeval x d * F (m + 1) + aeval x g * F m)
    {k : ℝ} (hk : 2 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ range (n + 1), (-1) ^ (n + 1) * (n.choose i : ℝ) * (k + 1) ^ i * (k - 1) ^ (n - i) *
        aeval x g ^ i * F ((n : ℤ) - 2 * i) =
      n * ∫ y in -k..k, (y * Real.sqrt (aeval x d ^ 2 + 4 * aeval x g) + aeval x d) ^ (n - 1)

/-- **Binomial sum of Fibonacci numbers as an integral.** Let $F \colon \mathbb{Z} \to \mathbb{R}$
be a function whose value $F_m$ at every $m \ge 0$ is the $m$-th Fibonacci number (with $F_0 = 0$
and $F_1 = 1$) and which satisfies $F_{m+2} = F_{m+1} + F_m$ for every integer $m$. Then for every
real $k \ge 2$ and every integer $n \ge 1$,
$$\sum_{i=0}^{n} (-1)^{n+1} \binom{n}{i} (k+1)^i (k-1)^{n-i} F_{n-2i}
  = n \int_{-k}^{k} (\sqrt{5}\, y + 1)^{n-1} \, dy.$$

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Corollary 5.2 (`fq-2024-florez11012023-cor-5.2`). -/
public theorem_wanted fib_binomial_sum_eq_integral (F : ℤ → ℝ) (hF : ∀ m : ℕ, F m = Nat.fib m)
    (hrec : ∀ m : ℤ, F (m + 2) = F (m + 1) + F m) {k : ℝ} (hk : 2 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ range (n + 1), (-1) ^ (n + 1) * (n.choose i : ℝ) * (k + 1) ^ i * (k - 1) ^ (n - i) *
        F ((n : ℤ) - 2 * i) =
      n * ∫ y in -k..k, (Real.sqrt 5 * y + 1) ^ (n - 1)

end

end MetaMathlibExt
