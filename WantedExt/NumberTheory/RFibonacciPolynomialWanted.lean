/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.NegRFibonacciGeneratingFunction
public import MathlibExt.NumberTheory.NegRFibonacciPolynomial
public import MathlibExt.NumberTheory.NegRFibonacciPolynomialSum
public import MathlibExt.NumberTheory.PQRFibonacciPolynomial
public import MathlibExt.NumberTheory.RFibonacciPolynomial
public import MathlibExt.NumberTheory.RFibonacciPolynomialSum
public import MathlibExt.NumberTheory.RLucasPolynomial
public import MathlibExt.NumberTheory.RLucasPolynomialAlternatingSum
public import MathlibExt.NumberTheory.RFibonacciPolynomialNegRFibonacciEqSumRoots

namespace MetaMathlibExt

@[expose] public section

/-- **Geometrically weighted sum of $r$-Fibonacci polynomials.** Let $K$ be a field, let $r \ge 1$
be a natural number, let $x, y, m \in K$ with $1 - m x - m^{r+1} y \ne 0$, and write $U_j$ for
the $r$-Fibonacci polynomial $U^{(r)}_j(x, y)$. Then for every natural number $n$,
$$
\sum_{j=1}^{n} m^{j-1} U_j =
\frac{1 - m^n U_{n+1} - m^{r+1} y \sum_{j=1}^{r} m^{n-r+j-1} U_{n-r+j}}{1 - m x - m^{r+1} y},
$$
where the terms of the inner sum with $n - r + j \le 0$ are zero.

The paper takes $m$ a positive integer; here $m$ is any element of $K$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 4 (`integers-2025-A38-thm-4`). -/
public theorem_wanted sum_pow_mul_rFibonacciPolynomial {K : Type*} [Field K] {r : ℕ}
    (hr : 1 ≤ r) (x y m : K) (hP : 1 - m * x - m ^ (r + 1) * y ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, m ^ (j - 1) * rFibonacciPolynomial r x y j
      = (1 - m ^ n * rFibonacciPolynomial r x y (n + 1)
          - m ^ (r + 1) * y * ∑ j ∈ Finset.Icc 1 r,
              m ^ (n + j - r - 1) * rFibonacciPolynomial r x y (n + j - r))
        / (1 - m * x - m ^ (r + 1) * y)

/-- **Alternating sum of $r$-Fibonacci polynomials.** Let $K$ be a field, let $r \ge 1$ be a
natural number, let $x, y \in K$ with $1 + x + (-1)^r y \ne 0$, and write $U_j$ for the
$r$-Fibonacci polynomial $U^{(r)}_j(x, y)$. Then for every natural number $n$,
$$
\sum_{j=1}^{n} (-1)^{j-1} U_j =
\frac{1 - (-1)^n U_{n+1} + (-1)^r y \sum_{j=1}^{r} (-1)^{n-r+j-1} U_{n-r+j}}{1 + x + (-1)^r y},
$$
where the terms of the inner sum with $n - r + j \le 0$ are zero.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Corollary 3 (`integers-2025-A38-cor-3`). -/
public theorem_wanted sum_neg_one_pow_mul_rFibonacciPolynomial {K : Type*} [Field K] {r : ℕ}
    (hr : 1 ≤ r) (x y : K) (hP : 1 + x + (-1) ^ r * y ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (-1) ^ (j - 1) * rFibonacciPolynomial r x y j
      = (1 - (-1) ^ n * rFibonacciPolynomial r x y (n + 1)
          + (-1) ^ r * y * ∑ j ∈ Finset.Icc 1 r,
              (-1) ^ (n + j - r - 1) * rFibonacciPolynomial r x y (n + j - r))
        / (1 + x + (-1) ^ r * y)

/-- **Binet formula for the $r$-Fibonacci polynomials (distinct zeros).** Let $K$ be a field, let
$r \ge 1$ be a natural number and let $x, y \in K$. Suppose that
$t^{r+1} - x t^r - y = \prod_{k=0}^{r} (t - \alpha_k)$ in $K[t]$, where
$\alpha_0, \dots, \alpha_r \in K$ are pairwise distinct. Then for every $n \ge 0$ the
$r$-Fibonacci polynomials $U^{(r)}_n(x, y)$ satisfy
$$U^{(r)}_{n+1}(x, y) = \sum_{k=0}^{r} \frac{\alpha_k^{n+1}}{(r+1) \alpha_k - r x}.$$

The paper's hypothesis $y \ne -\frac{1}{r} \left( \frac{rx}{r+1} \right)^{r+1}$ is replaced by the
distinctness of the zeros it is meant to guarantee (it does not exclude the multiple zero $0$
when $y = 0$, $r \ge 2$).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 1 (`integers-2025-A38-thm-1`). -/
public theorem_wanted rFibonacciPolynomial_eq_sum_roots {K : Type*} [Field K] {r : ℕ}
    (hr : 1 ≤ r) (x y : K) (α : Fin (r + 1) → K) (hα : Function.Injective α)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C x * Polynomial.X ^ r - Polynomial.C y
      : Polynomial K) = ∏ k, (Polynomial.X - Polynomial.C (α k))) (n : ℕ) :
    rFibonacciPolynomial r x y (n + 1)
      = ∑ k, α k ^ (n + 1) / ((r + 1) * α k - r * x)

/-- **Binet formula for the $r$-Lucas polynomials (distinct zeros).** Let $K$ be a field, let
$r \ge 1$ and $s$ be natural numbers, and let $x, y \in K$. Suppose that
$t^{r+1} - x t^r - y = \prod_{k=0}^{r} (t - \alpha_k)$ in $K[t]$, where
$\alpha_0, \dots, \alpha_r \in K$ are pairwise distinct. Then for every $n \ge 0$ the
$r$-Lucas polynomials of type $s$ satisfy
$$V^{(r,s)}_n(x, y) = \sum_{k=0}^{r} \frac{\alpha_k^n ((s+1)\alpha_k - s x)}{(r+1)\alpha_k - r x}.$$

The paper takes $1 \le s \le r$; the identity holds for every $s$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 1 (`integers-2025-A38-thm-1`). -/
public theorem_wanted rLucasPolynomial_eq_sum_roots {K : Type*} [Field K] {r : ℕ}
    (hr : 1 ≤ r) (s : ℕ) (x y : K) (α : Fin (r + 1) → K) (hα : Function.Injective α)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C x * Polynomial.X ^ r - Polynomial.C y
      : Polynomial K) = ∏ k, (Polynomial.X - Polynomial.C (α k))) (n : ℕ) :
    rLucasPolynomial r s x y n
      = ∑ k, α k ^ n * ((s + 1) * α k - s * x) / ((r + 1) * α k - r * x)

/-- **Binet formula for the r-Fibonacci polynomials with one double zero.** Let $K$ be a field
of characteristic zero, let $r \ge 1$ be a natural number, and let $x, y, \alpha \in K$. Let
$\beta_1, \dots, \beta_{r-1} \in K$ be pairwise distinct and all different from $\alpha$, put
$\tilde P(t) = \prod_{k=1}^{r-1} (t - \beta_k)$, and suppose that
$t^{r+1} - x t^r - y = (t - \alpha)^2 \tilde P(t)$ as polynomials over $K$. Then for every
natural number $n$ the $r$-Fibonacci polynomial $U^{(r)}$ satisfies
$$
U^{(r)}_{n+1}(x, y) = \frac{\alpha^{n+r-1}}{\tilde P(\alpha)}
\Bigl((n + r) - \frac{\alpha \tilde P'(\alpha)}{\tilde P(\alpha)}\Bigr) +
\sum_{k=1}^{r-1} \frac{\beta_k^{n+1}}{(r+1)\beta_k - r x}.
$$

The paper's hypothesis $y = -\frac{1}{r}\bigl(\frac{rx}{r+1}\bigr)^{r+1}$ (which makes
$\alpha = rx/(r+1)$ the double zero) is replaced by the factorization it yields.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 1 (`integers-2025-A38-thm-1`). -/
public theorem_wanted rFibonacciPolynomial_eq_of_double_root {K : Type*} [Field K]
    [CharZero K] {r : ℕ} (hr : 1 ≤ r) (x y α : K) (β : Fin (r - 1) → K)
    (hβ : Function.Injective β) (hβα : ∀ k, β k ≠ α)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C x * Polynomial.X ^ r - Polynomial.C y
      : Polynomial K) = (Polynomial.X - Polynomial.C α) ^ 2 *
        ∏ k, (Polynomial.X - Polynomial.C (β k))) (n : ℕ) :
    rFibonacciPolynomial r x y (n + 1)
      = α ^ (n + r - 1) / (∏ k, (Polynomial.X - Polynomial.C (β k))).eval α *
          ((n + r : K) - α * (Polynomial.derivative
              (∏ k, (Polynomial.X - Polynomial.C (β k)))).eval α /
            (∏ k, (Polynomial.X - Polynomial.C (β k))).eval α)
        + ∑ k, β k ^ (n + 1) / ((r + 1) * β k - r * x)

/-- **Binet formula for the $r$-Lucas polynomials (one double zero).** Let $K$ be a field of
characteristic zero, let $r \ge 1$ and $s$ be natural numbers, and let $x, y, \alpha \in K$ with
$\alpha \ne 0$. Suppose that $t^{r+1} - x t^r - y = (t - \alpha)^2 \tilde P(t)$ in $K[t]$, where
$\tilde P(t) = \prod_{k=1}^{r-1} (t - \beta_k)$ for pairwise distinct
$\beta_1, \dots, \beta_{r-1} \in K$, all different from $\alpha$. Then for every $n \ge 0$ the
$r$-Lucas polynomials of type $s$ satisfy
$$V^{(r,s)}_n(x, y) = \frac{\alpha^{n+r-1}}{\tilde P(\alpha)} \left( n \, \frac{r-s}{r} + r +
\frac{s}{r} - \alpha \, \frac{r-s}{r} \, \frac{\tilde P'(\alpha)}{\tilde P(\alpha)} \right) +
\sum_{k=1}^{r-1} \frac{\beta_k^n ((s+1) \beta_k - s x)}{(r+1) \beta_k - r x}.$$

The paper's hypothesis $y = -\frac{1}{r} \left( \frac{rx}{r+1} \right)^{r+1}$ (which makes
$\alpha = rx/(r+1)$ the double zero) is replaced by the factorization it yields. The paper takes
$1 \le s \le r$; the identity holds for every $s$. The hypothesis $\alpha \ne 0$ is added: for
$r = 2$, $y = 0$ the factorization $t^2 (t - x)$ has $\alpha = 0$ and the formula fails at $n = 0$
(for $x = s = 1$: $V_0 = 2$, right side $1$). In the paper's setting $\alpha = rx/(r+1)$ with
$x \ne 0$, so $\alpha \ne 0$; the only other $\alpha = 0$ case, $r = 1$, $x = y = 0$, is dropped.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 1 (`integers-2025-A38-thm-1`). -/
public theorem_wanted rLucasPolynomial_eq_of_double_root {K : Type*} [Field K]
    [CharZero K] {r : ℕ} (hr : 1 ≤ r) (s : ℕ) (x y α : K) (hα : α ≠ 0) (β : Fin (r - 1) → K)
    (hβ : Function.Injective β) (hβα : ∀ k, β k ≠ α)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C x * Polynomial.X ^ r - Polynomial.C y
      : Polynomial K) = (Polynomial.X - Polynomial.C α) ^ 2 *
        ∏ k, (Polynomial.X - Polynomial.C (β k))) (n : ℕ) :
    rLucasPolynomial r s x y n
      = α ^ (n + r - 1) / (∏ k, (Polynomial.X - Polynomial.C (β k))).eval α *
          (n * ((r - s) / r) + (r + s / r) - α * ((r - s) / r) *
            (Polynomial.derivative (∏ k, (Polynomial.X - Polynomial.C (β k)))).eval α /
              (∏ k, (Polynomial.X - Polynomial.C (β k))).eval α)
        + ∑ k, β k ^ n * ((s + 1) * β k - s * x) / ((r + 1) * β k - r * x)

/-- **Second recurrence for the $(p,q)$-analogue of the $r$-Fibonacci polynomial.** Let $R$ be a
commutative semiring, let $r \ge 1$, $n \ge r$ and $m$ be natural numbers and let
$x, y, p, q \in R$. Write $U_j(x, y)$ for $U^{(r)}_j(x, y, p, q, m)$, the $(p,q)$-analogue of the
$r$-Fibonacci polynomial with $r$, $p$, $q$ and $m$ fixed. Then
$$U_{n+1}(x, y) = p x \, U_n(p x, p y) + q y \, U_{n-r}(q x, q^{m+1} y).$$

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 2, Equation (5) (`integers-2025-A38-thm-2`). -/
public theorem_wanted pqRFibonacci_succ_eq_right {R : Type*} [CommSemiring R] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (x y p q : R) (m : ℕ) :
    pqRFibonacci r x y p q m (n + 1)
      = p * x * pqRFibonacci r (p * x) (p * y) p q m n
        + q * y * pqRFibonacci r (q * x) (q ^ (m + 1) * y) p q m (n - r)

/-- **First-kind (p, q)-Lucas polynomials.** Let $R$ be a commutative semiring, let $r$, $s$ and
$m$ be natural numbers, let $x, y, p, q \in R$, and write $[a, b]_{p,q}$ for the
$(p, q)$-binomial coefficients. The first-kind $(p, q)$-analogue $V^{(r,s)}_n(x, y, p, q, m)$ of
the $r$-Lucas polynomial of type $s$, written $V_n$, is defined by $V_0 = s + 1$ and, for
$n \ge 1$,
$$
V_n = \sum_{k=0}^{\lfloor n/(r+1) \rfloor} p^{\binom{n-(r+1)k}{2}} q^{(m+1)\binom{k}{2}}\,
c_{n,k}\,x^{n-(r+1)k} y^k,
$$
where $c_{n,0} = [n, 0]_{p,q}$ and, for $k \ge 1$,
$c_{n,k} = [n - rk, k]_{p,q} + s\,p^{n-(r+1)k} [n - rk - 1, k - 1]_{p,q}$.

The paper writes $c_{n,k}$ as
$[n - rk, k]_{p,q} (1 + s\,p^{n-(r+1)k} [k]_{p,q} / [n - rk]_{p,q})$, with $[a]_{p,q}$ the
$(p, q)$-numbers; the division-free form is the first step of the paper's proof of Theorem 3
and agrees with it whenever $[n - rk]_{p,q} \ne 0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 2. -/
public def pqRLucas {R : Type*} [CommSemiring R] (r s : ℕ) (x y p q : R) (m : ℕ) : ℕ → R
  | 0 => (s : R) + 1
  | n + 1 => ∑ k ∈ Finset.range ((n + 1) / (r + 1) + 1),
      p ^ (n + 1 - (r + 1) * k).choose 2 * q ^ ((m + 1) * k.choose 2) *
        (pqBinomial p q (n + 1 - r * k) k +
          if k = 0 then 0 else s * p ^ (n + 1 - (r + 1) * k) * pqBinomial p q (n - r * k) (k - 1)) *
        x ^ (n + 1 - (r + 1) * k) * y ^ k

/-- **Initial value of the first-kind (p, q)-Lucas polynomials.** Let $R$ be a commutative
semiring, let $r$, $s$ and $m$ be natural numbers, and let $x, y, p, q \in R$. The first-kind
$(p, q)$-analogue $V^{(r,s)}_n(x, y, p, q, m)$ of the $r$-Lucas polynomial of type $s$ satisfies
$V^{(r,s)}_0(x, y, p, q, m) = s + 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 2. -/
public theorem pqRLucas_zero {R : Type*} [CommSemiring R] (r s : ℕ) (x y p q : R) (m : ℕ) :
    pqRLucas r s x y p q m 0 = (s : R) + 1 := rfl

/-- **Second-kind (p, q)-Lucas polynomials.** Let $K$ be a field, let $r$, $s$ and $m$ be natural
numbers, let $x, y, p, q \in K$, and write $[a, b]_{p,q}$ for the $(p, q)$-binomial
coefficients. The second-kind $(p, q)$-analogue $\mathbb{V}^{(r,s)}_n(x, y, p, q, m)$ of the
$r$-Lucas polynomial of type $s$, written $\mathbb{V}_n$, is defined by $\mathbb{V}_0 = s + 1$
and, for $n \ge 1$,
$$
\mathbb{V}_n = \sum_{k=0}^{\lfloor n/(r+1) \rfloor}
\frac{p^{\binom{n-(r+1)k}{2}} q^{\binom{k+1}{2} + m\binom{k}{2}}}{p^k}\,
d_{n,k}\,x^{n-(r+1)k} y^k,
$$
where $d_{n,0} = [n, 0]_{p,q}$ and, for $k \ge 1$,
$d_{n,k} = [n - rk, k]_{p,q} + s\,q^{n-(r+1)k} [n - rk - 1, k - 1]_{p,q}$. Division by $0$ is
read as $0$, so for $p = 0$ every term with $k \ge 1$ vanishes.

The paper writes $d_{n,k}$ as
$[n - rk, k]_{p,q} (1 + s\,q^{n-(r+1)k} [k]_{p,q} / [n - rk]_{p,q})$, with $[a]_{p,q}$ the
$(p, q)$-numbers; the two agree whenever $[n - rk]_{p,q} \ne 0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 2. -/
public def pqRLucasSecond {K : Type*} [Field K] (r s : ℕ) (x y p q : K) (m : ℕ) : ℕ → K
  | 0 => (s : K) + 1
  | n + 1 => ∑ k ∈ Finset.range ((n + 1) / (r + 1) + 1),
      p ^ (n + 1 - (r + 1) * k).choose 2 * q ^ ((k + 1).choose 2 + m * k.choose 2) / p ^ k *
        (pqBinomial p q (n + 1 - r * k) k +
          if k = 0 then 0 else s * q ^ (n + 1 - (r + 1) * k) * pqBinomial p q (n - r * k) (k - 1)) *
        x ^ (n + 1 - (r + 1) * k) * y ^ k

/-- **Initial value of the second-kind (p, q)-Lucas polynomials.** Let $K$ be a field, let $r$,
$s$ and $m$ be natural numbers, and let $x, y, p, q \in K$. The second-kind $(p, q)$-analogue
$\mathbb{V}^{(r,s)}_n(x, y, p, q, m)$ of the $r$-Lucas polynomial of type $s$ satisfies
$\mathbb{V}^{(r,s)}_0(x, y, p, q, m) = s + 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 2. -/
public theorem pqRLucasSecond_zero {K : Type*} [Field K] (r s : ℕ) (x y p q : K) (m : ℕ) :
    pqRLucasSecond r s x y p q m 0 = (s : K) + 1 := rfl

/-- **Splitting formula for first-kind (p, q)-Lucas polynomials.** Let $K$ be a field, let
$r \ge 1$, $s$ and $m$ be natural numbers, and let $x, y, p, q \in K$ with $p \ne 0$ and
$q \ne 0$. Write $U_n(x, y)$ for the $(p, q)$-analogue of the $r$-Fibonacci polynomial with
parameters $p, q, m$, and $V_n(x, y)$ for the first-kind $(p, q)$-analogue of the $r$-Lucas
polynomial of type $s$ with the same parameters. Then for every natural number $n \ge r$,
$$
V_n(x, y) = U_{n+1}(x/p, y/q) + s\,y\,U_{n-r}(x, y q^m).
$$

The paper takes positive $s$; the identity holds for every natural number $s$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 1 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucas_eq_pqRFibonacci_add {K : Type*} [Field K] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (s : ℕ) (x y p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (m : ℕ) :
    pqRLucas r s x y p q m n
      = pqRFibonacci r (x / p) (y / q) p q m (n + 1)
        + s * y * pqRFibonacci r x (y * q ^ m) p q m (n - r)

/-- **Splitting formula for second-kind (p, q)-Lucas polynomials.** Let $K$ be a field, let
$r \ge 1$, $s$ and $m$ be natural numbers, and let $x, y, p, q \in K$ with $p \ne 0$ and
$q \ne 0$. Write $U_n(x, y)$ for the $(p, q)$-analogue of the $r$-Fibonacci polynomial with
parameters $p, q, m$, and $\mathbb{V}_n(x, y)$ for the second-kind $(p, q)$-analogue of the
$r$-Lucas polynomial of type $s$ with the same parameters. Then for every natural number
$n \ge r$,
$$
\mathbb{V}_n(x, y) = U_{n+1}(x/p, y/p) + s\,y\,(q/p)^{n-r}\,U_{n-r}(x, y p^r q^m / q^r).
$$

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 1 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucasSecond_eq_pqRFibonacci_add {K : Type*} [Field K] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (s : ℕ) (x y p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (m : ℕ) :
    pqRLucasSecond r s x y p q m n
      = pqRFibonacci r (x / p) (y / p) p q m (n + 1)
        + s * y * (q / p) ^ (n - r) * pqRFibonacci r x (y * p ^ r * q ^ m / q ^ r) p q m (n - r)

/-- **First-kind (p, q)-Lucas polynomials as a difference of (p, q)-Fibonacci polynomials.** Let
$K$ be a field, let $r \ge 1$, $s$ and $m$ be natural numbers, and let $x, y, p, q \in K$ with
$p \ne 0$ and $q \ne 0$. Write $U_n(x, y)$ for the $(p, q)$-analogue of the $r$-Fibonacci
polynomial with parameters $p, q, m$, and $V_n(x, y)$ for the first-kind $(p, q)$-analogue of
the $r$-Lucas polynomial of type $s$ with the same parameters. Then for every natural number $n$,
$$
V_n(x, y) = (s + 1)\,U_{n+1}(x/p, y/q) - s\,x\,U_n(x, y).
$$

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 2 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucas_eq_succ_mul_sub {K : Type*} [Field K] {r : ℕ} (hr : 1 ≤ r)
    (s : ℕ) (x y p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (m n : ℕ) :
    pqRLucas r s x y p q m n
      = (s + 1) * pqRFibonacci r (x / p) (y / q) p q m (n + 1)
        - s * x * pqRFibonacci r x y p q m n

/-- **Second-kind (p, q)-Lucas polynomials as a difference of (p, q)-Fibonacci polynomials.** Let
$K$ be a field, let $r \ge 1$, $s$ and $m$ be natural numbers, and let $x, y, p, q \in K$ with
$p \ne 0$. Write $U_n(x, y)$ for the $(p, q)$-analogue of the $r$-Fibonacci polynomial with
parameters $p, q, m$, and $\mathbb{V}_n(x, y)$ for the second-kind $(p, q)$-analogue of the
$r$-Lucas polynomial of type $s$ with the same parameters. Then for every natural number $n$,
$$
\mathbb{V}_n(x, y) = (s + 1)\,U_{n+1}(x/p, y/p) - s\,x\,U_n(x, y).
$$

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 2 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucasSecond_eq_succ_mul_sub {K : Type*} [Field K] {r : ℕ}
    (hr : 1 ≤ r) (s : ℕ) (x y p q : K) (hp : p ≠ 0) (m n : ℕ) :
    pqRLucasSecond r s x y p q m n
      = (s + 1) * pqRFibonacci r (x / p) (y / p) p q m (n + 1)
        - s * x * pqRFibonacci r x y p q m n

/-- **First-kind $(p,q)$-analogue of the $r$-Lucas polynomial via two $r$-Fibonacci terms.** Let
$R$ be a commutative semiring, let $r \ge 1$, $n \ge r$, $s$ and $m$ be natural numbers and let
$x, y, p, q \in R$. Write $U_j(x, y)$ for the $(p,q)$-analogue $U^{(r)}_j(x, y, p, q, m)$ of the
$r$-Fibonacci polynomial and $V_n(x, y)$ for the first-kind $(p,q)$-analogue
$V^{(r,s)}_n(x, y, p, q, m)$ of the $r$-Lucas polynomial of type $s$, with $r$, $s$, $p$, $q$
and $m$ fixed. Then
$$V_n(x, y) = x \, U_n(x, y) + (1 + s) \, y \, U_{n-r}(x, y q^m).$$

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 3 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucas_eq_mul_add {R : Type*} [CommSemiring R] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (s : ℕ) (x y p q : R) (m : ℕ) :
    pqRLucas r s x y p q m n
      = x * pqRFibonacci r x y p q m n
        + (1 + s) * y * pqRFibonacci r x (y * q ^ m) p q m (n - r)

/-- **Recurrence-type formula for second-kind (p, q)-Lucas polynomials.** Let $K$ be a field, let
$r \ge 1$, $s$ and $m$ be natural numbers, and let $x, y, p, q \in K$ with $p \ne 0$ and
$q \ne 0$. Write $U_n(x, y)$ for the $(p, q)$-analogue of the $r$-Fibonacci polynomial with
parameters $p, q, m$, and $\mathbb{V}_n(x, y)$ for the second-kind $(p, q)$-analogue of the
$r$-Lucas polynomial of type $s$ with the same parameters. Then for every natural number
$n \ge r$,
$$
\mathbb{V}_n(x, y) = x\,U_n(x, y) + (1 + s)\,(q/p)^{n-r}\,y\,U_{n-r}(x, y p^r q^m / q^r).
$$

The paper writes the second argument as $y p^r q^{m-r}$ and drops $p, q$ from the argument list
$(x, y p^r q^{m-r}, m)$; they are unchanged.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 3 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucasSecond_eq_mul_add {K : Type*} [Field K] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (s : ℕ) (x y p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (m : ℕ) :
    pqRLucasSecond r s x y p q m n
      = x * pqRFibonacci r x y p q m n
        + (1 + s) * (q / p) ^ (n - r) * y *
            pqRFibonacci r x (y * p ^ r * q ^ m / q ^ r) p q m (n - r)

/-- **Geometrically weighted sum of $r$-Lucas polynomials.** Let $K$ be a field, let $r \ge 1$ and
$s$ be natural numbers, let $x, y, m \in K$ with $1 - m x - m^{r+1} y \ne 0$, and write $V_j$ for
the $r$-Lucas polynomial of type $s$, $V_j = V^{(r,s)}_j(x, y)$. Then for every natural number
$n \ge r - 1$,
$$
\sum_{j=1}^{n} m^j V_j =
\frac{1 + s m^{r+1} y - m^{n+1} V_{n+1} - m^{r+1} y \sum_{j=1}^{r} m^{n-r+j} V_{n-r+j}}
{1 - m x - m^{r+1} y} - 1.
$$

The paper takes $m$ a positive integer (here any element of $K$) and states no range for $n$; for
$n < r - 1$ the right side involves $V$ at negative indices.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 5 (`integers-2025-A38-thm-5`). -/
public theorem_wanted sum_pow_mul_rLucasPolynomial {K : Type*} [Field K] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n + 1) (s : ℕ) (x y m : K) (hP : 1 - m * x - m ^ (r + 1) * y ≠ 0) :
    ∑ j ∈ Finset.Icc 1 n, m ^ j * rLucasPolynomial r s x y j
      = (1 + s * m ^ (r + 1) * y - m ^ (n + 1) * rLucasPolynomial r s x y (n + 1)
          - m ^ (r + 1) * y * ∑ j ∈ Finset.Icc 1 r,
              m ^ (n + j - r) * rLucasPolynomial r s x y (n + j - r))
        / (1 - m * x - m ^ (r + 1) * y) - 1

/-- **Explicit sum for the companion sequence $V^{(-r)}$.** Let $K$ be a field of
characteristic zero, $r \ge 2$ and $n \ge 1$ natural numbers, $x \in K$ and $y$ a unit of
$K$, and let $V^{(-r)}_n(x, y)$ be the companion sequence of the $(-r)$-Fibonacci
polynomials. Then

$$V^{(-r)}_n(x, y) = \sum_{k} \frac{n}{n - rk} \binom{k - 1}{n - 1 - rk} y^{-k} \,
(-x)^{n - rk} + \varepsilon,$$

where the sum runs over the natural numbers $k \ge 1$ with $rk < n$, $\binom{a}{b}$ is the
binomial coefficient of natural numbers (zero when $b > a$), and $\varepsilon = r y^{-n/r}$ if
$r$ divides $n$ and $\varepsilon = 0$ otherwise.

The paper's range $\lfloor n/(r+1) \rfloor \le k \le \lfloor n/r \rfloor$ also admits $k = n/r$
(division by zero; that term is the $\varepsilon$ term) and, for $n \le r$, $k = 0$, whose term
$\binom{-1}{n-1}$ must be read as $0$ (with $\binom{-1}{j} = (-1)^j$, $r = 2$, $n = 1$ gives
$-x$ instead of $V^{(-r)}_1 = 0$); both are excluded.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 7 (`integers-2025-A38-thm-7`). -/
public theorem_wanted negRLucas_eq_sum {K : Type*} [Field K] [CharZero K] {r n : ℕ}
    (hr : 2 ≤ r) (hn : 1 ≤ n) (x : K) (y : Kˣ) :
    negRLucas r x y n
      = ∑ k ∈ (Finset.Icc 1 (n / r)).filter (fun k => r * k < n),
          (n : K) / ((n : K) - ((r * k : ℕ) : K)) * ((k - 1).choose (n - 1 - r * k) : K) *
            (↑y⁻¹ : K) ^ k * (-x) ^ (n - r * k)
        + if r ∣ n then (r : K) * (↑y⁻¹ : K) ^ (n / r) else 0

/-- **Explicit sum for the (-r)-Lucas polynomials, second form.** Let $K$ be a field of
characteristic zero, $r \ge 2$, $x \in K$ and $y \in K$ nonzero, and write
$V_n = V^{(-r)}_n(x, y)$ for the companion $(-r)$-Lucas sequence. For every $n \ge 1$, $V_n$ is
the sum of
$$\frac{n}{k+1} \binom{(n-1-r-k)/r}{k} y^{-(n-1-k)/r} (-x)^{k+1}$$
over the integers $k$ with $0 \le k \le \lfloor n/(r+1) \rfloor - 1$ and $r \mid n - k - 1$,
plus $r y^{-n/r}$ when $r \mid n$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 7 (`integers-2025-A38-thm-7`). -/
public theorem_wanted negRLucas_eq_sum' {K : Type*} [Field K] [CharZero K] {r n : ℕ}
    (hr : 2 ≤ r) (hn : 1 ≤ n) (x : K) (y : Kˣ) :
    negRLucas r x y n
      = ∑ k ∈ (Finset.range (n / (r + 1))).filter (fun k => r ∣ n - k - 1),
          (n : K) / (k + 1) * (((n - 1 - r - k) / r).choose k : K) *
            (↑y⁻¹ : K) ^ ((n - 1 - k) / r) * (-x) ^ (k + 1)
        + if r ∣ n then (r : K) * (↑y⁻¹ : K) ^ (n / r) else 0

/-- **Generating function of the companion sequence $V^{(-r)}$.** Let $A$ be a commutative
ring, $r \ge 2$ a natural number, $x \in A$ and $y$ a unit of $A$, and let $V^{(-r)}_n(x, y)$
be the companion sequence of the $(-r)$-Fibonacci polynomials. In the ring $A[[z]]$ of formal
power series,

$$(1 - y^{-1} z^r + x y^{-1} z^{r+1}) \sum_{n \ge 0} V^{(-r)}_n(x, y) z^n = r + 1 - y^{-1} z^r.$$

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 8 (`integers-2025-A38-thm-8`). -/
public theorem_wanted negRLucas_generatingFunction {A : Type*} [CommRing A] {r : ℕ}
    (hr : 2 ≤ r) (x : A) (y : Aˣ) :
    (1 - PowerSeries.C (↑y⁻¹ : A) * PowerSeries.X ^ r
        + PowerSeries.C (x * ↑y⁻¹) * PowerSeries.X ^ (r + 1)) *
      PowerSeries.mk (fun n => negRLucas r x y n)
      = PowerSeries.C ((r : A) + 1) - PowerSeries.C (↑y⁻¹ : A) * PowerSeries.X ^ r

/-- **Binet formula for the companion sequence $V^{(-r)}$.** Let $K$ be a field, $r \ge 2$ a
natural number, $x \in K$ and $y$ a unit of $K$, and let $V^{(-r)}_n(x, y)$ be the companion
sequence of the $(-r)$-Fibonacci polynomials. Suppose $\beta_0, \dots, \beta_r \in K$ are
pairwise distinct and $t^{r+1} - y^{-1} t + x y^{-1} = \prod_{k=0}^{r} (t - \beta_k)$ in the
polynomial ring $K[t]$. Then $V^{(-r)}_n(x, y) = \sum_{k=0}^{r} \beta_k^n$ for every natural
number $n$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 9 (`integers-2025-A38-thm-9`). -/
public theorem_wanted negRLucas_eq_sum_roots {K : Type*} [Field K] {r : ℕ} (hr : 2 ≤ r)
    (x : K) (y : Kˣ) (β : Fin (r + 1) → K) (hβ : Function.Injective β)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C (↑y⁻¹ : K) * Polynomial.X
      + Polynomial.C (x * ↑y⁻¹) : Polynomial K) = ∏ k, (Polynomial.X - Polynomial.C (β k)))
    (n : ℕ) :
    negRLucas r x y n = ∑ k, β k ^ n

end

end MetaMathlibExt
