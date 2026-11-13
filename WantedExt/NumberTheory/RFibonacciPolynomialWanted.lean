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
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.GaussianBinomial

namespace MetaMathlibExt

@[expose] public section

/-- **The $r$-Fibonacci polynomials.** Let $R$ be a commutative semiring, let $r$ be a natural
number and let $x, y \in R$. The $r$-Fibonacci polynomials $U^{(r)}_n(x, y) \in R$, $n \ge 0$, are
defined by $U^{(r)}_0 = 0$, $U^{(r)}_k = x^{k-1}$ for $1 \le k \le r$, and
$U^{(r)}_{n+1} = x \, U^{(r)}_n + y \, U^{(r)}_{n-r}$ for $n \ge r$.

These are the initial values and recurrence displayed for $\xi_n = m^{n-1} U_n$ in the paper,
at $m = 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public def rFibonacciPolynomial {R : Type*} [CommSemiring R] (r : ℕ) (x y : R) : ℕ → R
  | 0 => 0
  | n + 1 =>
    if n < r then x ^ n
    else x * rFibonacciPolynomial r x y n + y * rFibonacciPolynomial r x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- **The zeroth $r$-Fibonacci polynomial vanishes.** For every natural number $r$ and all
$x, y$ in a commutative semiring $R$, the $r$-Fibonacci polynomial $U^{(r)}_0(x, y)$ is $0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public theorem rFibonacciPolynomial_zero {R : Type*} [CommSemiring R] (r : ℕ) (x y : R) :
    rFibonacciPolynomial r x y 0 = 0 := by
  rw [rFibonacciPolynomial]

/-- **Initial values of the $r$-Fibonacci polynomials.** Let $R$ be a commutative semiring, let
$x, y \in R$, and let $n < r$ be natural numbers. Then the $r$-Fibonacci polynomial
$U^{(r)}_{n+1}(x, y)$ equals $x^n$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public theorem rFibonacciPolynomial_succ_of_lt {R : Type*} [CommSemiring R] {r n : ℕ}
    (x y : R) (h : n < r) : rFibonacciPolynomial r x y (n + 1) = x ^ n := by
  rw [rFibonacciPolynomial]
  simp [h]

/-- **Recurrence for the $r$-Fibonacci polynomials.** Let $R$ be a commutative semiring, let
$x, y \in R$, and let $r \le n$ be natural numbers. Then the $r$-Fibonacci polynomials
$U_m = U^{(r)}_m(x, y)$ satisfy $U_{n+1} = x \, U_n + y \, U_{n-r}$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public theorem rFibonacciPolynomial_succ_of_le {R : Type*} [CommSemiring R] {r n : ℕ}
    (x y : R) (h : r ≤ n) :
    rFibonacciPolynomial r x y (n + 1)
      = x * rFibonacciPolynomial r x y n + y * rFibonacciPolynomial r x y (n - r) := by
  rw [rFibonacciPolynomial]
  simp [show ¬n < r by omega]

/-- **The $1$-Fibonacci polynomials at $x = y = 1$ are the Fibonacci numbers.** For every
natural number $n$, the $r$-Fibonacci polynomial with $r = 1$, evaluated at $x = y = 1$ in the
natural numbers, is the $n$-th Fibonacci number: $U^{(1)}_n(1, 1) = F_n$, where $F_0 = 0$,
$F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rFibonacciPolynomial_one_one_one :
    ∀ n, rFibonacciPolynomial 1 (1 : ℕ) 1 n = Nat.fib n
  | 0 => by rw [rFibonacciPolynomial_zero]; rfl
  | 1 => by rw [rFibonacciPolynomial_succ_of_lt _ _ (by omega)]; simp
  | n + 2 => by
    rw [rFibonacciPolynomial_succ_of_le _ _ (by omega), rFibonacciPolynomial_one_one_one (n + 1),
      show n + 1 - 1 = n by omega, rFibonacciPolynomial_one_one_one n, Nat.fib_add_two]
    ring

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

/-- **Sum of the first $n$ $r$-Fibonacci polynomials.** Let $K$ be a field, let $r \ge 1$ be a
natural number, let $x, y \in K$ with $1 - x - y \ne 0$, and write $U_j$ for the $r$-Fibonacci
polynomial $U^{(r)}_j(x, y)$. Then for every natural number $n$,
$$
\sum_{j=1}^{n} U_j = \frac{1 - U_{n+1} - y \sum_{j=1}^{r} U_{n-r+j}}{1 - x - y},
$$
where the terms of the inner sum with $n - r + j \le 0$ are zero.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Corollary 2 (`integers-2025-A38-cor-2`). -/
public theorem_wanted sum_rFibonacciPolynomial {K : Type*} [Field K] {r : ℕ} (hr : 1 ≤ r)
    (x y : K) (hP : 1 - x - y ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, rFibonacciPolynomial r x y j
      = (1 - rFibonacciPolynomial r x y (n + 1)
          - y * ∑ j ∈ Finset.Icc 1 r, rFibonacciPolynomial r x y (n + j - r))
        / (1 - x - y)

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


/-- **The $r$-Lucas polynomials of type $s$.** Let $R$ be a commutative semiring, let $r$ and $s$
be natural numbers and let $x, y \in R$. The $r$-Lucas polynomials of type $s$ are the sequence
$V_n = V^{(r,s)}_n(x, y)$, $n \ge 0$, of elements of $R$ given by $V_0 = s + 1$, $V_k = x^k$ for
$1 \le k \le r$, and $V_{n+1} = x V_n + y V_{n-r}$ for $n \ge r$.

The paper takes $1 \le s \le r$; the definition makes sense for every natural number $s$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public def rLucasPolynomial {R : Type*} [CommSemiring R] (r s : ℕ) (x y : R) : ℕ → R
  | 0 => (s : R) + 1
  | n + 1 =>
    if n < r then x ^ (n + 1)
    else x * rLucasPolynomial r s x y n + y * rLucasPolynomial r s x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- **Initial value of the $r$-Lucas polynomials.** For every commutative semiring $R$, all natural
numbers $r$ and $s$ and all $x, y \in R$, the $r$-Lucas polynomial of type $s$ satisfies
$V^{(r,s)}_0(x, y) = s + 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rLucasPolynomial_zero {R : Type*} [CommSemiring R] (r s : ℕ) (x y : R) :
    rLucasPolynomial r s x y 0 = (s : R) + 1 := by
  rw [rLucasPolynomial]

/-- **Initial values of the $r$-Lucas polynomials.** Let $R$ be a commutative semiring, let $s$ be
a natural number, let $x, y \in R$, and let $n < r$ be natural numbers. Then the $r$-Lucas
polynomial of type $s$ satisfies $V^{(r,s)}_{n+1}(x, y) = x^{n+1}$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rLucasPolynomial_succ_of_lt {R : Type*} [CommSemiring R] {r n : ℕ} (s : ℕ)
    (x y : R) (h : n < r) : rLucasPolynomial r s x y (n + 1) = x ^ (n + 1) := by
  rw [rLucasPolynomial]
  simp [h]

/-- **Recurrence for the $r$-Lucas polynomials.** Let $R$ be a commutative semiring, let $s$ be a
natural number, let $x, y \in R$, and let $r \le n$ be natural numbers. Then the $r$-Lucas
polynomials of type $s$, $V_m = V^{(r,s)}_m(x, y)$, satisfy $V_{n+1} = x \, V_n + y \, V_{n-r}$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rLucasPolynomial_succ_of_le {R : Type*} [CommSemiring R] {r n : ℕ} (s : ℕ)
    (x y : R) (h : r ≤ n) :
    rLucasPolynomial r s x y (n + 1)
      = x * rLucasPolynomial r s x y n + y * rLucasPolynomial r s x y (n - r) := by
  rw [rLucasPolynomial]
  simp [show ¬n < r by omega]

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

/-- **$(p,q)$-binomial coefficient.** Let $R$ be a commutative semiring and $p, q \in R$. For
natural numbers $n$ and $k$, the $(p,q)$-binomial coefficient $\binom{n}{k}_{p,q} \in R$ is
defined recursively by $\binom{n}{0}_{p,q} = 1$, $\binom{0}{k+1}_{p,q} = 0$ and
$\binom{n+1}{k+1}_{p,q} = p^{n-k} \binom{n}{k}_{p,q} + q^{k+1} \binom{n}{k+1}_{p,q}$, where $n - k$
is truncated subtraction ($0$ when $k > n$).

For $k \le n$, where the $(p,q)$-factorials are invertible, $\binom{n}{k}_{p,q}$ equals
$[n]_{p,q}! / ([k]_{p,q}! \, [n-k]_{p,q}!)$, where $[j]_{p,q} = p^{j-1} + p^{j-2} q + \dots +
q^{j-1}$; this is the definition used in the source. At $p = 1$ it is the Gaussian binomial
coefficient $\binom{n}{k}_q$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3, Equation (3). -/
public def pqBinomial {R : Type*} [CommSemiring R] (p q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => p ^ (n - k) * pqBinomial p q n k + q ^ (k + 1) * pqBinomial p q n (k + 1)

/-- **$(p,q)$-binomial coefficients with lower index zero.** For all elements $p, q$ of a
commutative semiring and every natural number $n$, the $(p,q)$-binomial coefficient
$\binom{n}{0}_{p,q}$ equals $1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3. -/
public theorem pqBinomial_zero_right {R : Type*} [CommSemiring R] (p q : R) (n : ℕ) :
    pqBinomial p q n 0 = 1 := by
  cases n <;> rfl

/-- **$(p,q)$-binomial coefficients with upper index zero and positive lower index.** For all
elements $p, q$ of a commutative semiring and every natural number $k$, the $(p,q)$-binomial
coefficient $\binom{0}{k+1}_{p,q}$ equals $0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3. -/
public theorem pqBinomial_zero_succ {R : Type*} [CommSemiring R] (p q : R) (k : ℕ) :
    pqBinomial p q 0 (k + 1) = 0 := rfl

/-- **Pascal recursion for $(p,q)$-binomial coefficients.** For all elements $p, q$ of a
commutative semiring and all natural numbers $n$ and $k$, the $(p,q)$-binomial coefficients satisfy
$\binom{n+1}{k+1}_{p,q} = p^{n-k} \binom{n}{k}_{p,q} + q^{k+1} \binom{n}{k+1}_{p,q}$, where $n - k$
is truncated subtraction ($0$ when $k > n$).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3, Equation (3). -/
public theorem pqBinomial_succ_succ {R : Type*} [CommSemiring R] (p q : R) (n k : ℕ) :
    pqBinomial p q (n + 1) (k + 1)
      = p ^ (n - k) * pqBinomial p q n k + q ^ (k + 1) * pqBinomial p q n (k + 1) := rfl

/-- **The $(p, q)$-binomial coefficients at $p = 1$.** Let $R$ be a commutative semiring and
$q \in R$. For all natural numbers $n$ and $k$, the $(p, q)$-binomial coefficient
$[n, k]_{p,q}$ at $p = 1$ equals the Gaussian binomial coefficient $\binom{n}{k}_q$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3 (Remark 1: `p = 1` gives the `q`-analogue). -/
public theorem pqBinomial_one_left {R : Type*} [CommSemiring R] (q : R) (n k : ℕ) :
    pqBinomial 1 q n k = MathlibExt.gaussBinom q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [pqBinomial_zero_right, pqBinomial_zero_succ]
  | succ n ih =>
    cases k with
    | zero => simp [pqBinomial_zero_right]
    | succ k => rw [pqBinomial_succ_succ, MathlibExt.gaussBinom_succ_succ, ih, ih]; simp

/-- **$(p,q)$-analogue of the $r$-Fibonacci polynomial.** Let $R$ be a commutative semiring, let
$r$ and $m$ be natural numbers and let $x, y, p, q \in R$. The $(p,q)$-analogue
$U^{(r)}_n(x, y, p, q, m) \in R$ of the $r$-Fibonacci polynomial is defined by
$U^{(r)}_0(x, y, p, q, m) = 0$ and, for every natural number $n$,
$$
U^{(r)}_{n+1}(x, y, p, q, m) = \sum_{k=0}^{\lfloor n/(r+1) \rfloor} p^{\binom{n+1-(r+1)k}{2}}
q^{\binom{k+1}{2} + m \binom{k}{2}} \binom{n-rk}{k}_{p,q} x^{n-(r+1)k} y^k,
$$
where $\binom{a}{b}_{p,q}$ is the $(p,q)$-binomial coefficient.

The source also states $U^{(r)}_j = p^{\binom{j+1}{2}} x^{j-1}$ for $1 \le j \le r$, which
contradicts this sum: the sum gives $p^{\binom{j}{2}} x^{j-1}$ (for example $U^{(2)}_2 = p x$,
not $p^3 x$). The sum, which Theorem 2 of the source requires, is used.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 1. -/
public def pqRFibonacci {R : Type*} [CommSemiring R] (r : ℕ) (x y p q : R) (m : ℕ) : ℕ → R
  | 0 => 0
  | n + 1 => ∑ k ∈ Finset.range (n / (r + 1) + 1),
      p ^ (n + 1 - (r + 1) * k).choose 2 * q ^ ((k + 1).choose 2 + m * k.choose 2) *
        pqBinomial p q (n - r * k) k * x ^ (n - (r + 1) * k) * y ^ k

/-- **Zeroth value of the $(p,q)$-analogue of the $r$-Fibonacci polynomial.** For all natural
numbers $r$ and $m$ and all elements $x, y, p, q$ of a commutative semiring, the
$(p,q)$-analogue of the $r$-Fibonacci polynomial satisfies $U^{(r)}_0(x, y, p, q, m) = 0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 1. -/
public theorem pqRFibonacci_zero {R : Type*} [CommSemiring R] (r : ℕ) (x y p q : R)
    (m : ℕ) : pqRFibonacci r x y p q m 0 = 0 := rfl

/-- **First value of the $(p,q)$-analogue of the $r$-Fibonacci polynomial.** For all natural
numbers $r$ and $m$ and all elements $x, y, p, q$ of a commutative semiring, the
$(p,q)$-analogue of the $r$-Fibonacci polynomial satisfies $U^{(r)}_1(x, y, p, q, m) = 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 1. -/
public theorem pqRFibonacci_one {R : Type*} [CommSemiring R] (r : ℕ) (x y p q : R)
    (m : ℕ) : pqRFibonacci r x y p q m 1 = 1 := by
  simp [pqRFibonacci, pqBinomial_zero_right]

/-- **First recurrence for the $(p,q)$-analogue of the $r$-Fibonacci polynomial.** Let $R$ be a
commutative semiring, let $r \ge 1$, $n \ge r$ and $m$ be natural numbers and let
$x, y, p, q \in R$. Write $U_j(x, y)$ for $U^{(r)}_j(x, y, p, q, m)$, the $(p,q)$-analogue of the
$r$-Fibonacci polynomial with $r$, $p$, $q$ and $m$ fixed. Then
$$U_{n+1}(x, y) = p x \, U_n(p x, q y) + q y \, U_{n-r}(p x, q^{m+1} y).$$

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 2, Equation (4) (`integers-2025-A38-thm-2`). -/
public theorem_wanted pqRFibonacci_succ_eq_left {R : Type*} [CommSemiring R] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (x y p q : R) (m : ℕ) :
    pqRFibonacci r x y p q m (n + 1)
      = p * x * pqRFibonacci r (p * x) (q * y) p q m n
        + q * y * pqRFibonacci r (p * x) (q ^ (m + 1) * y) p q m (n - r)

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

/-- **Sum of the first $n$ $r$-Lucas polynomials.** Let $K$ be a field, let $r \ge 1$ and $s$ be
natural numbers, let $x, y \in K$ with $1 - x - y \ne 0$, and write $V_j$ for the $r$-Lucas
polynomial of type $s$, $V_j = V^{(r,s)}_j(x, y)$. Then for every natural number $n$ with
$n \ge 1$ and $n \ge r - 1$,
$$
\sum_{j=1}^{n} V_j = \frac{1 + s y - V_{n+1} - y \sum_{j=1}^{r} V_{n-r+j}}{1 - x - y} - 1.
$$

The paper states $n \ge 1$; for $n < r - 1$ the right side involves $V$ at negative indices.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Corollary 4 (`integers-2025-A38-cor-4`). -/
public theorem_wanted sum_rLucasPolynomial {K : Type*} [Field K] {r n : ℕ} (hr : 1 ≤ r)
    (hn1 : 1 ≤ n) (hn : r ≤ n + 1) (s : ℕ) (x y : K) (hP : 1 - x - y ≠ 0) :
    ∑ j ∈ Finset.Icc 1 n, rLucasPolynomial r s x y j
      = (1 + s * y - rLucasPolynomial r s x y (n + 1)
          - y * ∑ j ∈ Finset.Icc 1 r, rLucasPolynomial r s x y (n + j - r))
        / (1 - x - y) - 1

/-- **Alternating sum of $r$-Lucas polynomials.** Let $K$ be a field, let $r \ge 1$ and $s$ be
natural numbers, let $x, y \in K$ with $1 + x + (-1)^r y \ne 0$, and write $V_j$ for the
$r$-Lucas polynomial of type $s$, $V_j = V^{(r,s)}_j(x, y)$. Then for every natural number
$n \ge r - 1$,
$$
\sum_{j=1}^{n} (-1)^j V_j =
\frac{1 - (-1)^r s y + (-1)^n V_{n+1} + (-1)^r y \sum_{j=1}^{r} (-1)^{n-r+j} V_{n-r+j}}
{1 + x + (-1)^r y} - 1.
$$

For $n < r - 1$ the right side involves $V$ at negative indices.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Corollary 5 (`integers-2025-A38-cor-5`). -/
public theorem_wanted sum_neg_one_pow_mul_rLucasPolynomial {K : Type*} [Field K] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n + 1) (s : ℕ) (x y : K) (hP : 1 + x + (-1) ^ r * y ≠ 0) :
    ∑ j ∈ Finset.Icc 1 n, (-1) ^ j * rLucasPolynomial r s x y j
      = (1 - (-1) ^ r * s * y + (-1) ^ n * rLucasPolynomial r s x y (n + 1)
          + (-1) ^ r * y * ∑ j ∈ Finset.Icc 1 r,
              (-1) ^ (n + j - r) * rLucasPolynomial r s x y (n + j - r))
        / (1 + x + (-1) ^ r * y) - 1

/-- **The (-r)-Fibonacci polynomials.** Let $A$ be a commutative ring, $r$ a natural number,
$x \in A$ and $y$ a unit of $A$. The values $U_n = U^{(-r)}_n(x, y) \in A$ of the
$(-r)$-Fibonacci polynomials are defined for $n \ge 0$ by $U_0 = 0$, $U_1 = 1$, $U_n = 0$ for
$2 \le n \le r$, and, when $r \ge 1$, $U_{n+1} = y^{-1} U_{n-r+1} - y^{-1} x U_{n-r}$ for
$n \ge r$. When $r = 0$, $U_n = 0$ for every $n \ge 2$.

The paper takes $r \ge 2$; the case $r = 0$ only makes the definition total.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public def negRFibonacci {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) : ℕ → A
  | 0 => 0
  | n + 1 =>
    if n = 0 then 1
    else if n < r ∨ r = 0 then 0
    else (↑y⁻¹ : A) * negRFibonacci r x y (n - r + 1) - ↑y⁻¹ * x * negRFibonacci r x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- **The zeroth (-r)-Fibonacci polynomial.** For every commutative ring $A$, natural number
$r$, $x \in A$ and unit $y$ of $A$, the $(-r)$-Fibonacci polynomial satisfies
$U^{(-r)}_0(x, y) = 0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public theorem negRFibonacci_zero {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) :
    negRFibonacci r x y 0 = 0 := by
  rw [negRFibonacci]

/-- **The first (-r)-Fibonacci polynomial.** For every commutative ring $A$, natural number
$r$, $x \in A$ and unit $y$ of $A$, the $(-r)$-Fibonacci polynomial satisfies
$U^{(-r)}_1(x, y) = 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public theorem negRFibonacci_one {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) :
    negRFibonacci r x y 1 = 1 := by
  rw [negRFibonacci]
  simp

/-- **The (-r)-Fibonacci polynomials vanish at indices 2 to r.** Let $A$ be a commutative ring,
$x \in A$ and $y$ a unit of $A$. For natural numbers $r$ and $n$ with $1 \le n < r$, the
$(-r)$-Fibonacci polynomial satisfies $U^{(-r)}_{n+1}(x, y) = 0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public theorem negRFibonacci_succ_of_lt {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (h1 : 1 ≤ n) (h : n < r) : negRFibonacci r x y (n + 1) = 0 := by
  rw [negRFibonacci]
  simp [show n ≠ 0 by omega, h]

/-- **Recurrence for the (-r)-Fibonacci polynomials.** Let $A$ be a commutative ring, $x \in A$
and $y$ a unit of $A$, let $r$ and $n$ be natural numbers with $1 \le r \le n$, and write
$U_m = U^{(-r)}_m(x, y)$. Then $U_{n+1} = y^{-1} U_{n-r+1} - y^{-1} x U_{n-r}$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3, Equation (7). -/
public theorem negRFibonacci_succ_of_le {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (hr : 1 ≤ r) (h : r ≤ n) :
    negRFibonacci r x y (n + 1)
      = ↑y⁻¹ * negRFibonacci r x y (n - r + 1) - ↑y⁻¹ * x * negRFibonacci r x y (n - r) := by
  rw [negRFibonacci]
  simp [show n ≠ 0 by omega, show ¬n < r by omega, show r ≠ 0 by omega]

/-- **Companion sequence of the $(-r)$-Fibonacci polynomials.** Let $A$ be a commutative ring,
$r$ a natural number, $x \in A$ and $y$ a unit of $A$. The companion sequence
$V^{(-r)}_n(x, y) \in A$, $n \ge 0$, is defined by $V^{(-r)}_0 = r + 1$ and, if $r \ge 1$, by
$V^{(-r)}_n = 0$ for $1 \le n < r$, $V^{(-r)}_r = r y^{-1}$ and
$V^{(-r)}_{n+1} = y^{-1} V^{(-r)}_{n-r+1} - y^{-1} x V^{(-r)}_{n-r}$ for $n \ge r$. If $r = 0$,
then $V^{(-r)}_n = 0$ for all $n \ge 1$.

The paper takes $r \ge 2$; the case $r = 0$ only makes the definition total.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public def negRLucas {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) : ℕ → A
  | 0 => (r : A) + 1
  | n + 1 =>
    if r = 0 ∨ n + 1 < r then 0
    else if n + 1 = r then (r : A) * ↑y⁻¹
    else (↑y⁻¹ : A) * negRLucas r x y (n - r + 1) - ↑y⁻¹ * x * negRLucas r x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- **Zeroth term of the companion sequence $V^{(-r)}$.** Let $A$ be a commutative ring, $r$ a
natural number, $x \in A$ and $y$ a unit of $A$. The companion sequence of the
$(-r)$-Fibonacci polynomials satisfies $V^{(-r)}_0(x, y) = r + 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_zero {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) :
    negRLucas r x y 0 = (r : A) + 1 := by
  rw [negRLucas]

/-- **Vanishing initial terms of the companion sequence $V^{(-r)}$.** Let $A$ be a commutative
ring, $x \in A$ and $y$ a unit of $A$. For natural numbers $r$ and $n$ with $n + 1 < r$, the
companion sequence of the $(-r)$-Fibonacci polynomials satisfies $V^{(-r)}_{n+1}(x, y) = 0$;
that is, $V^{(-r)}_m(x, y) = 0$ for $1 \le m < r$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_succ_of_lt {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (h : n + 1 < r) : negRLucas r x y (n + 1) = 0 := by
  rw [negRLucas]
  simp [h]

/-- **The $r$-th term of the companion sequence $V^{(-r)}$.** Let $A$ be a commutative ring,
$r \ge 1$ a natural number, $x \in A$ and $y$ a unit of $A$. The companion sequence of the
$(-r)$-Fibonacci polynomials satisfies $V^{(-r)}_r(x, y) = r y^{-1}$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_self {A : Type*} [CommRing A] {r : ℕ} (x : A) (y : Aˣ)
    (hr : 1 ≤ r) : negRLucas r x y r = (r : A) * ↑y⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [negRLucas]
  simp

/-- **Recurrence for the companion sequence $V^{(-r)}$.** Let $A$ be a commutative ring, $x \in A$
and $y$ a unit of $A$. For natural numbers $r$ and $n$ with $1 \le r \le n$, the companion
sequence of the $(-r)$-Fibonacci polynomials satisfies
$V^{(-r)}_{n+1}(x, y) = y^{-1} V^{(-r)}_{n-r+1}(x, y) - y^{-1} x V^{(-r)}_{n-r}(x, y)$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_succ_of_le {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (hr : 1 ≤ r) (h : r ≤ n) :
    negRLucas r x y (n + 1)
      = ↑y⁻¹ * negRLucas r x y (n - r + 1) - ↑y⁻¹ * x * negRLucas r x y (n - r) := by
  rw [negRLucas]
  simp [show r ≠ 0 by omega, show ¬n + 1 < r by omega, show n + 1 ≠ r by omega]

/-- **Explicit sum for the (-r)-Fibonacci polynomials.** Let $A$ be a commutative ring,
$r \ge 2$, $x \in A$ and $y$ a unit of $A$, and write $U_n = U^{(-r)}_n(x, y)$. For every
$n \ge 0$,
$$U_{n+1} = \sum_{k=0}^{\lfloor n/r \rfloor} \binom{k}{n - rk} y^{-k} (-x)^{n-rk},$$
where $\binom{a}{b} = 0$ for $b > a$, so the terms with $(r+1) k < n$ vanish.

The paper states $n \ge 1$ and $x$ a unit; the identity holds for $n = 0$ and every $x$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 6 (`integers-2025-A38-thm-6`). -/
public theorem_wanted negRFibonacci_succ_eq_sum {A : Type*} [CommRing A] {r : ℕ}
    (hr : 2 ≤ r) (x : A) (y : Aˣ) (n : ℕ) :
    negRFibonacci r x y (n + 1)
      = ∑ k ∈ Finset.range (n / r + 1),
          ((k.choose (n - r * k) : ℕ) : A) * (↑y⁻¹ : A) ^ k * (-x) ^ (n - r * k)

/-- **Explicit sum for the (-r)-Fibonacci polynomials, second form.** Let $A$ be a commutative
ring, $r \ge 2$, $x \in A$ and $y$ a unit of $A$, and write $U_n = U^{(-r)}_n(x, y)$. For every
$n \ge 0$, $U_{n+1}$ is the sum of $\binom{(n-k)/r}{k} y^{-(n-k)/r} (-x)^k$ over the integers
$k$ with $0 \le k \le \lfloor n/r \rfloor$ and $r \mid n - k$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 6 (`integers-2025-A38-thm-6`). -/
public theorem_wanted negRFibonacci_succ_eq_sum' {A : Type*} [CommRing A] {r : ℕ}
    (hr : 2 ≤ r) (x : A) (y : Aˣ) (n : ℕ) :
    negRFibonacci r x y (n + 1)
      = ∑ k ∈ (Finset.range (n / r + 1)).filter (fun k => r ∣ n - k),
          ((((n - k) / r).choose k : ℕ) : A) * (↑y⁻¹ : A) ^ ((n - k) / r) * (-x) ^ k

/-- **The companion sequence in terms of the $(-r)$-Fibonacci polynomials.** Let $A$ be a
commutative ring, $r \ge 2$ a natural number, $x \in A$ and $y$ a unit of $A$, and let
$U^{(-r)}_n(x, y)$ be the $(-r)$-Fibonacci polynomials and $V^{(-r)}_n(x, y)$ their companion
sequence. For every natural number $n \ge r$,
$V^{(-r)}_n(x, y) = r \, U^{(-r)}_{n+1}(x, y) - x y^{-1} U^{(-r)}_{n-r}(x, y)$.

The paper takes $x$ a unit; the identity holds for every $x$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Proposition 1, Equation (8) (`integers-2025-A38-prop-1`). -/
public theorem_wanted negRLucas_eq {A : Type*} [CommRing A] {r n : ℕ} (hr : 2 ≤ r)
    (hn : r ≤ n) (x : A) (y : Aˣ) :
    negRLucas r x y n = r * negRFibonacci r x y (n + 1) - x * ↑y⁻¹ * negRFibonacci r x y (n - r)

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

/-- **Generating function of the (-r)-Fibonacci polynomials.** Let $A$ be a commutative ring,
$r \ge 2$, $x \in A$ and $y$ a unit of $A$, and write $U_n = U^{(-r)}_n(x, y)$. In the ring
$A[[z]]$ of formal power series,
$$\left(1 - y^{-1} z^r + x y^{-1} z^{r+1}\right) \sum_{n \ge 0} U_{n+1} z^n = 1.$$

The paper states the identity for complex $z$; convergence is not part of this statement.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 8 (`integers-2025-A38-thm-8`). -/
public theorem_wanted negRFibonacci_generatingFunction {A : Type*} [CommRing A] {r : ℕ}
    (hr : 2 ≤ r) (x : A) (y : Aˣ) :
    (1 - PowerSeries.C (↑y⁻¹ : A) * PowerSeries.X ^ r
        + PowerSeries.C (x * ↑y⁻¹) * PowerSeries.X ^ (r + 1)) *
      PowerSeries.mk (fun n => negRFibonacci r x y (n + 1)) = 1

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

/-- **Separability of $t^{r+1} - y^{-1} t + x y^{-1}$.** Let $K$ be a field of characteristic zero,
let $r \ge 1$, let $x \in K$ and let $y \in K$ be nonzero with $(r+1)^{r+1} x^r y \ne r^r$. Then
the polynomial $t^{r+1} - y^{-1} t + x y^{-1} \in K[t]$ is separable, that is, coprime to its
derivative; equivalently, it has no multiple zeros in an algebraic closure of $K$.

This corrects Lemma 1 of the paper. The printed hypothesis $x \ne \frac{r}{r+1} ((r+1) y)^{-1/r}$
names only one $r$-th root and is insufficient: $r = 2$, $y = 1/3$, $x = -2/3$ satisfies it, since
$\frac{2}{3} \cdot 1^{-1/2} = \frac{2}{3}$, yet $t^3 - 3t - 2 = (t + 1)^2 (t - 2)$. The paper's
proof shows that a multiple zero $\beta$ forces $x = r\beta/(r+1)$ with $\beta^r = 1/((r+1) y)$,
that is, $(r+1)^{r+1} x^r y = r^r$, which is the branch-free condition used here.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Lemma 1 (`integers-2025-A38-lem-1`). -/
public theorem_wanted separable_negRFibonacci_charPoly {K : Type*} [Field K] [CharZero K]
    {r : ℕ} (hr : 1 ≤ r) (x : K) (y : Kˣ)
    (h : ((r : K) + 1) ^ (r + 1) * x ^ r * y ≠ (r : K) ^ r) :
    (Polynomial.X ^ (r + 1) - Polynomial.C (↑y⁻¹ : K) * Polynomial.X
      + Polynomial.C (x * ↑y⁻¹) : Polynomial K).Separable

/-- **Binet formula for the (-r)-Fibonacci polynomials.** Let $K$ be a field, $r \ge 2$,
$x \in K$ and $y \in K$ nonzero, and write $U_n = U^{(-r)}_n(x, y)$. Suppose that
$\beta_0, \dots, \beta_r \in K$ are pairwise distinct and that
$t^{r+1} - y^{-1} t + x y^{-1} = \prod_{k=0}^{r} (t - \beta_k)$ as polynomials over $K$. Then for
every $n \ge 0$,
$$U_{n+1} = \sum_{k=0}^{r} \frac{\beta_k^{n+r+1}}{r \beta_k^{r+1} - x y^{-1}},$$
where a term whose denominator vanishes is read as $0$.

The paper's hypothesis $x \ne \frac{r}{r+1} ((r+1) y)^{-1/r}$ is replaced by the distinctness of
the zeros (compare Lemma 1).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 9 (`integers-2025-A38-thm-9`). -/
public theorem_wanted negRFibonacci_eq_sum_roots {K : Type*} [Field K] {r : ℕ} (hr : 2 ≤ r)
    (x : K) (y : Kˣ) (β : Fin (r + 1) → K) (hβ : Function.Injective β)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C (↑y⁻¹ : K) * Polynomial.X
      + Polynomial.C (x * ↑y⁻¹) : Polynomial K) = ∏ k, (Polynomial.X - Polynomial.C (β k)))
    (n : ℕ) :
    negRFibonacci r x y (n + 1) = ∑ k, β k ^ (n + r + 1) / (r * β k ^ (r + 1) - x * ↑y⁻¹)

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
