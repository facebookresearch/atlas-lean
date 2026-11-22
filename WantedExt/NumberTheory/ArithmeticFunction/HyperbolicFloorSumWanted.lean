/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Antidiag.Nat
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! # Hyperbolic sums of arithmetic functions at the integer part

Statement-only requests from Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation
Involving Certain Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026),
Article A37. Following the source (arXiv:2412.16675v2, Section 1),
`S_{f,r}(x) = ∑_{n₁⋯n_r ≤ x} f(⌊x/(n₁⋯n_r)⌋) = ∑_{n ≤ x} f(⌊x/n⌋) τ_r(n)`, where
`τ_r(n) = (Nat.finMulAntidiag r n).card` counts the ordered factorizations of `n` into `r`
positive factors. The polynomial `P_r` with coefficients `a_j` is the one in
`∑_{n ≤ x} τ_r(n) = x P_r(log x) + O(x^{1-1/r} (log x)^{r-2})`; it is taken as a hypothesis
`P` satisfying that estimate, which determines it uniquely. The constants are
`C_i = ∑_{n ≥ 1} f(n) ((log n)^i/n - (log (n+1))^i/(n+1))`, written with the index
shifted to `n + 1`.
-/

open Asymptotics Filter

namespace MetaMathlibExt

@[expose] public section

/-- **Absolute convergence of a log-weighted difference series.** Let $f$ be a real function on
the natural numbers with $f(n) = O(n^\alpha)$ as $n \to \infty$ for some real $\alpha$ with
$0 \le \alpha < 1$. Then for every natural number $i$ the series
$$\sum_{n \ge 1} f(n) \left( \frac{(\log n)^i}{n} - \frac{(\log (n+1))^i}{n+1} \right)$$
converges absolutely.

Source: Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation Involving Certain
Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026), Article A37,
Lemma 1 (`integers-2026-A37-lem-1`). -/
public theorem_wanted summable_abs_mul_log_pow_div_sub
    (f : ℕ → ℝ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hf : (fun n : ℕ => f n) =O[atTop] fun n : ℕ => (n : ℝ) ^ α) (i : ℕ) :
    Summable fun n : ℕ =>
      |f (n + 1) * (Real.log (n + 1) ^ i / (n + 1) - Real.log (n + 2) ^ i / (n + 2))|

/-- **Asymptotics of hyperbolic floor sums.** Let $r \ge 2$ and let $\tau_r(n)$ be the number of
ordered factorizations $n = n_1 \cdots n_r$ of $n$ into $r$ positive factors. Let
$P(t) = \sum_j a_j t^j$ be a real polynomial with
$\sum_{1 \le n \le x} \tau_r(n) - x P(\log x) = O(x^{1 - 1/r} (\log x)^{r-2})$ as $x \to \infty$.
Let $f$ be a nonnegative real function on the natural numbers such that, for some real $\alpha$
with $0 \le \alpha < 1$, $f(n) = O(n^\alpha)$ as $n \to \infty$, and, for some real $\beta \ge 0$,
$\sum_{1 \le n \le x} f(n) = O(x (\log \log x)^\beta)$ as $x \to \infty$. For $i \ge 0$ let
$$C_i = \sum_{n \ge 1} f(n) \left( \frac{(\log n)^i}{n} - \frac{(\log (n+1))^i}{n+1} \right).$$
Then, as $x \to \infty$,
$$\sum_{1 \le n \le x} f(\lfloor x/n \rfloor) \, \tau_r(n) = x \sum_{j=0}^{r-1} \sum_{i=0}^{j}
\binom{j}{i} (-1)^i a_j C_i (\log x)^{j-i} + O(x (\log x)^{r-2} (\log \log x)^\beta).$$

The hypothesis $f \ge 0$ is not in the source: its proof bounds the error sum
$\sum_{d \le x} f(d) \, O((x/d)^{1-1/r} (\log (x/d))^{r-2})$ through $\sum_{n \le x} f(n)$,
which controls it only for nonnegative $f$.

Source: Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation Involving Certain
Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026), Article A37,
Theorem 1 (`integers-2026-A37-thm-1`). -/
public theorem_wanted hyperbolic_floor_sum_asymptotic
    (r : ℕ) (hr : 2 ≤ r) (P : Polynomial ℝ)
    (hP : (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.finMulAntidiag r n).card : ℝ)) -
          x * P.eval (Real.log x)) =O[atTop]
        fun x : ℝ => x ^ (1 - 1 / (r : ℝ)) * Real.log x ^ (r - 2))
    (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hf : (fun n : ℕ => f n) =O[atTop] fun n : ℕ => (n : ℝ) ^ α)
    (β : ℝ) (hβ : 0 ≤ β)
    (hsum : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) =O[atTop]
        fun x : ℝ => x * Real.log (Real.log x) ^ β) :
    (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f ⌊x / n⌋₊ * ((Nat.finMulAntidiag r n).card : ℝ)) -
          x * ∑ j ∈ Finset.range r, ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * (-1) ^ i * P.coeff j *
              (∑' n : ℕ, f (n + 1) *
                (Real.log (n + 1) ^ i / (n + 1) - Real.log (n + 2) ^ i / (n + 2))) *
              Real.log x ^ (j - i)) =O[atTop]
      fun x : ℝ => x * Real.log x ^ (r - 2) * Real.log (Real.log x) ^ β

/-- **Hyperbolic floor sums of additive functions of prime exponents.** Let $r \ge 2$ and let
$\tau_r(n)$ be the number of ordered factorizations $n = n_1 \cdots n_r$ of $n$ into $r$ positive
factors. Let $P(t) = \sum_j a_j t^j$ be a real polynomial with
$\sum_{1 \le n \le x} \tau_r(n) - x P(\log x) = O(x^{1 - 1/r} (\log x)^{r-2})$ as $x \to \infty$.
Let $g$ be a real function on the natural numbers with $g(1) \ne 0$ and $g(a) = O(2^{a/2})$ as
$a \to \infty$. For $n \ge 1$ let $f(n) = \sum_{p \mid n} g(v_p(n))$, the sum over the primes $p$
dividing $n$, where $v_p(n)$ is the exponent of $p$ in $n$, and for $i \ge 0$ let
$$C_i = \sum_{n \ge 1} f(n) \left( \frac{(\log n)^i}{n} - \frac{(\log (n+1))^i}{n+1} \right).$$
Then, as $x \to \infty$,
$$\sum_{1 \le n \le x} f(\lfloor x/n \rfloor) \, \tau_r(n) = x \sum_{j=0}^{r-1} \sum_{i=0}^{j}
\binom{j}{i} (-1)^i a_j C_i (\log x)^{j-i} + O(x (\log x)^{r-2} \log \log x).$$

Since $f(n)$ sums only over the primes dividing $n$, the source's convention $g(0) = 0$ is not
needed.

Source: Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation Involving Certain
Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026), Article A37,
Proposition 1 (`integers-2026-A37-prop-1`). -/
public theorem_wanted hyperbolic_floor_sum_asymptotic_additive
    (r : ℕ) (hr : 2 ≤ r) (P : Polynomial ℝ)
    (hP : (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.finMulAntidiag r n).card : ℝ)) -
          x * P.eval (Real.log x)) =O[atTop]
        fun x : ℝ => x ^ (1 - 1 / (r : ℝ)) * Real.log x ^ (r - 2))
    (g : ℕ → ℝ) (hg1 : g 1 ≠ 0)
    (hg : (fun n : ℕ => g n) =O[atTop] fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 2)) :
    (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            (∑ p ∈ (⌊x / n⌋₊).primeFactors, g ((⌊x / n⌋₊).factorization p)) *
              ((Nat.finMulAntidiag r n).card : ℝ)) -
          x * ∑ j ∈ Finset.range r, ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * (-1) ^ i * P.coeff j *
              (∑' n : ℕ, (∑ p ∈ (n + 1).primeFactors, g ((n + 1).factorization p)) *
                (Real.log (n + 1) ^ i / (n + 1) - Real.log (n + 2) ^ i / (n + 2))) *
              Real.log x ^ (j - i)) =O[atTop]
      fun x : ℝ => x * Real.log x ^ (r - 2) * Real.log (Real.log x)

end

end MetaMathlibExt
