/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Primorial
public import WantedExt.NumberTheory.PrimeCounting.DusartMertensReciprocalSumWanted

namespace MetaMathlibExt

@[expose] public section

open Filter Topology Real

/-- **The real extension of the harmonic numbers.** For a real number $x$, let

$$H(x) = \int_0^1 \frac{t^x - 1}{t - 1}\,dt,$$

where $t^x$ is the real power and the integral is the Lebesgue integral over $[0, 1]$, taken to be
$0$ when the integrand is not integrable.

This extends the harmonic numbers: $H(n) = 1 + \frac{1}{2} + \cdots + \frac{1}{n}$ for every
natural number $n$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Section 3.1 (definition of `H(x)`). -/
noncomputable def harmonicExtension (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (t ^ x - 1) / (t - 1)

/-- **The real extension of the harmonic numbers vanishes at zero.** The real extension
$H(x) = \int_0^1 \frac{t^x - 1}{t - 1}\,dt$ of the harmonic numbers satisfies $H(0) = 0$.

Source: Assani, Chester, and Paschal, INTEGERS 26 (2026), Article A86, Section 3.1 (definition of
`H(x)`). -/
theorem harmonicExtension_zero : harmonicExtension 0 = 0 := by
  simp [harmonicExtension]

/-- **The real extension agrees with the harmonic numbers.** Let
$H(x) = \int_0^1 \frac{t^x - 1}{t - 1}\,dt$ for real $x$ be the real extension of the harmonic
numbers. For every natural number $n$, $H(n) = H_n$, where $H_n = \sum_{i=1}^n 1/i$ is the
$n$-th harmonic number.

Source: Assani, Chester, and Paschal, INTEGERS 26 (2026), Article A86, Section 3.1 ("`H(n) = H_n`
for all `n ∈ ℕ`"). -/
public theorem_wanted harmonicExtension_natCast (n : ℕ) :
    harmonicExtension n = harmonic n

/-- **Rosser–Schoenfeld and Dusart bounds for the $k$-th prime.** Let $p_k$ be the $k$-th prime
($p_1 = 2$) and $\log$ the natural logarithm. For every natural number $k \ge 6$,

$$k(\log k + \log \log k - 1) < p_k < k(\log k + \log \log k).$$

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 1, equation (3)
(`integers-2026-A86-thm-1`). -/
public theorem_wanted nth_prime_bounds (k : ℕ) (hk : 6 ≤ k) :
    (k : ℝ) * (log k + log (log k) - 1) < Nat.nth Nat.Prime (k - 1) ∧
      (Nat.nth Nat.Prime (k - 1) : ℝ) < k * (log k + log (log k))

/-- **Lower bound for the double logarithm of a primorial divided by one of its primes.** Let
$p_\ell$ be the $\ell$-th prime ($p_1 = 2$) and $\log$ the natural logarithm. For natural numbers
$k \ge 99$ and $j$ with $1 \le j \le k + 1$, let $m = p_1 p_2 \cdots p_{k+1} / p_j$. Then

$$\log \log m > \log\bigl((k+1)(\log(k+1) + \log \log(k+1) - 1) \log 2.51 - \log p_j\bigr).$$

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 4 (`integers-2026-A86-lem-4`).
-/
public theorem_wanted log_log_primorial_div_prime_gt (k j : ℕ) (hk : 99 ≤ k) (hj : 1 ≤ j)
    (hjk : j ≤ k + 1) :
    log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1) * log (251 / 100) -
        log (Nat.nth Nat.Prime (j - 1))) <
      log (log ((primorial (Nat.nth Nat.Prime k) : ℝ) / Nat.nth Nat.Prime (j - 1)))

/-- **Robin's inequality for $n > 5040$ when one of $2, 3, 5$ does not divide $n$.** Let
$\sigma(n)$ denote the sum of the divisors of $n$ and $\gamma$ the Euler–Mascheroni constant.
Let $p \in \{2, 3, 5\}$ and let $n > 5040$ be a natural number not divisible by $p$. Then Robin's
inequality $\sigma(n) < e^{\gamma} n \log \log n$ holds.

The paper prints Robin's inequality as $\sigma(n) < e^{\gamma} \log \log n$, dropping the factor
$n$; the standard form, which the paper uses in Section 2, is formalized.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 4 (`integers-2026-A86-thm-4`).
-/
public theorem_wanted robin_inequality_of_not_dvd (p : ℕ) (hp : p ∈ ({2, 3, 5} : Finset ℕ))
    (n : ℕ) (hn : 5040 < n) (hdvd : ¬ p ∣ n) :
    (ArithmeticFunction.sigma 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n)

/-- **Robin's inequality for $2^k n$ with $n$ odd and large.** Let $\sigma(N)$ denote the sum of
the divisors of $N$ and $\gamma$ the Euler–Mascheroni constant. Let $k \ge 1$ and let $n$ be an
odd natural number with $n > b(k) = e^{e^{\sqrt{2.51(2^{k+1} - 1)/e^{\gamma}}}} / 2^k$. Then
Robin's inequality $\sigma(2^k n) < e^{\gamma} 2^k n \log \log (2^k n)$ holds.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 5, equation (12)
(`integers-2026-A86-thm-5`). -/
public theorem_wanted robin_inequality_two_pow_mul_odd (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : Odd n)
    (hb : exp (exp (√((251 / 100 : ℝ) * (2 ^ (k + 1) - 1) / exp eulerMascheroniConstant))) /
      2 ^ k < n) :
    (ArithmeticFunction.sigma 1 (2 ^ k * n) : ℝ) <
      exp eulerMascheroniConstant * (2 ^ k * n : ℕ) * log (log (2 ^ k * n : ℕ))

/-- **Robin's inequality for $2n$ with $n \ge 620$ odd and for primorials above $30$.** Let
$\sigma(N)$ denote the sum of the divisors of $N$ and $\gamma$ the Euler–Mascheroni constant. For
every odd natural number $n \ge 620$, Robin's inequality
$\sigma(2n) < e^{\gamma} \cdot 2n \log \log (2n)$ holds. For every natural number $m$ whose
primorial $m\# = \prod_{p \le m,\ p \text{ prime}} p$ exceeds $30$, Robin's inequality
$\sigma(m\#) < e^{\gamma} \, m\# \log \log (m\#)$ holds.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Corollary 2
(`integers-2026-A86-cor-2`). -/
public theorem_wanted robin_inequality_two_mul_odd_and_primorial :
    (∀ n : ℕ, Odd n → 620 ≤ n →
      (ArithmeticFunction.sigma 1 (2 * n) : ℝ) <
        exp eulerMascheroniConstant * (2 * n : ℕ) * log (log (2 * n : ℕ))) ∧
    ∀ m : ℕ, 30 < primorial m →
      (ArithmeticFunction.sigma 1 (primorial m) : ℝ) <
        exp eulerMascheroniConstant * primorial m * log (log (primorial m))

/-- **Robin's inequality for $2^k n > 5040$ with $n$ odd under a bound on $k$, and for $21$-free
$n > 5040$.** Let $\sigma(N)$ denote the sum of the divisors of $N$ and $\gamma$ the
Euler–Mascheroni constant, and let $C = 10^{10^{13.11485}}$. First, let $k \ge 1$ be such that
$2^k \tilde b(k) = e^{e^{(0.0168(2^{k+1} - 1)/e^{\gamma})^{1/3}}} < C$. Then for every odd natural
number $n$ with $2^k n > 5040$, Robin's inequality
$\sigma(2^k n) < e^{\gamma} 2^k n \log \log (2^k n)$ holds. Second, for every natural number
$n > 5040$ that is $21$-free (no prime $p$ satisfies $p^{21} \mid n$), Robin's inequality
$\sigma(n) < e^{\gamma} n \log \log n$ holds.

The paper omits $> 5040$; as printed the claims fail at $2 \cdot 3 = 6$ and at the $21$-free
$n = 12$, and its proof treats exactly the range $2^k n > 5041$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 7 (`integers-2026-A86-thm-7`).
-/
public theorem_wanted robin_inequality_two_pow_mul_odd_and_twentyOne_free :
    (∀ k : ℕ, 1 ≤ k →
      exp (exp (((168 / 10000 : ℝ) * (2 ^ (k + 1) - 1) / exp eulerMascheroniConstant) ^
        (1 / 3 : ℝ))) < (10 : ℝ) ^ ((10 : ℝ) ^ (1311485 / 100000 : ℝ)) →
      ∀ n : ℕ, Odd n → 5040 < 2 ^ k * n →
        (ArithmeticFunction.sigma 1 (2 ^ k * n) : ℝ) <
          exp eulerMascheroniConstant * (2 ^ k * n : ℕ) * log (log (2 ^ k * n : ℕ))) ∧
    ∀ n : ℕ, 5040 < n → (∀ p : ℕ, p.Prime → ¬ p ^ 21 ∣ n) →
      (ArithmeticFunction.sigma 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n)

/-- **Robin's inequality holds on a set of natural density one.** Let $\sigma(n)$ be the sum of
the divisors of $n$, $\gamma$ the Euler–Mascheroni constant and $\log$ the natural logarithm. The
proportion of the integers $n$ with $1 \le n \le N$ that satisfy Robin's inequality
$\sigma(n) < e^{\gamma} n \log \log n$ tends to $1$ as $N \to \infty$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 8 (`integers-2026-A86-thm-8`).
-/
public theorem_wanted robin_inequality_density_one :
    Tendsto (fun N : ℕ => ((Finset.Icc 1 N).filter fun n : ℕ =>
        (ArithmeticFunction.sigma 1 n : ℝ) <
          exp eulerMascheroniConstant * n * log (log n)).card / (N : ℝ)) atTop (𝓝 1)

/-- **Upper bound $H(x) < \log x + \gamma + 1/(2x)$.** With $H$ the real extension of the harmonic
numbers, $\log$ the natural logarithm and $\gamma$ the Euler–Mascheroni constant, every real
$x \ge 1$ satisfies $H(x) < \log x + \gamma + \frac{1}{2x}$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 6 (`integers-2026-A86-lem-6`).
-/
public theorem_wanted harmonicExtension_lt_log_add (x : ℝ) (hx : 1 ≤ x) :
    harmonicExtension x < log x + eulerMascheroniConstant + 1 / (2 * x)

/-- **Logarithmic upper bound for $H(x)$ with a $\pi^2$ correction.** With $H$ the real extension of
the harmonic numbers and $\log$ the natural logarithm, every real $x \ge 4$ satisfies
$$H(x) < \frac{2 \log x}{1 + 6/(\pi^2 x)}.$$

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 7 (`integers-2026-A86-lem-7`).
-/
public theorem_wanted harmonicExtension_lt_two_log (x : ℝ) (hx : 4 ≤ x) :
    harmonicExtension x < 2 * log x / (1 + 6 / (π ^ 2 * x))

/-- **Upper bounds for harmonic numbers and for the logarithm of their real extension.** Let
$H_m = 1 + \frac{1}{2} + \cdots + \frac{1}{m}$ be the $m$-th harmonic number, $H(x)$ the real
extension $\int_0^1 \frac{t^x - 1}{t - 1}\,dt$ of the harmonic numbers, and $\log$ the natural
logarithm. Then $H_{n+1} \le n / \log n$ for every natural number $n > 1$, and
$\log H(x) \le x / (2 \log x)$ for every real number $x \ge 4$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 8 (`integers-2026-A86-lem-8`).
-/
public theorem_wanted harmonic_succ_le_and_log_harmonicExtension_le :
    (∀ n : ℕ, 1 < n → (harmonic (n + 1) : ℝ) ≤ n / log n) ∧
    ∀ x : ℝ, 4 ≤ x → log (harmonicExtension x) ≤ x / (2 * log x)

/-- **Upper bound for $H(x) \log H(x)$.** With $H$ the real extension of the harmonic numbers and
$\log$ the natural logarithm, every real $x \ge 4$ satisfies
$$H(x) \log H(x) < \frac{x^2}{x + 6/\pi^2}.$$

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 9 (`integers-2026-A86-lem-9`).
-/
public theorem_wanted harmonicExtension_mul_log_lt (x : ℝ) (hx : 4 ≤ x) :
    harmonicExtension x * log (harmonicExtension x) < x ^ 2 / (x + 6 / π ^ 2)

/-- **Lower bound for the derivative $H'(x)$.** With $H$ the real extension of the harmonic numbers
and $\log$ the natural logarithm, every real $x \ge 4$ satisfies
$$H'(x) > \frac{H(x) \log H(x)}{x^2}.$$

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 10 (`integers-2026-A86-lem-10`).
-/
public theorem_wanted harmonicExtension_mul_log_div_sq_lt_deriv (x : ℝ) (hx : 4 ≤ x) :
    harmonicExtension x * log (harmonicExtension x) / x ^ 2 < deriv harmonicExtension x

/-- **Monotonicity of $e^{H(x)} \log H(x) / x$.** With $H$ the real extension of the harmonic
numbers and $\log$ the natural logarithm, the function $g(x) = e^{H(x)} \log H(x) / x$ is
non-decreasing on $[4, \infty)$: $g(x) \le g(y)$ whenever $4 \le x \le y$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Proposition 2
(`integers-2026-A86-prop-2`). -/
public theorem_wanted exp_harmonicExtension_mul_log_div_monotoneOn :
    MonotoneOn (fun x : ℝ => exp (harmonicExtension x) * log (harmonicExtension x) / x)
      (Set.Ici 4)

/-- **Monotonicity of $e^{H_n} \log H_n / n$.** With $H_n = \sum_{i=1}^n 1/i$ the $n$-th harmonic
number and $\log$ the natural logarithm, the sequence $e^{H_n} \log H_n / n$ is non-decreasing
for $n \ge 1$: its value at $m$ is at most its value at $n$ whenever $1 \le m \le n$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Corollary 3
(`integers-2026-A86-cor-3`). -/
public theorem_wanted exp_harmonic_mul_log_div_monotoneOn :
    MonotoneOn (fun n : ℕ => exp (harmonic n : ℝ) * log (harmonic n : ℝ) / n) (Set.Ici 1)

/-- **A least counterexample to the Kaneko–Lagarias inequality is superabundant.** Let
$\sigma(n)$ be the sum of the divisors of $n$, $H_n = 1 + \frac{1}{2} + \cdots + \frac{1}{n}$ the
$n$-th harmonic number and $\log$ the natural logarithm. Let $n_0 > 60$ be a natural number for
which the Kaneko–Lagarias inequality $\sigma(n_0) < e^{H_{n_0}} \log H_{n_0}$ fails, while
$\sigma(n) < e^{H_n} \log H_n$ holds for every natural number $n$ with $60 < n < n_0$. Then $n_0$
is superabundant: $\sigma(m)/m < \sigma(n_0)/n_0$ for every natural number $m$ with $1 \le m < n_0$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 9 (`integers-2026-A86-thm-9`).
-/
public theorem_wanted least_kaneko_lagarias_counterexample_superabundant (n₀ : ℕ) (hn₀ : 60 < n₀)
    (hfail : ¬ (ArithmeticFunction.sigma 1 n₀ : ℝ) <
      exp (harmonic n₀ : ℝ) * log (harmonic n₀ : ℝ))
    (hleast : ∀ n : ℕ, 60 < n → n < n₀ →
      (ArithmeticFunction.sigma 1 n : ℝ) < exp (harmonic n : ℝ) * log (harmonic n : ℝ)) :
    ∀ m : ℕ, 1 ≤ m → m < n₀ →
      (ArithmeticFunction.sigma 1 m : ℝ) / m < (ArithmeticFunction.sigma 1 n₀ : ℝ) / n₀

/-- **Robin's inequality implies the Kaneko–Lagarias inequality.** Let $\sigma(n)$ be the sum of
the divisors of $n$, $\gamma$ the Euler–Mascheroni constant, $\log$ the natural logarithm and
$H_n = 1 + \frac{1}{2} + \cdots + \frac{1}{n}$ the $n$-th harmonic number. For every natural
number $n$, if Robin's inequality $\sigma(n) < e^{\gamma} n \log \log n$ holds, then so does the
Kaneko–Lagarias inequality $\sigma(n) < e^{H_n} \log H_n$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 10
(`integers-2026-A86-thm-10`). -/
public theorem_wanted kaneko_lagarias_of_robin (n : ℕ)
    (h : (ArithmeticFunction.sigma 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n)) :
    (ArithmeticFunction.sigma 1 n : ℝ) < exp (harmonic n : ℝ) * log (harmonic n : ℝ)


/-- **Mertens-type bound for a product over the first primes with one prime omitted.** Let
$p_\ell$ be the $\ell$-th prime ($p_1 = 2$), $\log$ the natural logarithm and $B \approx 0.2615$
the Meissel–Mertens constant. For all natural numbers $k$ and $j$ with $1 \le j \le k + 1$,

$$\prod_{1 \le \ell \le k+1,\ \ell \ne j} \frac{p_\ell + 1}{p_\ell} \le
\log(p_{k+1}) \exp\Bigl(B - \frac{1}{p_j} + \frac{5}{\log p_{k+1}}\Bigr).$$

In the source this constant is called $c_1$, cited there from Tenenbaum's Theorem 1.10.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 2
(`integers-2026-A86-lem-2`). -/
public theorem_wanted prod_succ_div_prime_le (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k + 1) :
    ∏ ℓ ∈ (Finset.Icc 1 (k + 1)).erase j,
        ((Nat.nth Nat.Prime (ℓ - 1) : ℝ) + 1) / Nat.nth Nat.Prime (ℓ - 1) ≤
      log (Nat.nth Nat.Prime k) *
        exp (meisselMertensConstant - 1 / (Nat.nth Nat.Prime (j - 1) : ℝ) +
          5 / log (Nat.nth Nat.Prime k))

/-- **Explicit bound for a product over the first primes with one prime omitted.** Let $p_\ell$ be
the $\ell$-th prime ($p_1 = 2$), $\log$ the natural logarithm and $B$ the Meissel–Mertens constant.
For natural numbers $k \ge 6$ and $j$ with $1 \le j \le k + 1$, put
$U = (k+1)(\log(k+1) + \log \log(k+1))$ and $L = (k+1)(\log(k+1) + \log \log(k+1) - 1)$. Then

$$\prod_{1 \le \ell \le k+1,\ \ell \ne j} \frac{p_\ell + 1}{p_\ell} <
\log U \cdot \exp\Bigl(B - \frac{1}{p_j} + \frac{5}{\log L}\Bigr).$$

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 3
(`integers-2026-A86-lem-3`). -/
public theorem_wanted prod_succ_div_prime_lt_bound (k j : ℕ) (hk : 6 ≤ k) (hj : 1 ≤ j)
    (hjk : j ≤ k + 1) :
    ∏ ℓ ∈ (Finset.Icc 1 (k + 1)).erase j,
        ((Nat.nth Nat.Prime (ℓ - 1) : ℝ) + 1) / Nat.nth Nat.Prime (ℓ - 1) <
      log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)))) *
        exp (meisselMertensConstant - 1 / (Nat.nth Nat.Prime (j - 1) : ℝ) +
          5 / log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1)))

/-- **Eventual bound for $C(k)B(k)$ by an explicit logarithm.** Let $p_\ell$ denote the $\ell$-th
prime ($p_1 = 2$), $\log$ the natural logarithm, $\gamma$ the Euler–Mascheroni constant and $c_1$
the Meissel–Mertens constant. For $j \in \{1, 2, 3\}$ and $k \in \mathbb{N}$ put
$L(k) = (k+1)(\log(k+1) + \log\log(k+1))$, $L^-(k) = (k+1)(\log(k+1) + \log\log(k+1) - 1)$ and
$$C(k) = \log L(k) \cdot \exp\Bigl(c_1 - \frac{1}{p_j} + \frac{5}{\log L^-(k)}\Bigr),
\qquad B(k) = \prod_{\substack{1 \le \ell \le k+1 \\ \ell \ne j}} \frac{p_\ell^2}{p_\ell^2 - 1}.$$
Then there is $K \in \mathbb{N}$ such that for every $k \ge K$,
$$C(k)\,B(k) < e^{\gamma} \log\bigl(L^-(k) \log 2.51 - \log p_j\bigr).$$

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Proposition 1
(`integers-2026-A86-prop-1`). -/
public theorem_wanted exists_bound_mul_prod_sq_lt_exp_eulerMascheroni_mul (j : ℕ) (hj : 1 ≤ j)
    (hj3 : j ≤ 3) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)))) *
          exp (meisselMertensConstant - 1 / (Nat.nth Nat.Prime (j - 1) : ℝ) +
            5 / log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1))) *
          ∏ ℓ ∈ (Finset.Icc 1 (k + 1)).erase j,
            (Nat.nth Nat.Prime (ℓ - 1) : ℝ) ^ 2 / ((Nat.nth Nat.Prime (ℓ - 1) : ℝ) ^ 2 - 1) <
        exp eulerMascheroniConstant *
          log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1) * log (251 / 100) -
            log (Nat.nth Nat.Prime (j - 1)))

/-- **Eventual bound for $C(k)B(k)$ by $e^\gamma \log\log$ of a primorial quotient.** Let $p_\ell$
denote the $\ell$-th prime ($p_1 = 2$), $\log$ the natural logarithm, $\gamma$ the
Euler–Mascheroni constant, $c_1$ the Meissel–Mertens constant and $p\#$ the product of all primes
at most $p$. For $j \in \{1, 2, 3\}$ and $k \in \mathbb{N}$ put
$L(k) = (k+1)(\log(k+1) + \log\log(k+1))$, $L^-(k) = (k+1)(\log(k+1) + \log\log(k+1) - 1)$ and
$$C(k) = \log L(k) \cdot \exp\Bigl(c_1 - \frac{1}{p_j} + \frac{5}{\log L^-(k)}\Bigr),
\qquad B(k) = \prod_{\substack{1 \le \ell \le k+1 \\ \ell \ne j}} \frac{p_\ell^2}{p_\ell^2 - 1}.$$
Then there is $K \in \mathbb{N}$ such that for every $k \ge K$,
$$C(k)\,B(k) < e^{\gamma} \log\log\frac{p_{k+1}\#}{p_j}.$$

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 2
(`integers-2026-A86-thm-2`). -/
public theorem_wanted exists_bound_mul_prod_sq_lt_exp_eulerMascheroni_mul_log_log (j : ℕ)
    (hj : 1 ≤ j) (hj3 : j ≤ 3) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)))) *
          exp (meisselMertensConstant - 1 / (Nat.nth Nat.Prime (j - 1) : ℝ) +
            5 / log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1))) *
          ∏ ℓ ∈ (Finset.Icc 1 (k + 1)).erase j,
            (Nat.nth Nat.Prime (ℓ - 1) : ℝ) ^ 2 / ((Nat.nth Nat.Prime (ℓ - 1) : ℝ) ^ 2 - 1) <
        exp eulerMascheroniConstant *
          log (log ((primorial (Nat.nth Nat.Prime k) : ℝ) / Nat.nth Nat.Prime (j - 1)))

/-- **The factor $\hat C(k)$ is below $1.525$.** Let $\log$ be the natural logarithm. For every
natural number $k \ge 13042$, with $L^-(k) = (k+1)(\log(k+1) + \log\log(k+1) - 1)$,
$$\hat C(k) = \exp\Bigl(\frac{5}{\log L^-(k)}\Bigr) < 1.525.$$

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 5
(`integers-2026-A86-lem-5`). -/
public theorem_wanted exp_five_div_log_bound_lt (k : ℕ) (hk : 13042 ≤ k) :
    exp (5 / log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1))) < 1.525


/-- **Bounds for $\sigma(n)/n$ over primes avoiding $p_j$.** For $\ell \ge 1$ let $p_\ell$ be the
$\ell$-th prime, so that $p_1 = 2$. Let $1 \le j \le k$, let $q_1 < \cdots < q_k$ be primes
different from $p_j$, let $\alpha_1, \dots, \alpha_k \ge 1$, and put
$n = \prod_{i=1}^k q_i^{\alpha_i}$. Let $\sigma(n)$ be the sum of the divisors of $n$ and let
$\varphi$ be Euler's totient function. Then
$$
\frac{\sigma(n)}{n} < \prod_{i=1}^k \frac{q_i}{q_i - 1} = \frac{n}{\varphi(n)} \le
\prod_{1 \le \ell \le k + 1,\ \ell \ne j} \frac{p_\ell}{p_\ell - 1}.
$$

The paper prints the last inequality as strict; it is an equality when the $q_i$ are exactly the
first $k$ primes other than $p_j$ (for example $j = k = 1$ and $n = 3$, where both sides are
$3/2$), and the proof ($p_i \le q_i$) gives $\le$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 1
(`integers-2026-A86-lem-1`). -/
public theorem_wanted sigma_div_lt_totient_ratio_le_prod_primes (k j : ℕ) (hj : 1 ≤ j)
    (hjk : j ≤ k) (q α : Fin k → ℕ) (hq : StrictMono q) (hqp : ∀ i, (q i).Prime)
    (hqj : ∀ i, q i ≠ Nat.nth Nat.Prime (j - 1)) (hα : ∀ i, 1 ≤ α i) :
    let n := ∏ i, q i ^ α i
    (ArithmeticFunction.sigma 1 n : ℝ) / n < ∏ i, (q i : ℝ) / (q i - 1) ∧
      ∏ i, (q i : ℝ) / (q i - 1) = (n : ℝ) / Nat.totient n ∧
      (n : ℝ) / Nat.totient n ≤
        ∏ ℓ ∈ (Finset.Icc 1 (k + 1)).erase j,
          (Nat.nth Nat.Prime (ℓ - 1) : ℝ) / (Nat.nth Nat.Prime (ℓ - 1) - 1)

end

end MetaMathlibExt
